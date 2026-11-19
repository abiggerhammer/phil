{-# LANGUAGE OverloadedStrings #-}

-- DATA-05D: original source three-level product through actual production
-- Surface cuts, independently replayed native Core eliminations.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import qualified Phil.Core.DataMode as ProductMode
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax
  ( Control (..), Mode (..), ProductElementType (..)
  , RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine (ProductEliminationRun (..))
import Phil.Surface.Check.Types (SurfaceCheckResult (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceNestedProductElimination
  ( GrammarV1NestedProductError (..), GrammarV1ThreeLevelProductTrace (..)
  , grammarV1CheckedThreeLevelProductElimination )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.data05d.unpack"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

deepElems :: [ProductElementType]
deepElems = [ProductElementType Linear bytes8, ProductElementType Unrestricted TyUnit]

middleElems :: [ProductElementType]
middleElems =
  [ ProductElementType Unrestricted TyUnit
  , ProductElementType Linear (TyProduct deepElems) ]

outerElems :: [ProductElementType]
outerElems =
  [ ProductElementType Unrestricted TyBool
  , ProductElementType Linear (TyProduct middleElems) ]

sourcePath :: String -> FilePath
sourcePath name = "test/fixtures/fsem01-data05d-three-level-v1/" ++ name ++ ".phil"

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne input = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "data05d-original-source" input)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] ->
      case locatedValue (grammarV1Declaration top) of
        GrammarV1FunctionDeclaration fn -> Right fn
        other -> Left ("not a source function: " ++ show other)
    other -> Left ("wrong top-level source count: " ++ show (length other))

observe :: DeclarationKey -> Text
  -> Either String (Maybe (Either GrammarV1NestedProductError
        GrammarV1ThreeLevelProductTrace))
observe key input = do
  fn <- parseOne input
  pure (grammarV1CheckedThreeLevelProductElimination emptyStaticContext key fn)

accepted :: DeclarationKey -> Text -> Either String GrammarV1ThreeLevelProductTrace
accepted key input = do
  result <- observe key input
  case result of
    Just (Right trace) -> Right trace
    other -> Left ("original source not admitted: " ++ show other)

ensure :: Bool -> String -> Either String ()
ensure ok message = if ok then Right () else Left message

checkNative :: GrammarV1ThreeLevelProductTrace -> Either String ()
checkNative trace = do
  let packet = grammarV1ResolvedBinderCoreName (threeLevelOriginalOwner trace)
      owners = map grammarV1ResolvedBinderCoreName (threeLevelOriginalLeaves trace)
  (flag,before,payload,after) <- case owners of
    [f,b,p,a] -> Right (f,b,p,a)
    _ -> Left "source returned incorrect four-leaf scope"
  let middle = threeLevelMiddleOwner trace
      deep = threeLevelDeepOwner trace
      context0 = Core.ResourceContext Map.empty Map.empty
        (Map.singleton packet (TyProduct outerElems)) Set.empty
      context1 = Core.ResourceContext (Map.singleton flag TyBool) Map.empty
        (Map.singleton middle (TyProduct middleElems)) Set.empty
      context2 = Core.ResourceContext
        (Map.fromList [(flag,TyBool),(before,TyUnit)]) Map.empty
        (Map.singleton deep (TyProduct deepElems)) Set.empty
      context3 = Core.ResourceContext
        (Map.fromList [(flag,TyBool),(before,TyUnit),(after,TyUnit)]) Map.empty
        (Map.singleton payload bytes8) Set.empty
      cuts = [threeLevelFirstCut trace,threeLevelSecondCut trace,threeLevelThirdCut trace]
      contexts = [context0,context1,context2,context3]
  ensure (Set.size (Set.fromList [packet,flag,before,payload,after,middle,deep]) == 7 &&
          threeLevelDeclarationKey trace == root &&
          threeLevelOuterContract trace == outerElems &&
          threeLevelMiddleContract trace == middleElems &&
          threeLevelDeepContract trace == deepElems &&
          threeLevelDeclaredReturn trace == CheckedTypeMode bytes8 Linear)
    "source-owned identity, product contract or return type differs"
  c0 <- either (Left . show) Right $
    Core.insertBinding Linear packet (TyProduct outerElems) Core.emptyContext
  c1 <- either (Left . show) Right $
    ProductMode.eliminateProductBinding packet [flag,middle] c0
  c2 <- either (Left . show) Right $
    ProductMode.eliminateProductBinding middle [before,deep] c1
  c3 <- either (Left . show) Right $
    ProductMode.eliminateProductBinding deep [payload,after] c2
  ensure ([c0,c1,c2,c3] == contexts)
    "independent native Core steps disagree with original source"
  ensure (map productEliminationBefore cuts == map Just (take 3 contexts) &&
          map productEliminationAfter cuts == map Just (tail contexts))
    "actual Surface trace cuts disagree with native Core operations"
  ensure (all (\name -> Core.useBinding name c3 == Left (Core.UnknownBinding name))
           [packet,middle,deep])
    "source packet or generated intermediate resurrected after move"
  (returned,terminal) <- either (Left . show) Right
    (Core.consumeLinear payload c3)
  ensure (returned == bytes8 &&
          Core.ensureComplete terminal == Right () &&
          Core.consumeLinear payload terminal == Left (Core.UnknownBinding payload) &&
          threeLevelAccepted trace == SurfaceCheckResult "unpack" [Return bytes8])
    "one-shot Linear return or production Surface success differed"

checkAccepted :: IO (Either String ())
checkAccepted = do
  source <- TextIO.readFile (sourcePath "accepted")
  pure (accepted root source >>= checkNative)

checkMismatch :: String -> String -> IO (Either String ())
checkMismatch fixture fragment = do
  source <- TextIO.readFile (sourcePath fixture)
  pure $ do
    result <- observe root source
    case result of
      Just (Left (NestedProductSourceMismatch actual)) ->
        ensure (Text.isInfixOf (Text.pack fragment) actual)
          ("source mismatch text differs: " ++ show actual)
      other -> Left ("unexpected rejection class for " ++ fixture ++ ": " ++ show other)

checkBinder :: String -> IO (Either String ())
checkBinder fixture = do
  source <- TextIO.readFile (sourcePath fixture)
  pure $ do
    result <- observe root source
    case result of
      Just (Left (NestedProductLetError _)) -> Right ()
      other -> Left ("duplicate/shadow error not preserved: " ++ show other)

checkNoncompetence :: String -> IO (Either String ())
checkNoncompetence fixture = do
  source <- TextIO.readFile (sourcePath fixture)
  pure $ do
    result <- observe root source
    ensure (result == Nothing)
      ("unsupported original source falsely admitted/invalidated: " ++ show result)

checkAlpha :: IO (Either String ())
checkAlpha = do
  source <- TextIO.readFile (sourcePath "accepted")
  let renamed = foldl (\s (a,b) -> Text.replace a b s) source
        [("packet","envelope"),("flag","condition"),("before","front"),
         ("payload","owned"),("after","back")]
  pure $ do
    orig <- accepted root source
    alpha <- accepted root renamed
    ensure (map grammarV1ResolvedBinderCoreName (threeLevelOriginalLeaves orig) ==
            map grammarV1ResolvedBinderCoreName (threeLevelOriginalLeaves alpha) &&
            threeLevelMiddleOwner orig == threeLevelMiddleOwner alpha &&
            threeLevelDeepOwner orig == threeLevelDeepOwner alpha)
      "alpha-renaming changed source owner or generated internal identities"
    changed <- accepted (DeclarationKey "decl.fsem01.data05d.other") source
    ensure (threeLevelMiddleOwner orig /= threeLevelMiddleOwner changed &&
            threeLevelDeepOwner orig /= threeLevelDeepOwner changed)
      "changing declaration key did not separate generated Core names"

main :: IO ()
main = do
  results <- sequence
    [ checkAccepted
    , checkMismatch "wrong-width" "three-level source product element"
    , checkMismatch "wrong-deep-leaf" "three-level source product element"
    , checkMismatch "wrong-return" "three-level returned source occurrence"
    , checkMismatch "wrong-return-type" "three-level declared return"
    , checkBinder "duplicate-leaf"
    , checkBinder "shadow-packet"
    , checkNoncompetence "flat-pattern"
    , checkNoncompetence "wide-inner-pattern"
    , checkNoncompetence "unknown-return"
    , checkNoncompetence "extra-statement"
    , checkAlpha
    ]
  case sequence results of
    Left reason -> putStrLn ("FAIL DATA-05D: " ++ reason) >> exitFailure
    Right _ -> putStrLn
      "PASS DATA-05D: real source-owned three-stage Surface/Core, exact negative and identity controls"
