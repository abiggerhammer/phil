{-# LANGUAGE OverloadedStrings #-}

-- DATA-05C: validate the production *source-owned* bounded adapter, not a
-- caller-provided SurfaceEnvironment or an independently invented type plan.
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
  ( Control (..), Mode (..), Name (..), ProductElementType (..)
  , RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine (ProductEliminationRun (..))
import Phil.Surface.Check.Types (SurfaceCheckResult (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..), parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceNestedProductElimination
  ( GrammarV1NestedProductError (..), GrammarV1NestedProductTrace (..)
  , grammarV1CheckedNestedProductElimination )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.data05c.unpack"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

innerElems :: [ProductElementType]
innerElems =
  [ ProductElementType Linear bytes8
  , ProductElementType Unrestricted TyUnit ]

innerTy :: Ty
innerTy = TyProduct innerElems

rightElems, leftElems :: [ProductElementType]
rightElems =
  [ ProductElementType Unrestricted TyBool
  , ProductElementType Linear innerTy ]
leftElems =
  [ ProductElementType Linear innerTy
  , ProductElementType Unrestricted TyBool ]

fixturePath :: String -> FilePath
fixturePath key = "test/fixtures/fsem01-data05a-nested-product-v1/"
  ++ key ++ ".phil"

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "data05c-original-source" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("source declaration is not a function: " ++ show other)
    other -> Left ("source declaration count mismatch: " ++ show (length other))

check :: Bool -> String -> Either String ()
check valid message = if valid then Right () else Left message

run :: DeclarationKey -> Text
  -> Either String (Maybe (Either GrammarV1NestedProductError
       GrammarV1NestedProductTrace))
run declarationKey source = do
  fn <- parseOne source
  pure (grammarV1CheckedNestedProductElimination
    emptyStaticContext declarationKey fn)

accepted :: DeclarationKey -> Text -> Either String GrammarV1NestedProductTrace
accepted declarationKey source = do
  observed <- run declarationKey source
  case observed of
    Just (Right trace) -> Right trace
    other -> Left ("original source was not accepted by source-owned adapter: "
      ++ show other)

-- The test does not feed these contexts into the production adapter.
-- It replays native Core operations from returned source binder identities
-- and *independently* checks their results against real Surface cut states.
checkNative :: Bool -> GrammarV1NestedProductTrace -> Either String ()
checkNative right trace = do
  let packet = grammarV1ResolvedBinderCoreName
        (nestedProductOriginalOwner trace)
      names = map grammarV1ResolvedBinderCoreName
        (nestedProductOriginalLeaves trace)
      mid = nestedProductInternalOwner trace
      (flag,payload,spare) = case (right,names) of
        (True,[a,b,c]) -> (a,b,c)
        (False,[a,b,c]) -> (c,a,b)
        _ -> error "accepted nested source has wrong lexical binder count"
      outer = if right then rightElems else leftElems
      firstRestored = if right then [flag,mid] else [mid,flag]
      firstExpected = Core.ResourceContext Map.empty Map.empty
        (Map.singleton packet (TyProduct outer)) Set.empty
      secondExpected = Core.ResourceContext
        (Map.singleton flag TyBool) Map.empty
        (Map.singleton mid innerTy) Set.empty
      thirdExpected = Core.ResourceContext
        (Map.fromList [(flag,TyBool),(spare,TyUnit)]) Map.empty
        (Map.singleton payload bytes8) Set.empty
      firstCut = nestedProductFirstCut trace
      secondCut = nestedProductSecondCut trace
      terminalExpected = thirdExpected { Core.linearBindings = Map.empty }
  check (Set.size (Set.fromList [packet,flag,payload,spare,mid]) == 5 &&
         nestedProductDeclarationKey trace == root &&
         nestedProductOuterContract trace == outer &&
         nestedProductInnerContract trace == innerElems &&
         nestedProductDeclaredReturn trace == CheckedTypeMode bytes8 Linear)
    "returned source certificate has invalid exact identity, type, or mode"
  first <- either (Left . show) Right $
    Core.insertBinding Linear packet (TyProduct outer) Core.emptyContext
  second <- either (Left . show) Right $
    ProductMode.eliminateProductBinding packet firstRestored first
  third <- either (Left . show) Right $
    ProductMode.eliminateProductBinding mid [payload,spare] second
  check (first == firstExpected &&
         second == secondExpected &&
         third == thirdExpected)
    "independent real Core native two-step context disagrees"
  check (productEliminationBefore firstCut == Just first &&
         productEliminationAfter firstCut == Just second &&
         productEliminationBefore secondCut == Just second &&
         productEliminationAfter secondCut == Just third)
    "source-owned production Surface checkpoints disagree with native Core"
  check (nestedProductAccepted trace ==
         SurfaceCheckResult "unpack" [Return bytes8])
    "production full Surface component did not return exact checked Bytes"
  check (Core.useBinding packet third == Left (Core.UnknownBinding packet) &&
         Core.useBinding mid third == Left (Core.UnknownBinding mid))
    "native test found resurrected packet or synthetic intermediate"
  (result,after) <- either (Left . show) Right
    (Core.consumeLinear payload third)
  check (result == bytes8 && after == terminalExpected &&
         Core.ensureComplete after == Right () &&
         Core.consumeLinear payload after == Left (Core.UnknownBinding payload))
    "successful source-owned projection failed one-shot Linear completion"

checkAccepted :: String -> Bool -> IO (Either String ())
checkAccepted key right = do
  source <- TextIO.readFile (fixturePath key)
  pure $ do
    trace <- accepted root source
    checkNative right trace

checkMismatch :: String -> String -> IO (Either String ())
checkMismatch key diagnostic = do
  source <- TextIO.readFile (fixturePath key)
  pure $ do
    outcome <- run root source
    case outcome of
      Just (Left (NestedProductSourceMismatch detail)) ->
        check (Text.isInfixOf (Text.pack diagnostic) detail)
          ("wrong exact nested-source mismatch: " ++ show detail)
      other -> Left ("source rejection had wrong class: " ++ key ++ " " ++ show other)

checkBinderError :: String -> IO (Either String ())
checkBinderError key = do
  source <- TextIO.readFile (fixturePath key)
  pure $ do
    outcome <- run root source
    case outcome of
      Just (Left (NestedProductLetError _)) -> Right ()
      other -> Left ("source active-shadow/duplicate binder admitted: " ++ show other)

checkNoncompetence :: String -> IO (Either String ())
checkNoncompetence key = do
  source <- TextIO.readFile (fixturePath key)
  pure $ do
    outcome <- run root source
    check (outcome == Nothing)
      ("unsupported nested form treated as normative source-invalidity or admitted: "
        ++ key ++ " " ++ show outcome)

checkAlphaAndRoot :: IO (Either String ())
checkAlphaAndRoot = do
  source <- TextIO.readFile (fixturePath "accepted-right")
  let renamed = foldl (\text' (old,new) -> Text.replace old new text')
        source
        [("packet","envelope"),("flag","condition"),
         ("payload","owned"),("spare","unused")]
  pure $ do
    orig <- accepted root source
    alpha <- accepted root renamed
    check (nestedProductOriginalOwner orig ==
             nestedProductOriginalOwner alpha ||
           grammarV1ResolvedBinderKey (nestedProductOriginalOwner orig) ==
             grammarV1ResolvedBinderKey (nestedProductOriginalOwner alpha))
      "alpha-renaming changed declaration-rooted binder keys"
    check (map grammarV1ResolvedBinderCoreName
             (nestedProductOriginalLeaves orig) ==
           map grammarV1ResolvedBinderCoreName
             (nestedProductOriginalLeaves alpha) &&
           nestedProductInternalOwner orig == nestedProductInternalOwner alpha)
      "alpha-renaming changed leaf or fresh Core intermediate identities"
    changed <- accepted (DeclarationKey "decl.fsem01.data05c.other") source
    check (grammarV1ResolvedBinderCoreName (nestedProductOriginalOwner orig) /=
           grammarV1ResolvedBinderCoreName (nestedProductOriginalOwner changed) &&
           nestedProductInternalOwner orig /= nestedProductInternalOwner changed)
      "two distinct declaration roots aliased one Core resource owner"

main :: IO ()
main = do
  verified <- sequence
    [ checkAccepted "accepted-right" True
    , checkAccepted "accepted-left" False
    , checkBinderError "duplicate-leaf"
    , checkBinderError "shadow-packet"
    , checkMismatch "wrong-return-owner" "returned source occurrence"
    , checkMismatch "wrong-return-type" "nested source return"
    , checkMismatch "wrong-leaf-width" "nested product source element"
    , checkMismatch "wrong-leaf-shape" "nested product source element"
    , checkMismatch "wrong-pattern-side" "nested product source element"
    , checkNoncompetence "wide-inner-pattern"
    , checkNoncompetence "flat-pattern"
    , checkNoncompetence "unknown-return"
    , checkNoncompetence "extra-source-statement"
    , checkAlphaAndRoot
    ]
  case sequence verified of
    Left reason -> putStrLn ("FAIL DATA-05C: " ++ reason) >> exitFailure
    Right _ -> putStrLn
      "PASS DATA-05C: source-owned production nested adapter, 2 native/Surface executions, original 13 source controls, alpha stability, root separation"
