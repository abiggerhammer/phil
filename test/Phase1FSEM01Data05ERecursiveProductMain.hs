{-# LANGUAGE OverloadedStrings #-}

-- DATA-04/05E: genuine original Grammar-v1 finite product trees, never
-- caller-constructed SurfaceEnvironment or synthetic source binders.
module Main (main) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import qualified Phil.Core.DataMode as ProductMode
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Ty (..))
import Phil.Surface.Check.Engine (ProductEliminationRun (..))
import Phil.Surface.Check.Types (RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..), GrammarV1FunctionDecl
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceRecursiveProductElimination
  ( RecursiveProductError (..), RecursiveProductStep (..)
  , RecursiveProductTrace (..), grammarV1CheckedRecursiveProductElimination )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.data05e.unpack"

sourcePath :: String -> FilePath
sourcePath fixture =
  "test/fixtures/fsem01-data05e-recursive-product-v1/" ++ fixture ++ ".phil"

ensure :: Bool -> String -> Either String ()
ensure condition errorMessage =
  if condition then Right () else Left errorMessage

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "data05e-original-source" source)
  case grammarV1TopLevelDecls file of
    [Located _ item] ->
      case locatedValue (grammarV1Declaration item) of
        GrammarV1FunctionDeclaration fn -> Right fn
        other -> Left ("source declaration is not a function: " ++ show other)
    others -> Left ("source declaration count differs: " ++ show (length others))

observe :: DeclarationKey -> Text
  -> Either String (Maybe (Either RecursiveProductError RecursiveProductTrace))
observe key text' = do
  source <- parseOne text'
  Right (grammarV1CheckedRecursiveProductElimination
    emptyStaticContext key source)

accepted :: DeclarationKey -> Text -> Either String RecursiveProductTrace
accepted key source = do
  outcome <- observe key source
  case outcome of
    Just (Right trace) -> Right trace
    other -> Left ("checked original source was not accepted: " ++ show other)

-- Execute the *independent* real Core operations, with zero reliance on the
-- source adapter's Haskell-computed expected context transition.
checkNative :: Int -> RecursiveProductTrace -> Either String ()
checkNative count trace = do
  let steps = recursiveProductSteps trace
      rootName = grammarV1ResolvedBinderCoreName
        (recursiveProductOriginalOwner trace)
      returnedName = grammarV1ResolvedBinderCoreName
        (recursiveProductReturnedOwner trace)
      returnedTy = checkedBindingType (recursiveProductDeclaredReturn trace)
      leafNames = map grammarV1ResolvedBinderCoreName
        (recursiveProductOriginalLeaves trace)
      internal = recursiveProductInternalOwners trace
  first <- case steps of
    step : _ -> Right step
    [] -> Left "no product steps for source product"
  ensure (length steps == count &&
          recursiveProductDeclarationKey trace == root &&
          checkedBindingMode (recursiveProductDeclaredReturn trace) == Linear &&
          Set.size (Set.fromList (rootName:leafNames ++ internal)) ==
            length (rootName:leafNames ++ internal) &&
          length internal == count - 1)
    "source product step count or global owner freshness differs"
  initial <- either (Left . show) Right $
    Core.insertBinding Linear rootName
      (TyProduct (recursiveStepContract first)) Core.emptyContext
  after <- foldM checkStage initial steps
  ensure (after == recursiveProductFinalContext trace)
    "independent Core terminal state differs from actual adapter"
  -- The only permitted Linear residue is the original checked Bytes leaf.
  ensure (Core.linearBindings after == Map.singleton returnedName returnedTy &&
          Set.null (Core.sharedLoans after) &&
          Map.null (Core.affineBindings after))
    "unexpected restricted owner, active loan or affine state at terminal"
  (consumed,terminal) <- either (Left . show) Right
    (Core.consumeLinear returnedName after)
  ensure (consumed == returnedTy &&
          Core.ensureComplete terminal == Right () &&
          Core.consumeLinear returnedName terminal ==
            Left (Core.UnknownBinding returnedName) &&
          recursiveProductAccepted trace ==
            SurfaceCheckResult "unpack" [Return returnedTy])
    "actual checker did not satisfy one-shot Linear return"

checkStage :: Core.ResourceContext -> RecursiveProductStep
  -> Either String Core.ResourceContext
checkStage before step = do
  let owner = recursiveStepSourceOwner step
      names = recursiveStepSuccessorNames step
      surface = recursiveStepSurface step
      wasLinear = Map.member owner (Core.linearBindings before)
      wasUnrestricted = Map.member owner (Core.unrestrictedBindings before)
  ensure (length names == 2 &&
          recursiveStepBefore step == before &&
          (wasLinear || wasUnrestricted))
    "source-derived product owner/arity/predecessor is wrong"
  after <- either (Left . show) Right
    (ProductMode.eliminateProductBinding owner names before)
  ensure (after == recursiveStepAfter step &&
          productEliminationBefore surface == Just before &&
          productEliminationAfter surface == Just after)
    "actual production Surface cut differs from independent Core"
  case productEliminationOutcome surface of
    Left err | surfaceErrorClass err == LinearCompletion -> Right ()
    other -> Left ("source prefix did not fail at exact LinearCompletion: " ++ show other)
  ensure (not wasLinear ||
          Map.notMember owner (Core.linearBindings after))
    "consumed Linear product owner was resurrected after elimination"
  ensure (not wasUnrestricted ||
          Map.member owner (Core.unrestrictedBindings after))
    "copyable unrestricted product was incorrectly consumed"
  Right after

checkAccepted :: String -> Int -> IO (Either String ())
checkAccepted fixture count = do
  input <- TextIO.readFile (sourcePath fixture)
  pure (accepted root input >>= checkNative count)

checkMismatch :: String -> String -> IO (Either String ())
checkMismatch fixture fragment = do
  input <- TextIO.readFile (sourcePath fixture)
  pure $ do
    outcome <- observe root input
    case outcome of
      Just (Left (RecursiveSourceMismatch details)) ->
        ensure (Text.isInfixOf (Text.pack fragment) details)
          ("wrong source mismatch: " ++ show details)
      other -> Left ("wrong negative class for " ++ fixture ++ ": " ++ show other)

checkBinder :: String -> IO (Either String ())
checkBinder fixture = do
  input <- TextIO.readFile (sourcePath fixture)
  pure $ do
    outcome <- observe root input
    case outcome of
      Just (Left (RecursiveLetError _)) -> Right ()
      other -> Left ("duplicate/active shadow not diagnosed by checker: " ++ show other)

checkNoncompetence :: String -> IO (Either String ())
checkNoncompetence fixture = do
  input <- TextIO.readFile (sourcePath fixture)
  pure $ do
    outcome <- observe root input
    ensure (outcome == Nothing)
      ("unsupported Grammar-v1 form falsely accepted/invalidated: " ++ show outcome)

checkAlpha :: IO (Either String ())
checkAlpha = do
  input <- TextIO.readFile (sourcePath "balanced")
  let renamed = foldl (\source (old,new) -> Text.replace old new source)
        input [("packet","envelope"),("flag","condition"),
               ("payload","owned"),("after","spare"),
               ("first","initial"),("last","final")]
  pure $ do
    original <- accepted root input
    alpha <- accepted root renamed
    ensure (map grammarV1ResolvedBinderCoreName
              (recursiveProductOriginalLeaves original) ==
            map grammarV1ResolvedBinderCoreName
              (recursiveProductOriginalLeaves alpha) &&
            recursiveProductInternalOwners original ==
              recursiveProductInternalOwners alpha &&
            map recursiveStepSourceOwner (recursiveProductSteps original) ==
              map recursiveStepSourceOwner (recursiveProductSteps alpha))
      "alpha-renaming changed source/recursive owner semantic identities"
    rootChanged <- accepted
      (DeclarationKey "decl.fsem01.data05e.another") input
    ensure (recursiveProductInternalOwners original /=
              recursiveProductInternalOwners rootChanged)
      "declaration-root change preserved forbidden internal Core identities"

main :: IO ()
main = do
  results <- sequence
    [ checkAccepted "flat-one" 1
    , checkAccepted "right-two" 2
    , checkAccepted "right-three" 3
    , checkAccepted "both-nested" 4
    , checkAccepted "balanced" 4
    , checkAccepted "left-three" 3
    , checkAccepted "six-deep" 6
    , checkMismatch "wrong-return" "source return is not"
    , checkMismatch "wrong-return-type" "return type/mode"
    , checkMismatch "wrong-width" "return type/mode"
    , checkMismatch "wrong-pattern-shape" "disagree in shape"
    , checkMismatch "two-linear" "exactly one checked Linear"
    , checkBinder "duplicate-leaf"
    , checkBinder "shadow-packet"
    , checkNoncompetence "flat-arity-three"
    , checkNoncompetence "named-alias"
    , checkNoncompetence "unknown-return"
    , checkNoncompetence "extra-statement"
    , checkAlpha
    ]
  case sequence results of
    Left message -> putStrLn ("FAIL DATA-05E: " ++ message) >> exitFailure
    Right _ -> putStrLn
      "PASS DATA-05E: arbitrary finite binary tree, 7 original-source executions and exact native/Core/Surface/semantic identity negative controls"
