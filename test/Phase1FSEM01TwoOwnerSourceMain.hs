{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: *single parsed Grammar-v1 function* with two linear Bytes owners.
-- Unlike the preceding synthetic Core-context bridge, every observed resource
-- checkpoint is emitted by the actual production Surface checker from the
-- exact two-parameter source. Tuple type agreement is bounded elementwise;
-- general source-to-Core product type elaboration remains unproved.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Static
  ( DeclarationKey (..), emptyStaticContext )
import Phil.Core.Syntax
  ( Control (..), Mode (..), Name, ProductElementType (..)
  , RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..)
  , checkSurfaceComponent )
import Phil.Surface.Check.Types
  ( InitialBinding (..), RejectionClass (BorrowEscape, TypeMismatch)
  , SurfaceCheckError (..), SurfaceCheckResult (..), SurfaceEnvironment (..)
  , emptySurfaceEnvironment )
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType, syntheticSpan)
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..), GrammarV1TopLevelDecl (..)
  , GrammarV1FunctionDecl (..), GrammarV1SourceFile (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.TwoOwnerBorrowResourceSurface
  ( GrammarV1TwoOwnerBorrowTrace (..)
  , grammarV1CheckedTwoOwnerBorrowFunction
  , grammarV1CheckedTwoOwnerBorrowFunctionTrace )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Statement (..)
  , SurfaceExpression (..) )
import System.Exit (exitFailure)

sourceDir :: FilePath
sourceDir = "test/fixtures/fsem01-two-owner-source-v1/"

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.source-two-owner.v1"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

productType :: Ty
productType = TyProduct
  [ ProductElementType Linear bytes8
  , ProductElementType Linear bytes8
  ]

assert :: Bool -> String -> Either String ()
assert condition why =
  if condition then Right () else Left why

sourceFunction :: Text -> Either String GrammarV1FunctionDecl
sourceFunction source = do
  sourceFile <- either (Left . show) Right
    (parseGrammarV1StructuralSource "two-owner-source-v1" source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] ->
      case locatedValue (grammarV1Declaration top) of
        GrammarV1FunctionDeclaration fn -> Right fn
        _ -> Left "expected exactly one parsed function"
    _ -> Left "expected exactly one source declaration"

checkSource :: Text -> Either String GrammarV1TwoOwnerBorrowTrace
checkSource source = do
  fn <- sourceFunction source
  trace <- case grammarV1CheckedTwoOwnerBorrowFunctionTrace
    emptyStaticContext root fn of
    Just (Right result) -> Right result
    other -> Left ("two-owner traced source not admitted: " <> show other)
  assert
    (grammarV1CheckedTwoOwnerBorrowFunction emptyStaticContext root fn ==
      Just (twoOwnerOutcome trace))
    "ordinary checker and traced production outcome differ"
  Right trace

contextOf :: BorrowTraceCheckpoint -> Core.ResourceContext
contextOf cut = Core.ResourceContext
  { Core.unrestrictedBindings = traceUnrestrictedOwners cut
  , Core.affineBindings = traceAffineOwners cut
  , Core.linearBindings = traceLinearOwners cut
  , Core.sharedLoans = traceActiveLoans cut
  }

checkResourceDomains
  :: Name -> Name -> [BorrowTraceCheckpoint] -> Either String ()
checkResourceDomains primary spectator cuts = do
  assert (primary /= spectator) "two source binders have identical Core identity"
  assert (not (null cuts)) "production emitted no source checkpoints"
  mapM_ check (zip [0 :: Int ..] cuts)
  where
    check (index, cut) = do
      let ctx = contextOf cut
          linear = Core.linearBindings ctx
          loans = Core.sharedLoans ctx
          expected = if tracePhase cut == TraceOwnerReturned
            then Map.empty else Map.fromList
              [(primary, bytes8), (spectator, bytes8)]
          expectedLoans = case tracePhase cut of
            TraceLoanStarted -> Set.singleton primary
            TraceBodyResult _ -> Set.singleton primary
            TraceEscapeRejected -> Set.singleton primary
            _ -> Set.empty
      assert (traceOwnerName cut == primary)
        ("checkpoint owner mismatch at " <> show index)
      assert (Map.null (Core.unrestrictedBindings ctx) &&
              Map.null (Core.affineBindings ctx))
        ("nonlinear bindings at recorded post-prune checkpoint " <> show index)
      assert (linear == expected)
        ("missing/extra/wrong-type source linear binding " <> show index)
      assert (loans == expectedLoans)
        ("missing or foreign source loan " <> show index)

checkIndependentSpectator
  :: Name -> Name -> Core.ResourceContext -> Either String ()
checkIndependentSpectator primary spectator ctx = do
  assert (Core.consumeLinear primary ctx ==
    Left (Core.OwnerBorrowed primary))
    "borrowed primary was allowed to move"
  (ty, afterSpectator) <- either (Left . show) Right
    (Core.consumeLinear spectator ctx)
  assert (ty == bytes8) "spectator wrong type when independently consumed"
  assert (Core.linearBindings afterSpectator ==
            Map.singleton primary bytes8)
    "spectator use damaged primary binding"
  assert (Core.sharedLoans afterSpectator == Set.singleton primary)
    "spectator use damaged primary active loan"

-- Check the declared source tuple without importing the bridge's inferred
-- result. This independently establishes exact element order, mode and Ty.
checkDeclaredProduct :: Text -> Either String ()
checkDeclaredProduct source = do
  fn <- sourceFunction source
  resultSource <- maybe (Left "missing source result type") Right
    (grammarV1FunctionResultType fn)
  case grammarV1CheckedTypeMode
    emptyStaticContext emptySurfaceState (locatedValue resultSource) of
    Just (Right (result, steps)) ->
      assert (checkedBindingType result == productType &&
              checkedBindingMode result == Linear &&
              null steps)
        "two-Bytes source tuple did not elaborate to the exact linear TyProduct"
    other -> Left ("source product type was not accepted: " <> show other)

checkAccepted :: Text -> Either String ()
checkAccepted source = do
  checkDeclaredProduct source
  traced <- checkSource source
  let primary = grammarV1ResolvedBinderCoreName (twoOwnerPrimaryBinder traced)
      spectator = grammarV1ResolvedBinderCoreName (twoOwnerSpectatorBinder traced)
      cuts = twoOwnerCheckpoints traced
      actualPhases = map tracePhase cuts
  assert (twoOwnerExpectedProduct traced == productType)
    "traced checker lost the exact source-derived TyProduct"
  assert (twoOwnerOutcome traced ==
    Right (SurfaceCheckResult "loan" [Return productType]))
    "production did not return the elementwise-checked TyProduct"
  assert
    (actualPhases ==
      [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False
      , TraceLoanClosed, TraceOwnerReturned ])
    "successful two-owner source phases do not match the production trace"
  checkResourceDomains primary spectator cuts
  case map contextOf cuts of
    [before, started, body, closed, returned] -> do
      assert (Core.startSharedLoan primary before == Right started)
        "actual two-owner source loan start disagrees with Core"
      assert (started == body)
        "actual scope-exit checkpoint corrupted other owner"
      assert (Core.endSharedLoan primary body == Right closed)
        "actual two-owner source loan end disagrees with Core"
      (primaryTy, afterPrimary) <- either (Left . show) Right
        (Core.consumeLinear primary closed)
      assert (primaryTy == bytes8 &&
              Core.linearBindings afterPrimary == Map.singleton spectator bytes8)
        "primary consumption did not frame exact spectator"
      assert (Core.consumeLinear spectator afterPrimary ==
        Right (bytes8, returned))
        "source tuple did not consume both owners exactly"
      assert (Core.ensureComplete returned == Right ())
        "successful two-owner return had residual obligations"
      checkIndependentSpectator primary spectator started
    _ -> Left "unexpected accepted source trace length"

checkEscaping :: Text -> Either String ()
checkEscaping source = do
  traced <- checkSource source
  let primary = grammarV1ResolvedBinderCoreName (twoOwnerPrimaryBinder traced)
      spectator = grammarV1ResolvedBinderCoreName (twoOwnerSpectatorBinder traced)
      cuts = twoOwnerCheckpoints traced
  case twoOwnerOutcome traced of
    Left (GrammarV1BorrowResourceProductionError err) -> do
      assert (surfaceErrorClass err == BorrowEscape &&
              surfaceErrorDetail err ==
                "shared view escapes its lexical scope")
        "negative source rejected for a different cause"
    other -> Left ("expected exact BorrowEscape; got " <> show other)
  assert (map tracePhase cuts ==
    [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult True
    , TraceEscapeRejected ])
    "escaped source emitted closure/consumption after rejection"
  checkResourceDomains primary spectator cuts
  case map contextOf cuts of
    [before, started, escaped, rejected] -> do
      assert (Core.startSharedLoan primary before == Right started)
        "negative source prefix is not a real Core start-loan transition"
      assert (started == escaped && escaped == rejected)
        "escaping source fabricated a post-error successor"
      assert (Core.consumeLinear primary rejected ==
        Left (Core.OwnerBorrowed primary))
        "rejected source allowed borrowed owner consumption"
      assert (Core.linearBindings rejected ==
        Map.fromList [(primary, bytes8), (spectator, bytes8)])
        "rejected source lost either live owner"
      checkIndependentSpectator primary spectator rejected
    _ -> Left "unexpected escaped source trace length"

-- Check the production return boundary independently of the source adapter.
-- A forged product contract cannot make an unrelated runtime tuple type-check,
-- and the legacy (unconfigured) tuple carrier remains exactly opaque.
checkProductionProductContract :: Either String ()
checkProductionProductContract = do
  let one = "raw-owner"
      two = "other-owner"
      named text = Located syntheticSpan (VariableExpression text)
      tuple = Located syntheticSpan
        (TupleExpression [named one, named two])
      component = Located syntheticSpan (Component
        { componentName = "direct-product-test"
        , componentParameters = []
        , componentProvides = Nothing
        , componentBody = Located syntheticSpan (Block
            [Located syntheticSpan (ReturnStatement tuple)])
        })
      base = (emptySurfaceEnvironment emptyStaticContext)
        { surfaceInitialBindings = Map.fromList
            [ (one, InitialBinding Linear bytes8 (shapeForType bytes8))
            , (two, InitialBinding Linear bytes8 (shapeForType bytes8)) ]
        }
      withProduct elements =
        base { surfaceExpectedProductReturn = Just elements }
      exact = [ProductElementType Linear bytes8, ProductElementType Linear bytes8]
      wrongWidth =
        [ProductElementType Linear bytes8,
         ProductElementType Linear (TyBytes (RefNat 9))]
      wrongMode =
        [ProductElementType Linear bytes8,
         ProductElementType Unrestricted bytes8]
      wrongArity = [ProductElementType Linear bytes8]
      expectedNormal = SurfaceCheckResult "direct-product-test"
        [Return productType]
      expectedLegacy = SurfaceCheckResult "direct-product-test"
        [Return (TyOpaque "Tuple[2]")]
      rejects expected =
        case checkSurfaceComponent (withProduct expected) component of
          Left err -> assert (surfaceErrorClass err == TypeMismatch &&
              surfaceErrorDetail err ==
                "returned tuple elements do not match the checked product contract")
              "forged product expected an exact product-type mismatch"
          Right value -> Left ("forged product unexpectedly passed: " <> show value)
  assert (checkSurfaceComponent (withProduct exact) component ==
    Right expectedNormal)
    "production returned the wrong actual TyProduct for a checked tuple"
  assert (checkSurfaceComponent base component == Right expectedLegacy)
    "product opt-in changed the legacy opaque tuple return"
  rejects wrongWidth
  rejects wrongMode
  rejects wrongArity

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source label = do
  fn <- sourceFunction source
  assert
    (grammarV1CheckedTwoOwnerBorrowFunctionTrace
      emptyStaticContext root fn == Nothing)
    ("unexpected acceptance of outside-fragment source: " <> label)
  assert
    (grammarV1CheckedTwoOwnerBorrowFunction
      emptyStaticContext root fn == Nothing)
    ("ordinary route accepted outside-fragment source: " <> label)

main :: IO ()
main = do
  positive <- TextIO.readFile (sourceDir <> "accepted.phil")
  escaping <- TextIO.readFile (sourceDir <> "escape.phil")
  reversed <- TextIO.readFile (sourceDir <> "reversed-return.phil")
  extra <- TextIO.readFile (sourceDir <> "third-owner.phil")
  wrongWidth <- TextIO.readFile (sourceDir <> "wrong-product-width.phil")
  unsupported <- TextIO.readFile (sourceDir <> "unsupported-product-element.phil")
  let result = do
        checkAccepted positive
        checkEscaping escaping
        checkProductionProductContract
        checkUnsupported reversed "reversed return order"
        checkUnsupported extra "third linear parameter"
        checkUnsupported wrongWidth "second product type has wrong Bytes width"
        checkUnsupported unsupported "non-Bytes product element"
        -- The accepted/escaping source differs only in one final Unit
        -- expression within the borrow body, not in binder/type signatures.
        assert (Text.replace "view; unit;" "view;" positive == escaping)
          "negative is not the minimally modified escaping-view source"
  case result of
    Right () ->
      putStrLn "PASS: single-source two-linear-owner exact TyProduct return and BorrowEscape"
    Left msg ->
      putStrLn ("FAIL: " <> msg) >> exitFailure
