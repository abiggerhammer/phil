{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: exact source-checked nominal Affine + intrinsic Linear product
-- returned through the real production Surface checker with precise traces.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..), GenericStaticKind (..) )
import Phil.Core.NominalDataMode
  ( NominalModeError (..), NominalRestrictionJustification (..) )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), emptyStaticContext )
import Phil.Core.Syntax
  ( Control (..), Mode (..), ProductElementType (..), RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..) )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedFlatProduct (..)
  , GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..)
  , GrammarV1CheckedTypeModeResolutionError (..)
  , GrammarV1ResolvedNamedTypeMode (..)
  , grammarV1CheckedFlatProductWithNamedResolutions
  , grammarV1CheckedTypeMode )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataModeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl, GrammarV1FunctionDecl (..)
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..), parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceAffineProduct
  ( GrammarV1AffineProductError (..), GrammarV1AffineProductTrace (..)
  , grammarV1CheckedAffineProductFunctionTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.nominal-product.Permit"

functionRoot :: DeclarationKey
functionRoot = DeclarationKey "decl.fsem01.nominal-product.use"

revision :: InterfaceRevision
revision = InterfaceRevision "iface.fsem01.nominal-product.v1"

lifecycle :: Maybe NominalRestrictionJustification
lifecycle = Just (AdmittedLifecycleObligation
  "external reviewed Permit lifecycle/release obligation")

permitTy :: Ty
permitTy = TyOpaque "Permit"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

contract :: [ProductElementType]
contract =
  [ ProductElementType Affine permitTy
  , ProductElementType Linear bytes8 ]

productTy :: Ty
productTy = TyProduct contract

sourceDir :: FilePath
sourceDir = "test/fixtures/fsem01-nominal-affine-product-v1/"

assert :: Bool -> String -> Either String ()
assert truth reason = if truth then Right () else Left reason

parsePair :: Text -> Either String (GrammarV1DataDecl, GrammarV1FunctionDecl)
parsePair source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "nominal-product-v1" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ dat, Located _ fn] ->
      case (locatedValue (grammarV1Declaration dat),
            locatedValue (grammarV1Declaration fn)) of
        (GrammarV1DataDeclaration a, GrammarV1FunctionDeclaration b) ->
          Right (a,b)
        _ -> Left "expected one nominal data and one source function"
    _ -> Left "expected exactly two declarations"

check :: Maybe NominalRestrictionJustification -> Text
  -> Maybe (Either GrammarV1AffineProductError GrammarV1AffineProductTrace)
check attestation source =
  case parsePair source of
    Left _ -> Nothing
    Right (dat, fn) ->
      grammarV1CheckedAffineProductFunctionTrace
        emptyStaticContext root revision attestation dat functionRoot fn

checked :: Text -> Either String GrammarV1AffineProductTrace
checked source = case check lifecycle source of
  Just (Right trace) -> Right trace
  other -> Left ("source nominal flat product not admitted: " ++ show other)

contextOf :: BorrowTraceCheckpoint -> Core.ResourceContext
contextOf cut = Core.ResourceContext
  { Core.unrestrictedBindings = traceUnrestrictedOwners cut
  , Core.affineBindings = traceAffineOwners cut
  , Core.linearBindings = traceLinearOwners cut
  , Core.sharedLoans = traceActiveLoans cut
  }

checkCommon :: GrammarV1AffineProductTrace -> Either String ()
checkCommon result = do
  let permit = grammarV1ResolvedBinderCoreName (affineProductPermitBinder result)
      payload = grammarV1ResolvedBinderCoreName (affineProductPayloadBinder result)
      view = grammarV1ResolvedBinderCoreName (affineProductViewBinder result)
      cuts = affineProductCheckpoints result
  assert (permit /= payload && permit /= view && payload /= view)
    "semantic binders from the same parsed function collided"
  assert (affineProductDeclarationKey result == root &&
          affineProductInterfaceRevision result == revision)
    "resolved declaration and interface lineage were lost"
  assert (affineProductPermitMode result == CheckedTypeMode permitTy Affine &&
          affineProductPayloadMode result == CheckedTypeMode bytes8 Linear)
    "nominal affine or intrinsic linear source mode was guessed"
  assert (affineProductPermitOrigin result ==
          GrammarV1NamedTypeModeOrigin
            (ReferencedGenericStaticActual "Permit") root revision)
    "source nominal parameter lost exact origin"
  assert (not (null cuts)) "production checker recorded no resource checkpoints"
  let first = head cuts
  assert (traceOwnerName first == permit && traceViewName first == view)
    "borrow checkpoint mismatches resolved source owner/view identity"
  assert (contextOf first == Core.ResourceContext
          Map.empty (Map.singleton permit permitTy)
          (Map.singleton payload bytes8) Set.empty)
    "initial production state not exact affine/linear owner context"
  assert (all (\cut ->
          traceUnrestrictedOwners cut == Map.empty &&
          traceOwnerName cut == permit) cuts)
    "unexpected unrestricted owner or changed borrow identity in checkpoints"

checkAccepted :: Text -> Either String ()
checkAccepted source = do
  result <- checked source
  checkCommon result
  let permit = grammarV1ResolvedBinderCoreName (affineProductPermitBinder result)
      payload = grammarV1ResolvedBinderCoreName (affineProductPayloadBinder result)
      cuts = affineProductCheckpoints result
      elems = affineProductReturnElements result
  assert (affineProductCheckedReturn result == CheckedTypeMode productTy Linear)
    "nominal affine member or aggregate linear product mode lost"
  assert (map checkedResolvedTypeMode elems ==
          [CheckedTypeMode permitTy Affine, CheckedTypeMode bytes8 Linear])
    "checked product changed element order, mode or type"
  assert (map checkedResolvedTypeModeOrigin elems ==
          [ GrammarV1NamedTypeModeOrigin
              (ReferencedGenericStaticActual "Permit") root revision
          , GrammarV1IntrinsicTypeModeOrigin ])
    "product element provenance was silently lost"
  assert (affineProductOutcome result ==
          Right (SurfaceCheckResult "use" [Return productTy]))
    ("production returned wrong exact TyProduct: " ++ show (affineProductOutcome result))
  assert (map tracePhase cuts ==
          [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False
          , TraceLoanClosed, TraceOwnerReturned ])
    "accepted product did not traverse exact loan and return checkpoints"
  case map contextOf cuts of
    [before, started, body, closed, terminal] -> do
      assert (Core.startSharedLoan permit before == Right started &&
              started == body &&
              Core.endSharedLoan permit body == Right closed)
        "native Core affine loan start/end did not match production"
      assert (Core.consumeAffine permit started ==
              Left (Core.OwnerBorrowed permit))
        "borrowed affine Permit was consumable"
      assert (Core.ensureComplete closed ==
              Left (Core.UnconsumedLinearResources
                (Map.singleton payload bytes8)))
        "live linear payload was incorrectly considered completed"
      (affineTy, afterAffine) <- either (Left . show) Right
        (Core.consumeAffine permit closed)
      (linearTy, afterLinear) <- either (Left . show) Right
        (Core.consumeLinear payload afterAffine)
      assert (affineTy == permitTy && linearTy == bytes8 &&
              afterLinear == terminal && terminal == Core.emptyContext &&
              Core.ensureComplete terminal == Right ())
        "exact production tuple return did not consume both owner modes"
      assert (Core.consumeAffine permit terminal ==
              Left (Core.UnknownBinding permit) &&
              Core.consumeLinear payload terminal ==
              Left (Core.UnknownBinding payload))
        "product return duplicated an already-consumed owner"
      -- Check independent linear move while the affine owner's shared loan
      -- is still active. No cross-mode observation may change.
      (independentTy, independent) <- either (Left . show) Right
        (Core.consumeLinear payload started)
      assert (independentTy == bytes8 &&
              Core.affineBindings independent == Core.affineBindings started &&
              Core.unrestrictedBindings independent == Core.unrestrictedBindings started &&
              Core.sharedLoans independent == Set.singleton permit)
        "linear spectator move changed affine borrowed owner or loan"
      closedIndependent <- either (Left . show) Right
        (Core.endSharedLoan permit independent)
      (_, finished) <- either (Left . show) Right
        (Core.consumeAffine permit closedIndependent)
      assert (finished == Core.emptyContext)
        "independent linear move changed affine owner restoration"
    _ -> Left "unexpected number of production product-return snapshots"

checkEscape :: Text -> Either String ()
checkEscape source = do
  result <- checked source
  checkCommon result
  let permit = grammarV1ResolvedBinderCoreName (affineProductPermitBinder result)
      payload = grammarV1ResolvedBinderCoreName (affineProductPayloadBinder result)
      cuts = affineProductCheckpoints result
  case affineProductOutcome result of
    Left err ->
      assert (surfaceErrorClass err == BorrowEscape &&
              surfaceErrorDetail err == "shared view escapes its lexical scope")
        ("borrow escape rejected for wrong reason: " ++ show err)
    other -> Left ("borrow escape was accepted: " ++ show other)
  assert (map tracePhase cuts ==
          [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult True
          , TraceEscapeRejected ])
    "escape fabricated a post-error product consumption checkpoint"
  case map contextOf cuts of
    [before, started, body, rejected] -> do
      assert (Core.startSharedLoan permit before == Right started &&
              started == body && body == rejected &&
              Core.sharedLoans rejected == Set.singleton permit &&
              Core.affineBindings rejected == Map.singleton permit permitTy &&
              Core.linearBindings rejected == Map.singleton payload bytes8)
        "escape did not preserve both source owners or exact active loan"
    _ -> Left "escape snapshot count mismatch"

checkReturnError :: Text -> RejectionClass -> Text -> Either String ()
checkReturnError source expectedClass expectedDetail = do
  result <- checked source
  checkCommon result
  case affineProductOutcome result of
    Left err -> assert
      (surfaceErrorClass err == expectedClass &&
       surfaceErrorDetail err == expectedDetail)
      ("unexpected exact product return error: " ++ show err)
    other -> Left ("invalid product return accepted: " ++ show other)
  assert (map tracePhase (affineProductCheckpoints result) ==
          [TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False, TraceLoanClosed])
    "rejected product return acquired fictitious successful terminal checkpoint"

checkErrorClass :: Text -> RejectionClass -> Either String ()
checkErrorClass source expectedClass = do
  result <- checked source
  checkCommon result
  case affineProductOutcome result of
    Left err -> assert (surfaceErrorClass err == expectedClass)
      ("duplicate restricted owner rejected for wrong reason: " ++ show err)
    other -> Left ("duplicate owner accepted: " ++ show other)
  assert (map tracePhase (affineProductCheckpoints result) ==
          [TraceBeforeLoan,TraceLoanStarted,TraceBodyResult False,TraceLoanClosed])
    "duplicated owner error fabricated a return successor"

checkNominalAuthority :: Text -> Text -> Either String ()
checkNominalAuthority noEvidence weakens = do
  assert (check Nothing noEvidence == Just (Left
          (AffineProductNominalError (GrammarV1DataModeNominalError
             (StrongerModeMissingJustification Unrestricted Affine)))))
    "source mode spelling was accepted as external lifecycle evidence"
  assert (check (Just (UnadmittedNominalRestriction "unreviewed"))
          noEvidence == Just (Left
            (AffineProductNominalError (GrammarV1DataModeNominalError
              (StrongerModeUnadmittedJustification "unreviewed")))))
    "unadmitted nominal restriction bypassed lifecycle authority"
  assert (check Nothing weakens == Just (Left
          (AffineProductNominalError (GrammarV1DataModeNominalError
            (DeclaredModeWeakensDerived Linear Unrestricted)))))
    "nominal Unrestricted weakened a Linear Bytes payload"

-- The opt-in named-flat-product helper must reject missing/ambiguous/wrong
-- resolution rather than fabricate a nominal mode by spelling. Its resolver
-- entries are themselves supplied by the caller, and must not be treated as
-- independent certificate verification.
checkResolutionGuards :: Text -> Either String ()
checkResolutionGuards source = do
  (_,fn) <- parsePair source
  result <- maybe (Left "source result missing") Right
    (grammarV1FunctionResultType fn)
  let ref = ReferencedGenericStaticActual "Permit"
      trusted = GrammarV1ResolvedNamedTypeMode
        { resolvedNamedTypeReference = ref
        , resolvedNamedTypeKind = GenericTypeKind
        , resolvedNamedTypeDeclarationKey = root
        , resolvedNamedTypeInterfaceRevision = revision
        , resolvedNamedTypeCheckedMode = CheckedTypeMode permitTy Affine
        }
      query rs = grammarV1CheckedFlatProductWithNamedResolutions
        emptyStaticContext emptySurfaceState rs (locatedValue result)
      wrongKind = trusted { resolvedNamedTypeKind = GenericIndexKind }
      ambiguous = trusted
        { resolvedNamedTypeDeclarationKey = DeclarationKey "other.nominal.root" }
      wrongType = trusted
        { resolvedNamedTypeCheckedMode = CheckedTypeMode
            (TyOpaque "WrongPermit") Affine }
  assert (query [] == Just (Left (GrammarV1NamedTypeModeUnresolved ref)))
    "unresolved nominal product element escaped fail-closed check"
  assert (query [wrongKind] ==
          Just (Left (GrammarV1NamedTypeModeKindMismatch ref [GenericIndexKind])))
    "wrong-kind nominal product resolution was accepted"
  assert (query [trusted,ambiguous] ==
          Just (Left (GrammarV1NamedTypeModeAmbiguous ref
            [root, DeclarationKey "other.nominal.root"])))
    "ambiguous nominal product resolver did not fail"
  assert (query [wrongType] ==
          Just (Left (GrammarV1NamedTypeModeCheckedTypeMismatch
            ref permitTy (TyOpaque "WrongPermit"))))
    "wrong nominal product semantic type was accepted"
  case query [trusted] of
    Just (Right resolved) -> do
      assert (checkedResolvedFlatProductMode resolved ==
              CheckedTypeMode productTy Linear &&
              map checkedResolvedTypeMode
                (checkedResolvedFlatProductElements resolved) ==
                  [CheckedTypeMode permitTy Affine, CheckedTypeMode bytes8 Linear] &&
              null (checkedResolvedFlatProductFocusingSteps resolved))
        "opt-in product resolver did not preserve exact ordered checked modes"
    other -> Left ("checked nominal flat product not admitted: " ++ show other)
  assert (grammarV1CheckedTypeMode emptyStaticContext emptySurfaceState
          (locatedValue result) == Nothing)
    "primitive-only legacy source route silently admitted nominal product"

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source label = assert (check lifecycle source == Nothing)
  ("unsupported source admitted via nominal-flat route: " ++ label)

main :: IO ()
main = do
  accepted <- TextIO.readFile (sourceDir ++ "accepted.phil")
  reversed <- TextIO.readFile (sourceDir ++ "reversed.phil")
  wrongWidth <- TextIO.readFile (sourceDir ++ "wrong-width.phil")
  wrongMode <- TextIO.readFile (sourceDir ++ "wrong-mode.phil")
  twiceAffine <- TextIO.readFile (sourceDir ++ "duplicate-affine.phil")
  twiceLinear <- TextIO.readFile (sourceDir ++ "duplicate-linear.phil")
  escaping <- TextIO.readFile (sourceDir ++ "escape.phil")
  unjustified <- TextIO.readFile (sourceDir ++ "unjustified.phil")
  weakened <- TextIO.readFile (sourceDir ++ "weakened.phil")
  unknown <- TextIO.readFile (sourceDir ++ "unknown-named.phil")
  nested <- TextIO.readFile (sourceDir ++ "nested.phil")
  wrongArity <- TextIO.readFile (sourceDir ++ "wrong-arity.phil")
  wrongBorrow <- TextIO.readFile (sourceDir ++ "wrong-borrow.phil")
  let mismatch = "returned tuple elements do not match the checked product contract"
      outcome = do
        checkAccepted accepted
        checkResolutionGuards accepted
        checkReturnError reversed TypeMismatch mismatch
        checkReturnError wrongWidth TypeMismatch mismatch
        checkReturnError wrongMode TypeMismatch mismatch
        checkErrorClass twiceAffine StructuralUse
        checkErrorClass twiceLinear StructuralUse
        checkEscape escaping
        checkNominalAuthority unjustified weakened
        assert (check lifecycle unknown ==
          Just (Left (AffineProductTypeError
            (GrammarV1NamedTypeModeUnresolved
              (ReferencedGenericStaticActual "Unknown")))))
          "unknown source nominal result was given an invented mode"
        checkUnsupported nested "nested nominal product"
        checkUnsupported wrongArity "three-value return"
        checkUnsupported wrongBorrow "linear borrow instead of Permit"
        assert (Text.replace "view; unit;" "view;" accepted == escaping)
          "BorrowEscape is not minimally different from accepted product source"
  case outcome of
    Right () -> putStrLn
      "PASS: exact source nominal affine/linear TyProduct, production moves, negative errors, provenance"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
