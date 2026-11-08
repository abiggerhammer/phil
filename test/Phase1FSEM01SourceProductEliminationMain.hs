{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: source-derived product elimination through the actual production
-- Surface checker and independently replayed native Core.DataMode.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import qualified Phil.Core.DataMode as DataMode
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.NominalDataMode
  ( NominalModeError (..), NominalRestrictionJustification (..) )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), emptyStaticContext )
import Phil.Core.Syntax
  ( Control (..), Mode (..), Name (..), ProductElementType (..)
  , RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine (ProductEliminationRun (..))
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..), GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..) )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataModeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl, GrammarV1FunctionDecl
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..), parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceProductElimination
  ( GrammarV1ProductEliminationError (..)
  , GrammarV1ProductEliminationTrace (..)
  , grammarV1CheckedProductEliminationTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

dataRoot, functionRoot :: DeclarationKey
dataRoot = DeclarationKey "decl.fsem01.product-elim.Permit"
functionRoot = DeclarationKey "decl.fsem01.product-elim.unpack"

revision :: InterfaceRevision
revision = InterfaceRevision "iface.fsem01.product-elim.v1"

attestation :: Maybe NominalRestrictionJustification
attestation = Just (AdmittedLifecycleObligation
  "reviewed external Permit lifecycle disposition")

permitTy, payloadTy, productTy :: Ty
permitTy = TyOpaque "Permit"
payloadTy = TyBytes (RefNat 8)
productTy = TyProduct
  [ProductElementType Affine permitTy, ProductElementType Linear payloadTy]

directory :: FilePath
directory = "test/fixtures/fsem01-source-product-elimination-v1/"

assert :: Bool -> String -> Either String ()
assert ok why = if ok then Right () else Left why

parsePair :: Text -> Either String (GrammarV1DataDecl, GrammarV1FunctionDecl)
parsePair src = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "source-product-elimination" src)
  case grammarV1TopLevelDecls parsed of
    [Located _ dat, Located _ fn] ->
      case (locatedValue (grammarV1Declaration dat),
            locatedValue (grammarV1Declaration fn)) of
        (GrammarV1DataDeclaration d, GrammarV1FunctionDeclaration f) ->
          Right (d,f)
        _ -> Left "expected data declaration and source function"
    _ -> Left "expected exactly two source declarations"

check :: Maybe NominalRestrictionJustification -> Text
  -> Maybe (Either GrammarV1ProductEliminationError
       GrammarV1ProductEliminationTrace)
check evidence src = case parsePair src of
  Left _ -> Nothing
  Right (d, fn) -> grammarV1CheckedProductEliminationTrace
    emptyStaticContext dataRoot revision evidence d functionRoot fn

checked :: Text -> Either String GrammarV1ProductEliminationTrace
checked src = case check attestation src of
  Just (Right result) -> Right result
  other -> Left ("source product not admitted to production: " ++ show other)

ownerName :: GrammarV1ProductEliminationTrace -> Name
ownerName = grammarV1ResolvedBinderCoreName . eliminatedSourceOwnerBinder

successors :: GrammarV1ProductEliminationTrace -> [Name]
successors = map grammarV1ResolvedBinderCoreName .
  eliminatedSourceSuccessorBinders

beforeContext :: GrammarV1ProductEliminationTrace -> Core.ResourceContext
beforeContext result = Core.ResourceContext Map.empty Map.empty
  (Map.singleton (ownerName result) productTy) Set.empty

afterContext :: Name -> Name -> Core.ResourceContext
afterContext permit payload = Core.ResourceContext Map.empty
  (Map.singleton permit permitTy)
  (Map.singleton payload payloadTy) Set.empty

checkTransition
  :: GrammarV1ProductEliminationTrace
  -> Either String (Name, Name, Core.ResourceContext)
checkTransition result = do
  let run = eliminatedSourceProduction result
  assert (eliminatedSourceDeclarationKey result == dataRoot &&
          eliminatedSourceInterfaceRevision result == revision)
    "source declaration/revision provenance changed"
  assert (eliminatedSourceParameter result == CheckedTypeMode productTy Linear)
    "input product lost its checked source aggregate mode or type"
  assert (map checkedResolvedTypeMode (eliminatedSourceElements result) ==
          [CheckedTypeMode permitTy Affine, CheckedTypeMode payloadTy Linear] &&
          map checkedResolvedTypeModeOrigin (eliminatedSourceElements result) ==
          [GrammarV1NamedTypeModeOrigin
             (ReferencedGenericStaticActual "Permit") dataRoot revision,
           GrammarV1IntrinsicTypeModeOrigin])
    "source mode/provenance of a restored member was invented"
  assert (productEliminationBefore run == Just (beforeContext result))
    "production input was not a single linear product owner"
  case successors result of
    [permit,payload] -> do
      assert (ownerName result /= permit && ownerName result /= payload &&
              permit /= payload)
        "product and restored successor identities collide"
      let expected = afterContext permit payload
      assert (productEliminationAfter run == Just expected)
        "production product elimination lost/mismoded an element"
      assert (DataMode.eliminateProductBinding
                (ownerName result) [permit,payload] (beforeContext result) ==
              Right expected)
        "actual source-driven transition differs from certified native Core"
      assert (Core.useBinding (ownerName result) expected ==
              Left (Core.UnknownBinding (ownerName result)))
        "consumed product remains reusable"
      assert (Core.ensureComplete expected ==
              Left (Core.UnconsumedLinearResources
                (Map.singleton payload payloadTy)))
        "restored linear debt was silently discharged"
      Right (permit,payload,expected)
    _ -> Left "expected exactly two restored semantic successors"

checkAcceptedPayload :: Text -> Either String ()
checkAcceptedPayload src = do
  result <- checked src
  (permit,payload,after) <- checkTransition result
  assert (eliminatedSourceReturn result == CheckedTypeMode payloadTy Linear &&
          eliminatedSourceOutcome result ==
            Right (SurfaceCheckResult "unpack" [Return payloadTy]))
    ("source return failed: " ++ show (eliminatedSourceOutcome result))
  (actual,terminal) <- either (Left . show) Right (Core.consumeLinear payload after)
  assert (actual == payloadTy &&
          terminal == Core.ResourceContext Map.empty
            (Map.singleton permit permitTy) Map.empty Set.empty &&
          Core.ensureComplete terminal == Right ())
    "returning linear successor did not leave only discardable affine state"
  assert (Core.consumeLinear payload terminal == Left (Core.UnknownBinding payload))
    "restored payload was consumed twice"

checkAcceptedBoth :: Text -> Either String ()
checkAcceptedBoth src = do
  result <- checked src
  (permit,payload,after) <- checkTransition result
  assert (eliminatedSourceReturn result == CheckedTypeMode productTy Linear &&
          eliminatedSourceOutcome result ==
            Right (SurfaceCheckResult "unpack" [Return productTy]))
    ("two-owner return failed: " ++ show (eliminatedSourceOutcome result))
  (affineTy,afterAffine) <- either (Left . show) Right
    (Core.consumeAffine permit after)
  (linearTy,terminal) <- either (Left . show) Right
    (Core.consumeLinear payload afterAffine)
  assert (affineTy == permitTy && linearTy == payloadTy &&
          terminal == Core.emptyContext && Core.ensureComplete terminal == Right ())
    "returning both restored owners failed exact consumption"

checkLinearDebt :: Text -> CheckedTypeMode -> Either String ()
checkLinearDebt src expectedMode = do
  result <- checked src
  (_,payload,after) <- checkTransition result
  let errorValue = Core.UnconsumedLinearResources (Map.singleton payload payloadTy)
  assert (eliminatedSourceReturn result == expectedMode)
    "negative source return type did not check"
  case eliminatedSourceOutcome result of
    Left err -> assert
      (surfaceErrorClass err == LinearCompletion &&
       surfaceErrorDetail err == Text.pack (show errorValue))
      ("wrong production linear completion error: " ++ show err)
    Right value -> Left ("live linear resource dropped: " ++ show value)
  assert (Core.ensureComplete after == Left errorValue)
    "exact restored owner state did not retain the linear debt"

checkReturnFailure :: Text -> RejectionClass
  -> (GrammarV1ProductEliminationTrace -> Text) -> Either String ()
checkReturnFailure src expectedClass expectedDetail = do
  result <- checked src
  _ <- checkTransition result
  case eliminatedSourceOutcome result of
    Left err -> assert
      (surfaceErrorClass err == expectedClass &&
       surfaceErrorDetail err == expectedDetail result)
      ("wrong return error class/detail: " ++ show err)
    Right value -> Left ("invalid source return passed: " ++ show value)

checkArityFailure :: Text -> Either String ()
checkArityFailure src = do
  result <- checked src
  let run = eliminatedSourceProduction result
  assert (length (successors result) == 3 &&
          productEliminationBefore run == Just (beforeContext result) &&
          productEliminationAfter run == Nothing)
    "failed product arity invented a successor or wrong source identities"
  case eliminatedSourceOutcome result of
    Left err -> assert
      (surfaceErrorClass err == TypeMismatch &&
       surfaceErrorDetail err == "product elimination: " <>
          Text.pack (show (DataMode.ProductArityMismatch 2 3)))
      ("unexpected arity error: " ++ show err)
    Right value -> Left ("3 successors accepted from 2-member product: " ++ show value)

checkBinderFailure :: Text -> Either String ()
checkBinderFailure src = case check attestation src of
  Just (Left (ProductEliminationBinderError (GrammarV1DuplicateBinder _ _))) ->
    Right ()
  other -> Left ("duplicate successor not rejected by source binder: " ++ show other)

checkAuthorityFailures :: Text -> Text -> Either String ()
checkAuthorityFailures positive weakened = do
  assert (check Nothing positive ==
    Just (Left (ProductEliminationNominalError
      (GrammarV1DataModeNominalError
        (StrongerModeMissingJustification Unrestricted Affine)))))
    "source mode spelling was accepted without lifecycle authority"
  assert (check (Just (UnadmittedNominalRestriction "unreviewed")) positive ==
    Just (Left (ProductEliminationNominalError
      (GrammarV1DataModeNominalError
        (StrongerModeUnadmittedJustification "unreviewed")))))
    "unadmitted lifecycle justification was accepted"
  assert (check Nothing weakened ==
    Just (Left (ProductEliminationNominalError
      (GrammarV1DataModeNominalError
        (DeclaredModeWeakensDerived Linear Unrestricted)))))
    "nominal unrestricted declaration weakened a linear payload"

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported src name = assert (check attestation src == Nothing)
  ("outside-competence source silently accepted: " ++ name)

main :: IO ()
main = do
  let get name = TextIO.readFile (directory ++ name ++ ".phil")
  accepted <- get "accepted"
  both <- get "return-both"
  affine <- get "return-affine"
  unit <- get "return-unit"
  owner <- get "return-product-owner"
  reversed <- get "reversed-return"
  duplicated <- get "duplicate-return"
  arity <- get "wrong-arity"
  duplicateBinder <- get "duplicate-successor"
  unjustified <- get "unjustified"
  weakened <- get "weakened"
  wrongParam <- get "wrong-parameter-order"
  wrongWidth <- get "wrong-result-width"
  wrongInit <- get "wrong-initializer"
  nested <- get "nested-pattern"
  let result = do
        checkAcceptedPayload accepted
        checkAcceptedBoth both
        checkLinearDebt affine (CheckedTypeMode permitTy Affine)
        checkLinearDebt unit (CheckedTypeMode TyUnit Unrestricted)
        checkReturnFailure owner StructuralUse
          (\trace -> "unknown or consumed binding: " <> unName (ownerName trace))
        checkReturnFailure reversed TypeMismatch
          (const "returned tuple elements do not match the checked product contract")
        checkReturnFailure duplicated StructuralUse
          (\trace -> case successors trace of
             [_,payload] -> "unknown or consumed binding: " <> unName payload
             _ -> "missing payload successor")
        checkArityFailure arity
        checkBinderFailure duplicateBinder
        checkAuthorityFailures unjustified weakened
        checkUnsupported wrongParam "reversed declared product"
        checkUnsupported wrongWidth "wrong scalar return size"
        checkUnsupported wrongInit "unresolved source initializer"
        checkUnsupported nested "nested tuple binding pattern"
  case result of
    Right () -> putStrLn
      "PASS: real single-source product elimination, exact affine/linear restoration and terminal errors"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
