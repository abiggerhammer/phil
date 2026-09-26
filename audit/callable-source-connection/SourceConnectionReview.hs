{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified CatalogFixture as Catalog
import qualified ShellFixture as Shell
import Phil.Compiler.CallableInvocation
import Phil.Compiler.SourceBundle
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.EffectPolymorphism
import Phil.Core.Generic
import Phil.Core.Generic.StaticActual
import Phil.Core.Static
import Phil.Core.Syntax (Control (..), Proposition (..), Ty (..))
import Phil.Examples.Steve.ApplicationShell
import Phil.Surface.Check (RejectionClass (ControlAfterTerminal), SurfaceCheckError (..), SurfaceCheckResult (..))
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CallableEffects
import Phil.Surface.GrammarV1.CallableSignature
import Phil.Surface.GrammarV1.FunctionBodySurface
import Phil.Surface.GrammarV1.GenericBinderScope
import Phil.Surface.GrammarV1.GenericDischarge
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticEffectPolymorphism
import Phil.Surface.GrammarV1.SpecializedStaticReference
import Phil.Surface.Syntax (Located (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)

type Result a = Either String a
right :: Show e => Either e a -> Result a
right = either (Left . show) Right
need :: String -> Maybe a -> Result a
need label = maybe (Left ("unsupported fixture: " <> label)) Right
check :: Bool -> String -> Result ()
check True _ = Right ()
check False detail = Left detail
one :: String -> [a] -> Result a
one _ [value] = Right value
one label values = Left (label <> ": expected one, got " <> show (length values))
reject :: (Show e, Show a) => String -> (e -> Bool) -> Either e a -> Result ()
reject _ predicate (Left err) | predicate err = Right ()
reject label _ result = Left (label <> ": unexpected result " <> show result)

-- Parser failures are fixture failures, never expected semantic rejections.
declaration :: Text -> Result GrammarV1Declaration
declaration text = do
  parsed <- right $ parseGrammarV1StructuralSource "source-connection-audit" text
  top <- one "declaration" (grammarV1TopLevelDecls parsed)
  pure $ locatedValue $ grammarV1Declaration $ locatedValue top
function :: Text -> Result GrammarV1FunctionDecl
function text = do
  parsed <- declaration text
  case parsed of
    GrammarV1FunctionDeclaration value -> Right value
    _ -> Left "fixture is not a function"
callable :: Text -> Result GrammarV1CallableContractDecl
callable text = do
  parsed <- declaration text
  case parsed of
    GrammarV1CallableContractDeclaration value -> Right value
    _ -> Left "fixture is not a callable"
reference :: Text -> Result GrammarV1StaticReference
reference text = do
  parsed <- declaration text
  case parsed of
    GrammarV1TypeAliasDeclaration alias -> case locatedValue (grammarV1TypeAliasTarget alias) of
      GrammarV1NamedType value -> Right value
      _ -> Left "fixture alias has no static reference"
    _ -> Left "fixture is not an alias"

root :: DeclarationKey
root = DeclarationKey "audit.callable.source"
iface :: InterfaceRevision
iface = InterfaceRevision "audit.callable.interface.v1"

telescope :: Result ()
telescope = do
  source <- function "fn f[T : Type, n : Nat](x : U8) -> U8 satisfies C { return x; }"
  renamed <- function "\nfn f[Element : Type, count : Nat](x : U8) -> U8 satisfies C { return x; }"
  (left,scope) <- right $ grammarV1FunctionGenericParameterScope root source
  (renamedParameters,_) <- right $ grammarV1FunctionGenericParameterScope root renamed
  (foreignParameters,_) <- right $ grammarV1FunctionGenericParameterScope (DeclarationKey "audit.other") source
  let parameters = map grammarV1ResolvedGenericParameter
  check (parameters left == parameters renamedParameters) "alpha-renaming changed semantic keys/kinds"
  check (map genericStaticParameterKind (parameters left) == [GenericTypeKind,GenericIndexKind]) "wrong kinds/order"
  check (and (zipWith (/=) (parameters left) (parameters foreignParameters))) "different declaration roots reused identities"
  check (map grammarV1ResolvedGenericSource left == grammarV1FunctionGenericParams source) "source telescope was reconstructed/reordered"
  first <- case left of
    x:_ -> Right x
    [] -> Left "empty telescope"
  let name = grammarV1GenericParamName (locatedValue (grammarV1ResolvedGenericSource first))
  resolved <- right $ grammarV1ResolveGenericParameter name scope
  check (resolved == first) "lookup changed actual resolved binder"

duplicateBinder :: Result ()
duplicateBinder = do
  source <- function "fn f[T : Type, T : Nat]() -> Unit satisfies C { return unit; }"
  reject "duplicate telescope" matches $ grammarV1FunctionGenericParameterScope root source
  where
    matches (GrammarV1DuplicateGenericBinder name previous) =
      locatedValue name == "T" && genericStaticParameterKind (grammarV1ResolvedGenericParameter previous) == GenericTypeKind
    matches _ = False

poly :: Result GrammarV1CallableContractDecl
poly = callable "callable Poly[E : Effects] requires { effects E within {IO, Audit}; } () -> Unit { effects E; }"

-- This adapter only composes real source/kind-specific producers. Root/interface
-- selection and placement of the returned objects are explicit audit premises.
-- No general source-to-call environment producer is asserted.
application :: GrammarV1CallableContractDecl -> Text -> Result (GrammarV1StaticReference, GrammarV1ResolvedDirectStaticArgument, GrammarV1CheckedSpecializedStaticReference)
application source text = do
  ref <- reference text
  argument <- one "static argument" (grammarV1StaticReferenceArguments ref)
  effects <- case argument of
    GrammarV1StaticEffectSetArgument set -> need "literal Effects" $ grammarV1EffectSet (locatedValue set)
    _ -> Left "fixture is not a literal Effects actual"
  (resolved,_) <- right $ grammarV1CallableGenericParameterScope root source
  let direct = GrammarV1ResolvedDirectStaticArgument argument GenericEffectsKind (effectSetSemanticForm effects)
  checked <- need "specialized application" (grammarV1CheckedSpecializedStaticReference root iface
    (map grammarV1ResolvedGenericParameter resolved) [direct] [] ref) >>= right
  pure (ref,direct,checked)

sourceActual :: Result ()
sourceActual = do
  source <- poly
  (ref,direct,checked) <- application source "type T = Poly[{IO, IO}];"
  actual <- one "checked static actual" (checkedSpecializedStaticArguments checked)
  check (resolvedDirectStaticSourceArgument direct `elem` grammarV1StaticReferenceArguments ref) "source actual not retained"
  check (checkedGenericStaticSemanticForm actual == effectSetSemanticForm (Set.singleton (SemanticEffect "IO"))) "source effect meaning was not canonical"
  let identity = checkedSpecializedStaticApplicationIdentity checked
  check (genericApplicationDeclarationKey identity == root && genericApplicationInterfaceRevision identity == iface) "target identity drifted"
  check (genericApplicationSemanticArguments identity == Map.singleton (checkedGenericStaticParameterKey actual) (checkedGenericStaticSemanticForm actual)) "application did not retain the actual checked map"

directEvidenceDomain :: Result ()
directEvidenceDomain = do
  source <- poly
  (ref,direct,_) <- application source "type T = Poly[{IO}];"
  (resolved,_) <- right $ grammarV1CallableGenericParameterScope root source
  let run evidence = grammarV1CheckedSpecializedStaticReference root iface (map grammarV1ResolvedGenericParameter resolved) evidence [] ref
      argument = resolvedDirectStaticSourceArgument direct
  check (run [] == Just (Left (GrammarV1MissingDirectStaticArgumentEvidence argument))) "missing direct evidence was not rejected exactly"
  check (run [direct,direct] == Just (Left (GrammarV1DuplicateDirectStaticArgumentEvidence argument))) "duplicate direct evidence was not rejected exactly"

bareReference :: Result ()
bareReference = do
  source <- poly
  (_,direct,_) <- application source "type T = Poly[{IO}];"
  bare <- reference "type T = Poly[Shared];"
  argument <- one "bare argument" (grammarV1StaticReferenceArguments bare)
  (resolved,_) <- right $ grammarV1CallableGenericParameterScope root source
  let parameters = map grammarV1ResolvedGenericParameter resolved
      semantic = resolvedDirectStaticSemanticForm direct
      candidates = [GenericStaticReferenceCandidate "Shared" GenericEffectsKind semantic]
      run evidence refs = grammarV1CheckedSpecializedStaticReference root iface parameters evidence refs bare
  accepted <- need "bare actual" (run [] candidates) >>= right
  actual <- one "bare checked actual" (checkedSpecializedStaticArguments accepted)
  check (checkedGenericStaticKind actual == GenericEffectsKind && checkedGenericStaticSemanticForm actual == semantic) "declared-kind selection changed actual"
  check (run [GrammarV1ResolvedDirectStaticArgument argument GenericEffectsKind semantic] candidates
    == Just (Left (GrammarV1UnexpectedDirectEvidenceForBareReference argument))) "bare reference accepted direct override"
  bareTarget <- reference "type T = Poly;"
  check (grammarV1CheckedSpecializedStaticReference root iface [] [] [] bareTarget == Nothing) "bare target acquired specialization"

boundedActuals :: Result ()
boundedActuals = do
  source <- poly
  bounds <- right $ grammarV1CheckedCallableEffectParameterBounds root source
  bound <- one "source bound" bounds
  (_,_,ioApp) <- application source "type T = Poly[{IO}];"
  (_,_,auditApp) <- application source "type T = Poly[{Audit}];"
  ioActual <- one "IO actual" (checkedSpecializedStaticArguments ioApp)
  auditActual <- one "Audit actual" (checkedSpecializedStaticArguments auditApp)
  ioChecked <- right $ checkBoundedEffectSetInstantiation (checkedCallableEffectParameterBoundCore bound) ioActual
  auditChecked <- right $ checkBoundedEffectSetInstantiation (checkedCallableEffectParameterBoundCore bound) auditActual
  (parameters,scope) <- right $ grammarV1CallableGenericParameterScope root source
  parameter <- one "Effects parameter" parameters
  use <- one "effect use" [u | Located _ (GrammarV1CallableEffects u) <- grammarV1CallableClauses source]
  sourceName <- case locatedValue use of
    GrammarV1EffectSetReference r -> case grammarV1QualifiedNameParts (grammarV1StaticReferenceName (locatedValue r)) of
      [name] -> Right (Located (locatedSpan r) name)
      _ -> Left "not a bare effect use"
    _ -> Left "not an effect parameter use"
  resolvedUse <- right $ grammarV1ResolveGenericParameter sourceName scope
  let key = genericStaticParameterKey (grammarV1ResolvedGenericParameter resolvedUse)
  templates <- need "source templates" (grammarV1ResolvedCallableEffectBounds
    [GrammarV1ResolvedCallableEffectsParameter (grammarV1ResolvedGenericSource parameter) (grammarV1ResolvedGenericParameter parameter)]
    [GrammarV1ResolvedCallableEffectUse use key] source) >>= right
  ioResult <- right $ grammarV1InstantiateCallableEffectBounds [ioChecked] templates
  auditResult <- right $ grammarV1InstantiateCallableEffectBounds [auditChecked] templates
  check (ioResult == [Set.singleton (SemanticEffect "IO")] && auditResult == [Set.singleton (SemanticEffect "Audit")]) "two applications lost their own admitted effect actuals"
  check (checkedEffectSetUpper ioChecked == checkedEffectSetUpper auditChecked && checkedSpecializedStaticApplicationIdentity ioApp /= checkedSpecializedStaticApplicationIdentity auditApp) "upper/application distinction lost"

boundIdentity :: Result ()
boundIdentity = do
  source <- poly
  (_,_,app) <- application source "type T = Poly[{IO}];"
  actual <- one "actual" (checkedSpecializedStaticArguments app)
  foreignBounds <- right $ grammarV1CheckedCallableEffectParameterBounds (DeclarationKey "audit.other") source
  foreignBound <- one "foreign bound" foreignBounds
  let core = checkedCallableEffectParameterBoundCore foreignBound
  check (checkBoundedEffectSetInstantiation core actual == Left
    (EffectSetParameterKeyMismatch (effectSetBoundParameterKey core) (checkedGenericStaticParameterKey actual))) "foreign declaration bound accepted"

header :: GrammarV1FunctionDecl -> Result GrammarV1CheckedFunctionHeader
header source = do
  (checked,_) <- need "closed header" (grammarV1CheckedClosedFunctionHeader emptyStaticContext root (DefinitionRevision "audit.definition") source) >>= right
  pure checked
body :: GrammarV1CheckedFunctionHeader -> GrammarV1FunctionDecl -> Result GrammarV1CheckedClosedFunctionBody
body h source = need "closed body" (grammarV1CheckedClosedFunctionBody emptyStaticContext h source) >>= right

closedPositive :: Result ()
closedPositive = mapM_ run [("Bool","true",TyBool),("Unit","unit",TyUnit)]
  where
    run (ty,value,expected) = do
      source <- function ("fn f() -> " <> ty <> " satisfies C { return " <> value <> "; }")
      h <- header source
      checked <- body h source
      check (checkedClosedFunctionBodyHeader checked == h && checkedClosedFunctionBodyControls checked == [Return expected]) "closed source/header/return connection drifted"

foreignHeader :: Result ()
foreignHeader = do
  source <- function "fn f() -> Bool satisfies C { return true; }"
  other <- function "fn g() -> Unit satisfies C { return unit; }"
  h <- header source
  foreignH <- header other
  _ <- body h source
  _ <- body foreignH other
  check (grammarV1CheckedClosedFunctionBody emptyStaticContext foreignH source == Just (Left
    (GrammarV1FunctionBodyHeaderMismatch foreignH h))) "independently checked foreign header attached to source"

bodyResults :: Result ()
bodyResults = do
  wrong <- function "fn f() -> Bool satisfies C { return unit; }"
  missing <- function "fn f() -> Bool satisfies C { true; }"
  terminated <- function "fn f() -> Bool satisfies C { return true; return false; }"
  hw <- header wrong
  hm <- header missing
  ht <- header terminated
  check (grammarV1CheckedClosedFunctionBody emptyStaticContext hw wrong == Just (Left
    (GrammarV1FunctionBodyResultMismatch TyBool [Return TyUnit]))) "wrong body result accepted"
  check (grammarV1CheckedClosedFunctionBody emptyStaticContext hm missing == Just (Left
    (GrammarV1FunctionBodyResultMismatch TyBool [Continue]))) "missing return accepted"
  case grammarV1CheckedClosedFunctionBody emptyStaticContext ht terminated of
    Just (Left (GrammarV1FunctionBodySurfaceCheckError err)) | surfaceErrorClass err == ControlAfterTerminal -> Right ()
    other -> Left ("sequencing gate changed: " <> show other)

bodyNoncompetence :: Result ()
bodyNoncompetence = do
  param <- function "fn f(x : U8) -> Unit satisfies C { return unit; }"
  calls <- function "fn f() -> Bool satisfies C { return invoke C(); }"
  generic <- function "fn f[T : Type]() -> Unit satisfies C { return unit; }"
  hp <- header param
  hc <- header calls
  check (grammarV1CheckedClosedFunctionBody emptyStaticContext hp param == Nothing) "parameterized body became competent"
  check (grammarV1CheckedClosedFunctionBody emptyStaticContext hc calls == Nothing) "call body became competent"
  check (grammarV1CheckedClosedFunctionHeader emptyStaticContext root (DefinitionRevision "audit.definition") generic == Nothing) "generic header became closed"

genericSource :: Result ()
genericSource = do
  source <- callable "callable Constant[E : Effects] requires { proposition true; } () -> Unit { effects E; }"
  (_,_,app) <- application source "type T = Constant[{IO}];"
  occurrence <- one "requirement occurrence" (grammarV1CallableRequirements source)
  let requirementSet = GrammarV1ResolvedGenericRequirementSet root iface [occurrence]
      -- GenericEvidence is the explicit competent-input premise of this API.
      -- The trivial Truth fixture is not claimed to establish an arbitrary proof.
      evidence = GenericSatisfiedByEvidence (GenericEvidence Truth "audit.truth")
      disposition = GrammarV1ResolvedRequirementDisposition occurrence evidence
      run set ds = grammarV1CheckedStrictSpecializedGenericDischarge emptyStaticContext emptySurfaceState [] []
        (DefinitionRevision "audit.definition") app set ds
  result <- need "constant source requirement" (run requirementSet [disposition]) >>= right
  check (checkedGenericDischargeApplication result == app) "discharge changed actual application"
  check (map checkedGenericRequirementSource (checkedGenericDischargeRequirements result) == [occurrence]) "source occurrence changed"
  check (genericDischargeApplicationIdentity (checkedGenericDischargeLineage result) == checkedSpecializedStaticApplicationIdentity app) "lineage lost actual application"
  check (run requirementSet [] == Just (Left (GrammarV1MissingRequirementDisposition occurrence))) "missing occurrence disposition accepted"
  check (run requirementSet [disposition,disposition] == Just (Left (GrammarV1DuplicateRequirementDisposition occurrence))) "duplicate occurrence disposition accepted"
  let foreignSet = GrammarV1ResolvedGenericRequirementSet (DeclarationKey "audit.other") iface [occurrence]
  check (run foreignSet [disposition] == Just (Left (GrammarV1GenericRequirementTargetMismatch root iface (DeclarationKey "audit.other") iface))) "foreign requirement set accepted"

catalogRename :: Result ()
catalogRename = do
  (original,contracts) <- Catalog.baseChecked
  renamed <- Catalog.checkedBundle
    [(Catalog.callerKey,"unit.caller","site.caller","Caller"),(Catalog.workerKey,"unit.worker","site.worker","Renamed")]
  left <- right $ buildCallableInvocationCatalog Set.empty contracts original
  rightCatalog <- right $ buildCallableInvocationCatalog (Set.singleton "Renamed") contracts renamed
  before <- right $ resolveCallableInvocation left "Worker" Catalog.workerExpectation
  after <- right $ resolveCallableInvocation rightCatalog "Renamed" Catalog.workerExpectation
  check (sourceCallableDeclarationKey (resolvedCallableBinding after) == Catalog.workerKey && sourceCallableContract (resolvedCallableBinding after) == sourceCallableContract (resolvedCallableBinding before)) "source rename changed persisted identity/contract"
  check (resolvedCallableRefinement after == resolvedCallableRefinement before && resolvedCallableOutcomes after == resolvedCallableOutcomes before) "source rename changed checked semantic witnesses"
  reject "old lookup" (== CallableNameUnknown "Worker") $ resolveCallableInvocation rightCatalog "Worker" Catalog.workerExpectation

catalogDomain :: Result ()
catalogDomain = do
  (checked,contracts) <- Catalog.baseChecked
  reject "missing contract" (== CallableContractMissing Catalog.workerKey) $
    buildCallableInvocationCatalog Set.empty (Map.delete Catalog.workerKey contracts) checked
  let outside = DeclarationKey "audit.outside"
  reject "outside contract" (== CallableContractOutsideBundle outside) $
    buildCallableInvocationCatalog Set.empty (Map.insert outside Catalog.workerContract contracts) checked
  ambiguous <- Catalog.checkedBundle
    [(Catalog.callerKey,"unit.caller","site.caller","Caller"),(Catalog.workerKey,"unit.a","site.a","Worker"),(Catalog.workerOtherKey,"unit.b","site.b","Worker")]
  table <- right $ buildCallableInvocationCatalog Set.empty (Map.insert Catalog.workerOtherKey Catalog.workerContract contracts) ambiguous
  reject "ambiguous source name" (== CallableNameAmbiguous "Worker" [Catalog.workerKey,Catalog.workerOtherKey]) $
    resolveCallableInvocation table "Worker" Catalog.workerExpectation
  ordinary <- right $ buildCallableInvocationCatalog (Set.singleton "ProviderOnly") contracts checked
  reject "provider-only name" (== CallableNameRefersOnlyToProviderPrimitive "ProviderOnly") $
    resolveCallableInvocation ordinary "ProviderOnly" Catalog.workerExpectation

catalogIndependentInterfaces :: Result ()
catalogIndependentInterfaces = do
  (checked,contracts) <- Catalog.baseChecked
  let alternate = Catalog.workerContract { sourceCallableRefinementSurface = Catalog.callableSurface "worker.v2" "Unit->Unit" }
      expectation = CallableInvocationExpectation Catalog.workerKey alternate
  first <- right $ buildCallableInvocationCatalog Set.empty contracts checked
  second <- right $ buildCallableInvocationCatalog Set.empty (Map.insert Catalog.workerKey alternate contracts) checked
  _ <- right $ resolveCallableInvocation first "Worker" Catalog.workerExpectation
  _ <- right $ resolveCallableInvocation second "Worker" expectation
  reject "valid foreign interface" (== CallableInterfaceRevisionMismatch "Worker" (InterfaceRevision "worker.v2") (InterfaceRevision "worker.v1")) $
    resolveCallableInvocation first "Worker" expectation
  reject "valid foreign declaration" (== CallableDeclarationIdentityMismatch "Worker" Catalog.workerOtherKey Catalog.workerKey) $
    resolveCallableInvocation first "Worker" (CallableInvocationExpectation Catalog.workerOtherKey Catalog.workerContract)

shellSource :: Text -> Text -> Result ()
shellSource putSource getSource = do
  checked <- Shell.checkedShell putSource getSource
  check (map checkedSourceDeclarationKey (checkedSourceUnits checked) == [Shell.putDeclaration,Shell.getDeclaration]) "shipped source identities changed"
  check (all (not . null . checkedTerminalControls . checkedSourceResult) (checkedSourceUnits checked)) "shipped caller lost checked controls"
  Shell.callableBindingsAreExact

shellEnvironmentDomain :: Text -> Text -> Result ()
shellEnvironmentDomain putSource getSource = do
  putEnvironment <- either (Left . Text.unpack) Right stevePutShellEnvironment
  reject "missing actual declaration environment" (== SourceBundleEnvironmentMissing Shell.getDeclaration) $
    checkPortableSourceBundle Shell.shellRoots (Map.singleton Shell.putDeclaration putEnvironment) (Shell.shellBundle putSource getSource)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [subject] -> do
      putSource <- TextIO.readFile (subject <> "/examples/steve/put-cli.phil")
      getSource <- TextIO.readFile (subject <> "/examples/steve/get-cli.phil")
      results <- mapM report
        [ ("P01", "parsed telescope preserves alpha identity, order and root separation", telescope)
        , ("P02", "parsed duplicate static binders reject at scope authority", duplicateBinder)
        , ("P03", "parsed literal Effects flow into actual application identity", sourceActual)
        , ("P04", "exact direct source evidence domain is mandatory", directEvidenceDomain)
        , ("P05", "bare actual resolution cannot be replaced by direct evidence", bareReference)
        , ("P06", "two genuine source applications preserve their own bounded effect results", boundedActuals)
        , ("P07", "source-derived bound from another declaration rejects", boundIdentity)
        , ("P08", "same-source closed headers and exact return controls compose", closedPositive)
        , ("P09", "independently valid foreign header rejects before body credit", foreignHeader)
        , ("P10", "wrong or missing return and terminal sequencing reject", bodyResults)
        , ("P11", "generic parameterized and call bodies retain bounded noncompetence", bodyNoncompetence)
        , ("P12", "real specialized application retains exact constant requirement domain", genericSource)
        , ("P13", "real checked-source catalog preserves renamed declaration and witnesses", catalogRename)
        , ("P14", "catalog declaration domain and namespace ambiguity remain exact", catalogDomain)
        , ("P15", "independently accepted interfaces reject cross-association", catalogIndependentInterfaces)
        , ("P16", "shipped Steve source consumes actual fixed callable environments", shellSource putSource getSource)
        , ("P17", "shipped source cannot borrow another declaration's environment entry", shellEnvironmentDomain putSource getSource)
        ]
      putStrLn "COMPLETE source_connection_groups=17"
      unless (and results) exitFailure
    _ -> putStrLn "usage: SourceConnectionReview SUBJECT" >> exitFailure

report :: (String,String,Result ()) -> IO Bool
report (key,label,result) = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left detail -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> detail) >> pure False
