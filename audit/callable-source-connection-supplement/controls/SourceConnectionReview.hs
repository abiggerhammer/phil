{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified CatalogFixture as Catalog
import qualified FunctionFixture as Function
import qualified GenericFixture as Generic
import Phil.Compiler.CallableInvocation
import Phil.Compiler.CallableInvocationContext
import Phil.Compiler.CallableInvocationSemantics
import Phil.Compiler.CallableSurfaceSemantics
import Phil.Compiler.SourceBundle
import Phil.Core.Callable (SemanticEffect)
import Phil.Core.EffectPolymorphism (effectSetSemanticForm)
import Phil.Core.Generic
  ( GenericApplicationIdentity (..), GenericDischargeLineage (..)
  , GenericEvidence (..), GenericInstantiationRecord (..)
  , GenericRequirement (..), GenericRequirementDisposition (..) )
import Phil.Core.Generic.StaticActual
import Phil.Core.Static (DeclarationKey (..), DefinitionRevision (..), InterfaceRevision (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Ty (..), Proposition (..))
import Phil.IO.Console
  ( ConsoleOperation (..), ConsoleOperationContract (..), consoleEnvironmentStdout
  , consoleOperationContract, standardConsoleEnvironment )
import Phil.Surface.Check
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CallableSignature
import Phil.Surface.GrammarV1.FunctionBodySurface
import Phil.Surface.GrammarV1.GenericBinderScope
import Phil.Surface.GrammarV1.GenericDischarge
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SpecializedStaticReference
import qualified Phil.Surface.Parser as Surface
import Phil.Surface.Syntax (Component (..), Located (..), SurfaceFile (..))
import System.Exit (ExitCode (..), exitWith)

-- PREPARED, UNCOMPILED, UNEXECUTED at creation. Namespace-only fixture imports
-- preserve the pinned production tests. This is not a production exporter.
-- Source lineage, referenced effect association, semantic contracts, and the
-- closed-Truth evidence identifier remain explicit supplied-interface premises.
-- Real returned checker/catalog/application/header objects are not fabricated.
data Failure = Harness String | Requirement String deriving Show
type Result a = Either Failure a
fixture :: Show e => Either e a -> Result a
fixture = either (Left . Harness . show) Right
accepted :: Show e => Either e a -> Result a
accepted = either (Left . Requirement . show) Right
assertion :: Bool -> String -> Result ()
assertion True _ = Right ()
assertion False reason = Left (Requirement reason)
exact :: (Eq a, Show a) => a -> a -> Result ()
exact expected actual = assertion (actual == expected)
  ("expected " <> show expected <> "; got " <> show actual)
competent :: Show e => Maybe (Either e a) -> Result a
competent Nothing = Left (Requirement "supported input unexpectedly outside competence")
competent (Just result) = accepted result

root :: DeclarationKey
root = DeclarationKey "audit.source.Worker"
revision :: InterfaceRevision
revision = InterfaceRevision "audit.source.Worker.interface"
definition :: DefinitionRevision
definition = DefinitionRevision "audit.source.Worker.definition"

parseFunction :: Text -> Result GrammarV1FunctionDecl
parseFunction = fixture . Function.onlyFunction
parseComponent :: Text -> Result (Located Component)
parseComponent source = do
  parsed <- fixture (Surface.parseSurfaceFile "audit-source-caller" source)
  case parsed of
    SurfaceFile [component] -> Right component
    _ -> Left (Harness "expected exactly one parsed component")

parametersOf :: DeclarationKey -> GrammarV1FunctionDecl -> Result [GenericStaticParameter]
parametersOf key source = do
  (resolved, _) <- accepted (grammarV1FunctionGenericParameterScope key source)
  pure (map grammarV1ResolvedGenericParameter resolved)

binderIdentity :: Result ()
binderIdentity = do
  source <- parseFunction "fn generic[T : Type, E : Effects]() -> Unit satisfies C { return unit; }"
  renamed <- parseFunction "fn generic[Element : Type, Footprint : Effects]() -> Unit satisfies C { return unit; }"
  first <- parametersOf root source
  second <- parametersOf root renamed
  elsewhere <- parametersOf (DeclarationKey "audit.other.Worker") source
  exact first second
  exact [GenericTypeKind, GenericEffectsKind] (map genericStaticParameterKind first)
  assertion (length first == 2 && length elsewhere == 2
    && and (zipWith (/=) (map genericStaticParameterKey first)
                        (map genericStaticParameterKey elsewhere)))
    "declaration-root change failed to change both ordinal keys"

binderDuplicate :: Result ()
binderDuplicate = do
  source <- parseFunction "fn duplicate[T : Type, T : Effects]() -> Unit satisfies C { return unit; }"
  case grammarV1FunctionGenericParameterScope root source of
    Left (GrammarV1DuplicateGenericBinder name previous) -> do
      exact "T" (locatedValue name)
      exact GenericTypeKind (genericStaticParameterKind (grammarV1ResolvedGenericParameter previous))
    result -> Left (Requirement ("expected duplicate telescope binder: " <> show result))

templateText :: Text
templateText = "fn Worker[E : Effects] requires { proposition true; }() -> Unit satisfies C { return unit; }"

applicationFor
  :: Text -> Set.Set SemanticEffect
  -> Result (GrammarV1FunctionDecl, GrammarV1CheckedSpecializedStaticReference)
applicationFor sourceText effects = do
  source <- parseFunction sourceText
  parameters <- parametersOf root source
  reference <- fixture (Generic.aliasStaticReference "type Applied = Worker[SuppliedEffects];")
  checked <- competent $ grammarV1CheckedSpecializedStaticReference
    root revision parameters []
    [GenericStaticReferenceCandidate "SuppliedEffects" GenericEffectsKind (effectSetSemanticForm effects)]
    reference
  pure (source, checked)

sourceActual :: Result ()
sourceActual = do
  (source, application) <- applicationFor templateText Set.empty
  parameters <- parametersOf root source
  case (parameters, checkedSpecializedStaticArguments application) of
    ([parameter], [actual]) -> do
      exact (genericStaticParameterKey parameter) (checkedGenericStaticParameterKey actual)
      exact GenericEffectsKind (checkedGenericStaticKind actual)
      exact (effectSetSemanticForm Set.empty) (checkedGenericStaticSemanticForm actual)
      exact (Map.singleton (genericStaticParameterKey parameter) (effectSetSemanticForm Set.empty))
        (genericApplicationSemanticArguments (checkedSpecializedStaticApplicationIdentity application))
    other -> Left (Harness ("expected one Effects parameter/actual: " <> show other))

sourceReferenceGuards :: Result ()
sourceReferenceGuards = do
  source <- parseFunction templateText
  parameters <- parametersOf root source
  reference <- fixture (Generic.aliasStaticReference "type Applied = Worker[SuppliedEffects];")
  case (parameters, grammarV1StaticReferenceArguments reference) of
    ([parameter], [argument]) -> do
      let key = genericStaticParameterKey parameter
          form = effectSetSemanticForm Set.empty
          candidate = GenericStaticReferenceCandidate "SuppliedEffects" GenericEffectsKind form
          run evidence candidates = grammarV1CheckedSpecializedStaticReference
            root revision parameters evidence candidates reference
      exact (Just (Left (GrammarV1SpecializedStaticKindError
        (GenericStaticReferenceUnresolved key GenericEffectsKind "SuppliedEffects"))))
        (run [] [])
      exact (Just (Left (GrammarV1SpecializedStaticKindError
        (GenericStaticReferenceAmbiguous key GenericEffectsKind "SuppliedEffects" [form, form]))))
        (run [] [candidate, candidate])
      exact (Just (Left (GrammarV1UnexpectedDirectEvidenceForBareReference argument)))
        (run [GrammarV1ResolvedDirectStaticArgument argument GenericEffectsKind form] [candidate])
    other -> Left (Harness ("unexpected telescope/reference shape: " <> show other))

trueDischarge
  :: GrammarV1FunctionDecl -> GrammarV1CheckedSpecializedStaticReference
  -> Result GrammarV1CheckedSpecializedGenericDischarge
trueDischarge source application = do
  let requirements = grammarV1FunctionRequirements source
      requirementSet = GrammarV1ResolvedGenericRequirementSet root revision requirements
      -- The closed Truth evidence is a caller premise. We do not pretend the
      -- evidence identity is a certificate emitted by source checking.
      disposition requirement = GrammarV1ResolvedRequirementDisposition requirement
        (GenericSatisfiedByEvidence (GenericEvidence { genericEvidenceProposition = Truth, genericEvidenceIdentity = "audit.supplied.closed-truth" }))
  assertion (length requirements == 1) "fixture must have one source requirement"
  competent $ grammarV1CheckedStrictSpecializedGenericDischarge
    emptyStaticContext emptySurfaceState [] [] definition application requirementSet
    (map disposition requirements)

closedRequirementLineage :: Result ()
closedRequirementLineage = do
  writeContract <- fixture (consoleOperationContract
    (consoleEnvironmentStdout standardConsoleEnvironment) ConsoleWriteOp)
  (firstSource, firstApp) <- applicationFor templateText Set.empty
  (secondSource, secondApp) <- applicationFor templateText (Set.singleton (consoleContractEffect writeContract))
  first <- trueDischarge firstSource firstApp
  second <- trueDischarge secondSource secondApp
  assertion (checkedSpecializedStaticApplicationIdentity firstApp /=
             checkedSpecializedStaticApplicationIdentity secondApp)
    "different real finite Effects actuals lost distinct application identities"
  let checkRetention source application result = do
        exact application (checkedGenericDischargeApplication result)
        exact (grammarV1FunctionRequirements source)
          (map checkedGenericRequirementSource (checkedGenericDischargeRequirements result))
        exact [GenericPropositionRequirement Truth]
          (map checkedGenericRequirementCore (checkedGenericDischargeRequirements result))
        exact (checkedSpecializedStaticApplicationIdentity application)
          (genericDischargeApplicationIdentity (checkedGenericDischargeLineage result))
        exact definition (genericDischargeDefinitionRevision (checkedGenericDischargeLineage result))
        exact (genericInstantiationDispositions (checkedGenericDischargeInstantiation result))
          (genericDischargeDispositions (checkedGenericDischargeLineage result))
  checkRetention firstSource firstApp first
  checkRetention secondSource secondApp second
  -- This requirement is intentionally actual-independent. The test does NOT
  -- claim substitution of E into dependent requirements.

requirementTarget :: Result ()
requirementTarget = do
  (source, application) <- applicationFor templateText Set.empty
  let run key iface = grammarV1CheckedStrictSpecializedGenericDischarge
        emptyStaticContext emptySurfaceState [] [] definition application
        (GrammarV1ResolvedGenericRequirementSet key iface (grammarV1FunctionRequirements source)) []
      otherKey = DeclarationKey "audit.other.Worker"
      otherInterface = InterfaceRevision "audit.other.interface"
  exact (Just (Left (GrammarV1GenericRequirementTargetMismatch root revision otherKey revision)))
    (run otherKey revision)
  exact (Just (Left (GrammarV1GenericRequirementTargetMismatch root revision root otherInterface)))
    (run root otherInterface)

requirementOccurrences :: Result ()
requirementOccurrences = do
  (source, application) <- applicationFor templateText Set.empty
  shifted <- parseFunction ("\n" <> templateText)
  case (grammarV1FunctionRequirements source, grammarV1FunctionRequirements shifted) of
    ([original], [differentOccurrence]) -> do
      exact (locatedValue original) (locatedValue differentOccurrence)
      assertion (original /= differentOccurrence) "fixture did not move the located source occurrence"
      let make requirement = GrammarV1ResolvedRequirementDisposition requirement
            (GenericSatisfiedByEvidence (GenericEvidence { genericEvidenceProposition = Truth, genericEvidenceIdentity = "audit.supplied.closed-truth" }))
          run values = grammarV1CheckedStrictSpecializedGenericDischarge
            emptyStaticContext emptySurfaceState [] [] definition application
            (GrammarV1ResolvedGenericRequirementSet root revision [original]) values
      exact (Just (Left (GrammarV1MissingRequirementDisposition original))) (run [])
      exact (Just (Left (GrammarV1DuplicateRequirementDisposition original)))
        (run [make original, make original])
      exact (Just (Left (GrammarV1UnexpectedRequirementDisposition differentOccurrence)))
        (run [make differentOccurrence])
    result -> Left (Harness ("expected one source requirement each: " <> show result))

unsupportedRequirement :: Result ()
unsupportedRequirement = do
  (source, application) <- applicationFor
    "fn Worker[E : Effects] requires { callable F : C; }() -> Unit satisfies C { return unit; }"
    Set.empty
  exact Nothing $ grammarV1CheckedStrictSpecializedGenericDischarge
    emptyStaticContext emptySurfaceState [] [] definition application
    (GrammarV1ResolvedGenericRequirementSet root revision (grammarV1FunctionRequirements source)) []

headerFor :: GrammarV1FunctionDecl -> Result GrammarV1CheckedFunctionHeader
headerFor = fixture . Function.checkedHeader root definition

associatedBody :: Result ()
associatedBody = mapM_ check
  [ ("fn value() -> Bool satisfies C { return true; }", TyBool)
  , ("fn value() -> Bool satisfies C { return false; }", TyBool)
  , ("fn value() -> Unit satisfies C { return (unit); }", TyUnit) ]
  where
    check (text, ty) = do
      source <- parseFunction text
      header <- headerFor source
      result <- competent (grammarV1CheckedClosedFunctionBody emptyStaticContext header source)
      exact header (checkedClosedFunctionBodyHeader result)
      exact [Return ty] (checkedClosedFunctionBodyControls result)

foreignHeader :: Result ()
foreignHeader = do
  first <- parseFunction "fn first() -> Bool satisfies C { return true; }"
  second <- parseFunction "fn second() -> Bool satisfies C { return true; }"
  h1 <- headerFor first
  h2 <- headerFor second
  _ <- competent (grammarV1CheckedClosedFunctionBody emptyStaticContext h1 first)
  _ <- competent (grammarV1CheckedClosedFunctionBody emptyStaticContext h2 second)
  exact (Just (Left (GrammarV1FunctionBodyHeaderMismatch h1 h2)))
    (grammarV1CheckedClosedFunctionBody emptyStaticContext h1 second)

wrongReturn :: Result ()
wrongReturn = do
  source <- parseFunction "fn mismatch() -> U32 satisfies C { return true; }"
  header <- headerFor source
  exact (Just (Left (GrammarV1FunctionBodyResultMismatch (TyUInt 32) [Return TyBool])))
    (grammarV1CheckedClosedFunctionBody emptyStaticContext header source)

returnDiscipline :: Result ()
returnDiscipline = do
  missing <- parseFunction "fn missing() -> Bool satisfies C { unit; }"
  after <- parseFunction "fn after() -> Bool satisfies C { return true; unit; }"
  missingHeader <- headerFor missing
  afterHeader <- headerFor after
  exact (Just (Left (GrammarV1FunctionBodyResultMismatch TyBool [Continue])))
    (grammarV1CheckedClosedFunctionBody emptyStaticContext missingHeader missing)
  case grammarV1CheckedClosedFunctionBody emptyStaticContext afterHeader after of
    Just (Left (GrammarV1FunctionBodySurfaceCheckError err)) -> exact ControlAfterTerminal (surfaceErrorClass err)
    other -> Left (Requirement ("wrong terminal-sequencing disposition: " <> show other))

bodyBoundary :: Result ()
bodyBoundary = do
  mapM_ check
    [ "fn parameterized(x : Bool) -> Bool satisfies C { return true; }"
    , "fn integerLiteral() -> U32 satisfies C { return 1; }"
    , "fn namedBody() -> Bool satisfies C { return missing; }" ]
  generic <- parseFunction "fn generic[T : Type]() -> Bool satisfies C { return true; }"
  exact Nothing (grammarV1CheckedClosedFunctionHeader emptyStaticContext root definition generic)
  where
    check text = do
      source <- parseFunction text
      header <- headerFor source
      exact Nothing (grammarV1CheckedClosedFunctionBody emptyStaticContext header source)

baseCatalog :: Result (CheckedSourceBundle, CallableInvocationCatalog, ResolvedCallableInvocation)
baseCatalog = do
  (checked, contracts) <- fixture Catalog.baseChecked
  catalog <- accepted (buildCallableInvocationCatalog Set.empty contracts checked)
  resolved <- accepted (resolveCallableInvocation catalog "Worker" Catalog.workerExpectation)
  pure (checked, catalog, resolved)

catalogRetention :: Result ()
catalogRetention = do
  (checked, _, resolved) <- baseCatalog
  let binding = resolvedCallableBinding resolved
      units = [u | u <- checkedSourceUnits checked, checkedSourceDeclarationKey u == Catalog.workerKey]
  exact Catalog.workerKey (sourceCallableDeclarationKey binding)
  exact Catalog.workerContract (sourceCallableContract binding)
  case units of
    [unit] -> do
      exact "Worker" (componentName (locatedValue (checkedSourceComponent unit)))
      exact [] (componentParameters (locatedValue (checkedSourceComponent unit)))
      exact [Return TyUnit] (checkedTerminalControls (checkedSourceResult unit))
    _ -> Left (Harness "expected exactly one genuine checked worker unit")

catalogRename :: Result ()
catalogRename = do
  checked <- fixture $ Catalog.checkedBundle
    [ (Catalog.callerKey, "unit.caller", "site.caller", "Caller")
    , (Catalog.workerKey, "unit.renamed", "site.renamed", "RenamedWorker") ]
  let contracts = Map.fromList [(Catalog.callerKey, Catalog.callerContract), (Catalog.workerKey, Catalog.workerContract)]
  catalog <- accepted (buildCallableInvocationCatalog Set.empty contracts checked)
  resolved <- accepted (resolveCallableInvocation catalog "RenamedWorker" Catalog.workerExpectation)
  exact Catalog.workerKey (sourceCallableDeclarationKey (resolvedCallableBinding resolved))
  case resolveCallableInvocation catalog "Worker" Catalog.workerExpectation of
    Left (CallableNameUnknown "Worker") -> Right ()
    other -> Left (Requirement ("old display spelling remained a locator: " <> show other))

catalogAmbiguity :: Result ()
catalogAmbiguity = do
  checked <- fixture $ Catalog.checkedBundle
    [ (Catalog.callerKey, "unit.caller", "site.caller", "Caller")
    , (Catalog.workerKey, "unit.a", "site.a", "Worker")
    , (Catalog.workerOtherKey, "unit.b", "site.b", "Worker") ]
  catalog <- accepted $ buildCallableInvocationCatalog Set.empty
    (Map.fromList [(Catalog.callerKey,Catalog.callerContract), (Catalog.workerKey,Catalog.workerContract),
                  (Catalog.workerOtherKey,Catalog.workerContract)]) checked
  case resolveCallableInvocation catalog "Worker" Catalog.workerExpectation of
    Left (CallableNameAmbiguous "Worker" keys) -> exact (Set.fromList [Catalog.workerKey,Catalog.workerOtherKey]) (Set.fromList keys)
    result -> Left (Requirement ("expected duplicate display ambiguity: " <> show result))

catalogDomain :: Result ()
catalogDomain = do
  (checked, contracts) <- fixture Catalog.baseChecked
  case buildCallableInvocationCatalog Set.empty (Map.delete Catalog.workerKey contracts) checked of
    Left (CallableContractMissing key) -> exact Catalog.workerKey key
    result -> Left (Requirement ("missing contract did not reject: " <> show result))
  let outside = DeclarationKey "audit.outside"
  case buildCallableInvocationCatalog Set.empty (Map.insert outside Catalog.workerContract contracts) checked of
    Left (CallableContractOutsideBundle key) -> exact outside key
    result -> Left (Requirement ("outside contract did not reject: " <> show result))

catalogNominal :: Result ()
catalogNominal = do
  (_, catalog, _) <- baseCatalog
  let different = DeclarationKey "audit.different"
  case resolveCallableInvocation catalog "Worker" (CallableInvocationExpectation different Catalog.workerContract) of
    Left (CallableDeclarationIdentityMismatch "Worker" expected actual) -> do
      exact different expected
      exact Catalog.workerKey actual
    result -> Left (Requirement ("wrong nominal identity disposition: " <> show result))
  case resolveCallableInvocation catalog "Worker" (CallableInvocationExpectation Catalog.workerKey Catalog.callerContract) of
    Left (CallableInterfaceRevisionMismatch "Worker" expected actual) -> do
      exact (InterfaceRevision "caller.v1") expected
      exact (InterfaceRevision "worker.v1") actual
    result -> Left (Requirement ("wrong interface disposition: " <> show result))

-- Narrow audit adapter: only a genuine zero-parameter, Unit-return source unit
-- paired with the successfully resolved fixture contract is translated. The
-- library does not export this adapter. No machine-shape string is parsed as Ty.
auditUnitEnvironment :: CheckedSourceBundle -> ResolvedCallableInvocation -> Result SurfaceEnvironment
auditUnitEnvironment checked resolved = do
  let binding = resolvedCallableBinding resolved
      key = sourceCallableDeclarationKey binding
  case [u | u <- checkedSourceUnits checked, checkedSourceDeclarationKey u == key] of
    [unit] -> do
      exact [] (componentParameters (locatedValue (checkedSourceComponent unit)))
      exact [Return TyUnit] (checkedTerminalControls (checkedSourceResult unit))
      pure $ (emptySurfaceEnvironment emptyStaticContext)
        { surfaceCallables = Map.singleton (sourceCallableDisplayName binding)
            (SurfaceCallableSignature key [] Nothing) }
    _ -> Left (Harness "audit adapter requires exactly one matching checked unit")

actualCallerComposition :: Result ()
actualCallerComposition = do
  (checked, _, resolved) <- baseCatalog
  environment <- auditUnitEnvironment checked resolved
  component <- parseComponent "component Caller { invoke Worker() invoke Worker() return unit }"
  let binding = resolvedCallableBinding resolved
      contracts = Map.singleton (sourceCallableDeclarationKey binding) (sourceCallableContract binding)
  enriched <- accepted (checkSurfaceComponentWithCallableSemantics contracts environment component)
  exact [Return TyUnit] (checkedTerminalControls (checkedSurfaceResult enriched))
  case checkedCallableInvocations enriched of
    [first, second] -> do
      exact Catalog.workerKey (surfaceInvocationDeclarationKey first)
      exact Catalog.workerKey (surfaceInvocationDeclarationKey second)
      exact (sourceCallableContract binding) (surfaceInvocationSemanticContract first)
      exact (sourceCallableContract binding) (surfaceInvocationSemanticContract second)
      assertion (surfaceInvocationSpan first /= surfaceInvocationSpan second) "two source occurrences collapsed"
    other -> Left (Requirement ("expected two real invocation witnesses: " <> show other))
  context <- accepted $ checkSurfaceComponentWithInvocationContext contracts
    (SurfaceCallableCallerContext Set.empty Catalog.callerInterface) environment component
  exact (summarizeSurfaceCallableSemantics enriched) (checkedInvocationSemanticSummary context)

callerDomain :: Result ()
callerDomain = do
  (checked, _, resolved) <- baseCatalog
  environment <- auditUnitEnvironment checked resolved
  component <- parseComponent "component Caller { invoke Worker() return unit }"
  _ <- accepted (checkSurfaceComponent environment component)
  case checkSurfaceComponentWithCallableSemantics Map.empty environment component of
    Left err -> exact UnknownCallable (surfaceErrorClass err)
    result -> Left (Requirement ("missing used semantic contract did not reject: " <> show result))
  let binding = resolvedCallableBinding resolved
      contracts = Map.singleton (sourceCallableDeclarationKey binding) (sourceCallableContract binding)
      extended = Map.insert (DeclarationKey "audit.unused") Catalog.callerContract contracts
  first <- accepted (checkSurfaceComponentWithCallableSemantics contracts environment component)
  second <- accepted (checkSurfaceComponentWithCallableSemantics extended environment component)
  exact first second
  -- Enrichment requires contracts for actually used calls; catalog construction
  -- has a different, closed checked-bundle domain. Neither domain is enlarged
  -- into the other one's claim by this test.

cases :: [(String, Result ())]
cases =
  [ ("G01",binderIdentity), ("G02",binderDuplicate), ("G03",sourceActual), ("G04",sourceReferenceGuards)
  , ("D01",closedRequirementLineage), ("D02",requirementTarget), ("D03",requirementOccurrences), ("D04",unsupportedRequirement)
  , ("F01",associatedBody), ("F02",foreignHeader), ("F03",wrongReturn), ("F04",returnDiscipline), ("F05",bodyBoundary)
  , ("N01",catalogRetention), ("N02",catalogRename), ("N03",catalogAmbiguity), ("N04",catalogDomain), ("N05",catalogNominal)
  , ("A01",actualCallerComposition), ("A02",callerDomain) ]

main :: IO ()
main = do
  codes <- mapM runCase cases
  putStrLn ("COMPLETE source_connection_groups=" <> show (length cases))
  let code | 2 `elem` codes = 2
           | 1 `elem` codes = 1
           | otherwise = 0
  unless (code == 0) (exitWith (ExitFailure code))
  where
    runCase (key, action) = do
      outcome <- try (evaluate action) :: IO (Either SomeException (Result ()))
      case outcome of
        Left err -> putStrLn ("CASE " <> key <> " HARNESS " <> show err) >> pure (2 :: Int)
        Right (Left (Harness reason)) -> putStrLn ("CASE " <> key <> " HARNESS " <> show reason) >> pure 2
        Right (Left (Requirement reason)) -> putStrLn ("CASE " <> key <> " FAIL " <> show reason) >> pure 1
        Right (Right ()) -> putStrLn ("CASE " <> key <> " PASS") >> pure 0
