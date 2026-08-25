{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.ProviderQualification
import Phil.Core.Static (DefinitionRevision (..), InterfaceRevision (..))
import Phil.Core.Syntax (Outcome (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-001 stateless pure Phil semantic qualification closes" validQualificationAccepts
    , test "PROV-002 missing public operation mapping rejects" missingOperationMappingRejects
    , test "PROV-002 matching symbols do not infer correspondence" symbolInferenceRejects
    , test "PROV-002 unexpected operation correspondence rejects" unexpectedOperationMappingRejects
    , test "PROV-002 unknown implementation entry rejects" unknownEntryRejects
    , test "PROV-003 stronger implementation precondition rejects" strongerPreconditionRejects
    , test "PROV-003 stronger caller authority rejects" strongerAuthorityRejects
    , test "PROV-004 narrower effect and failure implementation accepts" narrowerImplementationAccepts
    , test "PROV-004 wider effect rejects" widerEffectRejects
    , test "PROV-004 undeclared fatal outcome rejects" fatalOutcomeRejects
    , test "PROV-005 missing outcome correspondence rejects" missingOutcomeMappingRejects
    , test "PROV-005 unknown public outcome rejects" unknownPublicOutcomeRejects
    , test "PROV-005 resource residue mismatch rejects" resourceResidueMismatchRejects
    , test "provider contract revision is exact" contractRevisionMismatchRejects
    , test "provider implementation revision is exact" implementationRevisionMismatchRejects
    , test "operation correspondence ordering is canonical" correspondenceOrderingIsCanonical
    , test "implementation symbol set is nonsemantic" symbolsAreNonsemantic
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validQualificationAccepts :: Either String ()
validQualificationAccepts = do
  checked <- mapLeft show $ checkProviderSemanticQualification
    providerContract providerImplementation validClaim
  assert (Map.keysSet (checkedProviderOperations checked) == Set.fromList [readOperation, installOperation])
    "checked provider operation domain changed"

missingOperationMappingRejects :: Either String ()
missingOperationMappingRejects =
  let claim = validClaim
        { providerQualificationOperationCorrespondences = Map.delete installOperation validCorrespondences }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationMissingOperationCorrespondences missing) ->
      assert (missing == Set.singleton installOperation) "wrong missing operation"
    other -> Left ("missing operation mapping did not reject: " <> show other)

symbolInferenceRejects :: Either String ()
symbolInferenceRejects =
  let claim = validClaim { providerQualificationOperationCorrespondences = Map.empty }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationMissingOperationCorrespondences missing) ->
      assert (missing == Set.fromList [readOperation, installOperation])
        "matching symbols influenced semantic operation mapping"
    other -> Left ("symbols inferred semantic correspondence: " <> show other)

unexpectedOperationMappingRejects :: Either String ()
unexpectedOperationMappingRejects =
  let extra = ProviderOperationKey "delete"
      claim = validClaim
        { providerQualificationOperationCorrespondences =
            Map.insert extra readCorrespondence validCorrespondences }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationUnexpectedOperationCorrespondences unexpected) ->
      assert (unexpected == Set.singleton extra) "wrong unexpected operation"
    other -> Left ("unexpected operation mapping did not reject: " <> show other)

unknownEntryRejects :: Either String ()
unknownEntryRejects =
  let missingEntry = ProviderImplementationEntryKey "impl.missing"
      bad = readCorrespondence { providerCorrespondenceImplementationEntry = missingEntry }
      claim = validClaim
        { providerQualificationOperationCorrespondences = Map.insert readOperation bad validCorrespondences }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationUnknownImplementationEntry operation entry) -> do
      assert (operation == readOperation) "wrong operation in missing-entry error"
      assert (entry == missingEntry) "wrong missing implementation entry"
    other -> Left ("unknown implementation entry did not reject: " <> show other)

strongerPreconditionRejects :: Either String ()
strongerPreconditionRejects =
  let extra = ProviderPreconditionKey "caller.has-secret-token"
      readImpl = providerImplementationEntries providerImplementation Map.! readEntry
      implementation = providerImplementation
        { providerImplementationEntries = Map.insert readEntry
            (readImpl { providerImplementationPreconditions = Set.singleton extra })
            (providerImplementationEntries providerImplementation)
        }
  in case checkProviderSemanticQualification providerContract implementation validClaim of
    Left (ProviderQualificationStrongerPreconditions operation excess) -> do
      assert (operation == readOperation) "wrong operation for stronger precondition"
      assert (excess == Set.singleton extra) "wrong excess precondition"
    other -> Left ("stronger implementation precondition did not reject: " <> show other)

strongerAuthorityRejects :: Either String ()
strongerAuthorityRejects =
  let deleteAuthority = CallableAuthorityRequirement "storage.delete"
      readImpl = providerImplementationEntries providerImplementation Map.! readEntry
      surface = providerImplementationCallable readImpl
      stronger = surface
        { callableRefinementCallerAuthority = Set.insert deleteAuthority
            (callableRefinementCallerAuthority surface) }
      implementation = providerImplementation
        { providerImplementationEntries = Map.insert readEntry
            (readImpl { providerImplementationCallable = stronger })
            (providerImplementationEntries providerImplementation)
        }
  in case checkProviderSemanticQualification providerContract implementation validClaim of
    Left (ProviderQualificationCallableRefinementFailed operation
        (CallableAuthorityRequirementTooStrong excess)) -> do
      assert (operation == readOperation) "wrong operation for stronger authority"
      assert (excess == Set.singleton deleteAuthority) "wrong excess authority"
    other -> Left ("stronger caller authority did not reject: " <> show other)

narrowerImplementationAccepts :: Either String ()
narrowerImplementationAccepts =
  let readImpl = providerImplementationEntries providerImplementation Map.! readEntry
      surface = providerImplementationCallable readImpl
      narrowerContract = (callableRefinementContract surface)
        { callableContractEffectBound = Set.empty }
      narrower = surface
        { callableRefinementContract = narrowerContract
        , callableRefinementFailures = Set.empty
        }
      implementation = providerImplementation
        { providerImplementationEntries = Map.insert readEntry
            (readImpl { providerImplementationCallable = narrower })
            (providerImplementationEntries providerImplementation)
        }
  in mapLeft show $ checkProviderSemanticQualification providerContract implementation validClaim >> Right ()

widerEffectRejects :: Either String ()
widerEffectRejects =
  let writeEffect = SemanticEffect "write"
      readImpl = providerImplementationEntries providerImplementation Map.! readEntry
      surface = providerImplementationCallable readImpl
      widerContract = (callableRefinementContract surface)
        { callableContractEffectBound = Set.fromList [readEffect, writeEffect] }
      implementation = providerImplementation
        { providerImplementationEntries = Map.insert readEntry
            (readImpl { providerImplementationCallable = surface { callableRefinementContract = widerContract } })
            (providerImplementationEntries providerImplementation)
        }
  in case checkProviderSemanticQualification providerContract implementation validClaim of
    Left (ProviderQualificationCallableRefinementFailed operation (CallableEffectBoundTooWide excess)) -> do
      assert (operation == readOperation) "wrong operation for wider effect"
      assert (excess == Set.singleton writeEffect) "wrong excess effect"
    other -> Left ("wider provider effect did not reject: " <> show other)

fatalOutcomeRejects :: Either String ()
fatalOutcomeRejects =
  let fatal = CallableFatal "abort"
      readImpl = providerImplementationEntries providerImplementation Map.! readEntry
      surface = providerImplementationCallable readImpl
      implementation = providerImplementation
        { providerImplementationEntries = Map.insert readEntry
            (readImpl { providerImplementationCallable = surface
              { callableRefinementFailures = Set.insert fatal (callableRefinementFailures surface) } })
            (providerImplementationEntries providerImplementation)
        }
  in case checkProviderSemanticQualification providerContract implementation validClaim of
    Left (ProviderQualificationCallableRefinementFailed operation (CallableFailureSetTooWide excess)) -> do
      assert (operation == readOperation) "wrong operation for fatal outcome"
      assert (excess == Set.singleton fatal) "wrong excess failure"
    other -> Left ("undeclared fatal provider outcome did not reject: " <> show other)

missingOutcomeMappingRejects :: Either String ()
missingOutcomeMappingRejects =
  let bad = readCorrespondence
        { providerCorrespondenceOutcomes = Map.delete readNotFoundOutcome
            (providerCorrespondenceOutcomes readCorrespondence) }
      claim = validClaim
        { providerQualificationOperationCorrespondences = Map.insert readOperation bad validCorrespondences }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationMissingOutcomeCorrespondences operation missing) -> do
      assert (operation == readOperation) "wrong operation for missing outcome mapping"
      assert (missing == Set.singleton readNotFoundOutcome) "wrong missing implementation outcome"
    other -> Left ("missing outcome correspondence did not reject: " <> show other)

unknownPublicOutcomeRejects :: Either String ()
unknownPublicOutcomeRejects =
  let unknown = ProviderOutcomeKey "contract.read.mystery"
      bad = readCorrespondence
        { providerCorrespondenceOutcomes = Map.insert readSuccessOutcome unknown
            (providerCorrespondenceOutcomes readCorrespondence) }
      claim = validClaim
        { providerQualificationOperationCorrespondences = Map.insert readOperation bad validCorrespondences }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationUnknownContractOutcome operation implementationOutcome contractOutcome) -> do
      assert (operation == readOperation) "wrong operation for unknown public outcome"
      assert (implementationOutcome == readSuccessOutcome) "wrong implementation outcome"
      assert (contractOutcome == unknown) "wrong unknown contract outcome"
    other -> Left ("unknown public outcome did not reject: " <> show other)

resourceResidueMismatchRejects :: Either String ()
resourceResidueMismatchRejects =
  let readImpl = providerImplementationEntries providerImplementation Map.! readEntry
      badResidue = readSuccessResidue
        { providerResidueConsumedInputs = Set.singleton requestResource }
      implementation = providerImplementation
        { providerImplementationEntries = Map.insert readEntry
            (readImpl { providerImplementationOutcomeResidues = Map.insert readSuccessOutcome badResidue
              (providerImplementationOutcomeResidues readImpl) })
            (providerImplementationEntries providerImplementation)
        }
  in case checkProviderSemanticQualification providerContract implementation validClaim of
    Left (ProviderQualificationResourceResidueMismatch operation implementationOutcome contractOutcome expected actual) -> do
      assert (operation == readOperation) "wrong operation for residue mismatch"
      assert (implementationOutcome == readSuccessOutcome) "wrong implementation outcome for residue mismatch"
      assert (contractOutcome == contractReadSuccessOutcome) "wrong contract outcome for residue mismatch"
      assert (expected == readSuccessResidue) "wrong expected residue"
      assert (actual == badResidue) "wrong actual residue"
    other -> Left ("resource residue mismatch did not reject: " <> show other)

contractRevisionMismatchRejects :: Either String ()
contractRevisionMismatchRejects =
  let wrong = InterfaceRevision "provider.other.v1"
      claim = validClaim { providerQualificationRequiredInterface = wrong }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationContractRevisionMismatch expected actual) -> do
      assert (expected == providerRevision) "wrong expected provider revision"
      assert (actual == wrong) "wrong actual provider revision"
    other -> Left ("provider contract revision mismatch did not reject: " <> show other)

implementationRevisionMismatchRejects :: Either String ()
implementationRevisionMismatchRejects =
  let wrong = DefinitionRevision "provider.impl.other"
      claim = validClaim { providerQualificationImplementationRevision = wrong }
  in case checkProviderSemanticQualification providerContract providerImplementation claim of
    Left (ProviderQualificationImplementationRevisionMismatch expected actual) -> do
      assert (expected == implementationRevision) "wrong expected implementation revision"
      assert (actual == wrong) "wrong actual implementation revision"
    other -> Left ("implementation revision mismatch did not reject: " <> show other)

correspondenceOrderingIsCanonical :: Either String ()
correspondenceOrderingIsCanonical =
  let left = Map.fromList [(readOperation, readCorrespondence), (installOperation, installCorrespondence)]
      right = Map.fromList [(installOperation, installCorrespondence), (readOperation, readCorrespondence)]
      check mappings = checkProviderSemanticQualification providerContract providerImplementation
        (validClaim { providerQualificationOperationCorrespondences = mappings })
  in assert (check left == check right) "operation mapping enumeration order changed qualification"

symbolsAreNonsemantic :: Either String ()
symbolsAreNonsemantic =
  let renamed = providerImplementation
        { providerImplementationSymbols = Set.fromList ["totally_different_a", "totally_different_b"] }
  in assert
      (checkProviderSemanticQualification providerContract providerImplementation validClaim
        == checkProviderSemanticQualification providerContract renamed validClaim)
      "implementation symbols changed semantic qualification"

providerRevision :: InterfaceRevision
providerRevision = InterfaceRevision "provider.blob.v1"

implementationRevision :: DefinitionRevision
implementationRevision = DefinitionRevision "provider.blob.impl.v7"

readOperation, installOperation :: ProviderOperationKey
readOperation = ProviderOperationKey "read"
installOperation = ProviderOperationKey "installIfAbsent"

readEntry, installEntry :: ProviderImplementationEntryKey
readEntry = ProviderImplementationEntryKey "impl.read"
installEntry = ProviderImplementationEntryKey "impl.install"

readEffect, installEffect :: SemanticEffect
readEffect = SemanticEffect "read"
installEffect = SemanticEffect "install-if-absent"

readAuthority, installAuthority :: CallableAuthorityRequirement
readAuthority = CallableAuthorityRequirement "storage.read"
installAuthority = CallableAuthorityRequirement "storage.install-if-absent"

notFoundFailure, alreadyExistsFailure :: CallableFailure
notFoundFailure = CallableTypedNegative (Outcome "not-found")
alreadyExistsFailure = CallableTypedNegative (Outcome "already-exists")

readShape, installShape :: CallableMachineShape
readShape = CallableMachineShape "read(id)->bytes"
installShape = CallableMachineShape "install(id,bytes)->status"

surface :: InterfaceRevision -> CallableMachineShape -> SemanticEffect -> CallableAuthorityRequirement -> Set.Set CallableFailure -> CallableRefinementSurface
surface revision shape effect authority failures = CallableRefinementSurface
  { callableRefinementMachineShape = shape
  , callableRefinementContract = CallableContract revision PreserveCallee (Set.singleton effect)
  , callableRefinementCallerAuthority = Set.singleton authority
  , callableRefinementFailures = failures
  }

contractReadSurface, implementationReadSurface, contractInstallSurface, implementationInstallSurface :: CallableRefinementSurface
contractReadSurface = surface (InterfaceRevision "provider.blob.read.v1") readShape readEffect readAuthority (Set.singleton notFoundFailure)
implementationReadSurface = surface (InterfaceRevision "impl.blob.read.v7") readShape readEffect readAuthority (Set.singleton notFoundFailure)
contractInstallSurface = surface (InterfaceRevision "provider.blob.install.v1") installShape installEffect installAuthority (Set.singleton alreadyExistsFailure)
implementationInstallSurface = surface (InterfaceRevision "impl.blob.install.v7") installShape installEffect installAuthority (Set.singleton alreadyExistsFailure)

requestResource, ownerResource, successorResource :: ProviderResourceKey
requestResource = ProviderResourceKey "request"
ownerResource = ProviderResourceKey "owner"
successorResource = ProviderResourceKey "successor"

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue Set.empty Set.empty Set.empty Set.empty Set.empty

readSuccessResidue, readNotFoundResidue, installSuccessResidue, installExistsResidue :: ProviderResourceResidue
readSuccessResidue = emptyResidue { providerResidueBorrowedInputs = Set.singleton requestResource, providerResidueProducedResources = Set.singleton ownerResource }
readNotFoundResidue = emptyResidue { providerResidueBorrowedInputs = Set.singleton requestResource }
installSuccessResidue = emptyResidue { providerResidueConsumedInputs = Set.singleton ownerResource, providerResidueSuccessors = Set.singleton successorResource }
installExistsResidue = emptyResidue { providerResidueReturnedPredecessors = Set.singleton ownerResource }

contractReadSuccessOutcome, contractReadNotFoundOutcome, contractInstallSuccessOutcome, contractInstallExistsOutcome :: ProviderOutcomeKey
contractReadSuccessOutcome = ProviderOutcomeKey "contract.read.success"
contractReadNotFoundOutcome = ProviderOutcomeKey "contract.read.not-found"
contractInstallSuccessOutcome = ProviderOutcomeKey "contract.install.success"
contractInstallExistsOutcome = ProviderOutcomeKey "contract.install.already-exists"

readSuccessOutcome, readNotFoundOutcome, installSuccessOutcome, installExistsOutcome :: ProviderOutcomeKey
readSuccessOutcome = ProviderOutcomeKey "impl.read.ok"
readNotFoundOutcome = ProviderOutcomeKey "impl.read.miss"
installSuccessOutcome = ProviderOutcomeKey "impl.install.ok"
installExistsOutcome = ProviderOutcomeKey "impl.install.exists"

providerContract :: ProviderContract
providerContract = ProviderContract providerRevision (Map.fromList
  [ (readOperation, ProviderOperationContract contractReadSurface Set.empty (Map.fromList
      [ (contractReadSuccessOutcome, readSuccessResidue)
      , (contractReadNotFoundOutcome, readNotFoundResidue)
      ]))
  , (installOperation, ProviderOperationContract contractInstallSurface Set.empty (Map.fromList
      [ (contractInstallSuccessOutcome, installSuccessResidue)
      , (contractInstallExistsOutcome, installExistsResidue)
      ]))
  ])

providerImplementation :: ProviderImplementation
providerImplementation = ProviderImplementation implementationRevision (Map.fromList
  [ (readEntry, ProviderImplementationOperation implementationReadSurface Set.empty (Map.fromList
      [ (readSuccessOutcome, readSuccessResidue)
      , (readNotFoundOutcome, readNotFoundResidue)
      ]))
  , (installEntry, ProviderImplementationOperation implementationInstallSurface Set.empty (Map.fromList
      [ (installSuccessOutcome, installSuccessResidue)
      , (installExistsOutcome, installExistsResidue)
      ]))
  ]) (Set.fromList ["read", "installIfAbsent"])

readCorrespondence, installCorrespondence :: ProviderOperationCorrespondence
readCorrespondence = ProviderOperationCorrespondence readEntry (Map.fromList
  [ (readSuccessOutcome, contractReadSuccessOutcome)
  , (readNotFoundOutcome, contractReadNotFoundOutcome)
  ])
installCorrespondence = ProviderOperationCorrespondence installEntry (Map.fromList
  [ (installSuccessOutcome, contractInstallSuccessOutcome)
  , (installExistsOutcome, contractInstallExistsOutcome)
  ])

validCorrespondences :: Map.Map ProviderOperationKey ProviderOperationCorrespondence
validCorrespondences = Map.fromList
  [ (readOperation, readCorrespondence)
  , (installOperation, installCorrespondence)
  ]

validClaim :: ProviderQualificationClaim
validClaim = ProviderQualificationClaim providerRevision implementationRevision validCorrespondences

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
