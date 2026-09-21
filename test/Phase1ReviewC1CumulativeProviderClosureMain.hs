{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.ProviderQualification (ProviderOperationKey (..))
import Phil.Examples.Phase1.ProviderCallWitnesses
  ( steveProviderCallExpectations
  , uploadProviderCallExpectations
  )
import Phil.Examples.Phase1.StageClosureWitnesses
  ( steveStageClosureBundle
  , uploadStageClosureBundle
  )
import Phil.Systems.AuthorityEffectCorrespondence
import Phil.Systems.BoundaryCommitCorrespondence
import Phil.Systems.BranchResourceFailure
import Phil.Systems.ControlStateProjection
import Phil.Systems.Phase1Stage (SystemsMechanismKey)
import Phil.Systems.ProtocolStateCorrespondence
import Phil.Systems.ProviderCallCorrespondence
import Phil.Systems.StageClosure
import Phil.Systems.SubjectCorrespondence (SubjectStageBundle (subjectStageRevision))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "C1 genuine Steve closes through the branch route" steveAccepted
    , test "C1 genuine Upload closes through the boundary route" uploadAccepted
    , test "C1 authority construction rejects coordinated provider omission" authorityConstructionRejects
    , test "C1 BranchResource rejects coordinated site/link/use deletion" branchOmissionRejects
    , test "C1 final Steve closure rejects one omitted provider call"
        (closureOmissionRejects steveStageClosureBundle steveProviderCallExpectations False)
    , test "C1 final Steve closure rejects complete provider-call erasure"
        (closureOmissionRejects steveStageClosureBundle steveProviderCallExpectations True)
    , test "C1 final Upload boundary closure rejects provider-call erasure"
        (closureOmissionRejects uploadStageClosureBundle uploadProviderCallExpectations True)
    , test "C1 final closure rejects a wrong genuine provider operation" wrongOperationRejects
    , test "C1 final closure retains R19 qualified-entry rejection" wrongEntryRejects
    , test "C1 Steve cannot use Upload's genuine provider authority"
        (donorAuthorityRejects steveStageClosureBundle uploadStageClosureBundle)
    , test "C1 Upload cannot use Steve's genuine provider authority"
        (donorAuthorityRejects uploadStageClosureBundle steveStageClosureBundle)
    , test "C1 independent authority is invariant under expectation map order" authorityOrderIndependent
    , test "C1 restoring the genuine provider stage restores exact closure" restorationAccepted
    , test "C1 both final canonical identities retain their provider authority" canonicalAuthorityRetained
    ]
  if and results then pure () else exitFailure

steveAccepted :: Either String ()
steveAccepted = do
  bundle <- steveStageClosureBundle
  case stageClosureConcrete bundle of
    ConcreteThroughBranch _ -> mapLeft show $ verifyStageClosureBundle bundle
    _ -> Left "Steve fixture no longer exercises the branch closure route"

uploadAccepted :: Either String ()
uploadAccepted = do
  bundle <- uploadStageClosureBundle
  case stageClosureConcrete bundle of
    ConcreteThroughBoundary _ -> mapLeft show $ verifyStageClosureBundle bundle
    _ -> Left "Upload fixture no longer exercises the boundary closure route"

authorityConstructionRejects :: Either String ()
authorityConstructionRejects = do
  original <- steveStageClosureBundle
  (mutated, expectedError) <- prepareOmission original steveProviderCallExpectations False
  assertLeft expectedError $ certifyProviderCallClosureAuthority
    steveProviderCallExpectations (branchResourceStageBase (closureBranch mutated))

branchOmissionRejects :: Either String ()
branchOmissionRejects = do
  original <- steveStageClosureBundle
  (mutated, expectedError) <- prepareOmission original steveProviderCallExpectations False
  assertLeft (BranchResourceBaseStageError expectedError) $
    verifyBranchResourceStageBundle (closureBranch mutated)

closureOmissionRejects
  :: Either String StageClosureBundle
  -> ProviderCallExpectationMap
  -> Bool
  -> Either String ()
closureOmissionRejects fixture expectations eraseAll = do
  original <- fixture
  (mutated, expectedError) <- prepareOmission original expectations eraseAll
  expectClosureBranchError mutated (BranchResourceBaseStageError expectedError)

prepareOmission
  :: StageClosureBundle
  -> ProviderCallExpectationMap
  -> Bool
  -> Either String (StageClosureBundle, AuthorityEffectStageVerificationError)
prepareOmission original expectations eraseAll = do
  mapLeft show $ verifyStageClosureBundle original
  firstSite <- case Map.lookupMin expectations of
    Just (site, _) -> Right site
    Nothing -> Left "omission fixture has no independent required provider calls"
  let required = Map.keysSet expectations
      removed = if eraseAll then required else Set.singleton firstSite
      originalAuthority = branchResourceStageBase (closureBranch original)
      originalProvider = authorityEffectStageBase originalAuthority
      changedAuthority = dropSites removed originalAuthority
      mutated = mapClosureBranch (replaceAuthority changedAuthority) original
      changedProvider = authorityEffectStageBase changedAuthority
      expectedError = AuthorityEffectBaseStageError
        (ProviderCallRequiredSiteDomainMismatch required (required Set.\\ removed))
  assert (providerCallStageCallSites originalProvider == required)
    "baseline candidate does not match independent required inventory"
  assert (providerCallStageCallSites changedProvider == required Set.\\ removed)
    "candidate omitted the wrong call inventory"
  assert (providerCallStageSelections changedProvider == providerCallStageSelections originalProvider)
    "omission changed selected admissions or implementation entries"
  assert (authorityEffectStageSurfaces changedAuthority == authorityEffectStageSurfaces originalAuthority)
    "omission changed genuine semantic/authority surfaces"
  assertMutationBoundary original mutated
  -- Preserve the weaker checker's acceptance as a characterization control.
  -- Only the cumulative independent authority should reject this composition.
  mapLeft show $ verifyAuthorityEffectStageBundle changedAuthority
  assertLeft expectedError $ verifyAuthorityEffectStageBundleAgainst expectations changedAuthority
  Right (mutated, expectedError)

dropSites :: Set.Set SystemsMechanismKey -> AuthorityEffectStageBundle -> AuthorityEffectStageBundle
dropSites removed bundle = makeAuthorityEffectStageBundle
  (makeProviderCallStageBundle
    (providerCallStageBase base)
    (providerCallStageSelections base)
    (providerCallStageCallSites base Set.\\ removed)
    (Map.filterWithKey (\site _ -> Set.notMember site removed) (providerCallStageLinks base)))
  (authorityEffectStageSurfaces bundle)
  (Map.filterWithKey (\site _ -> Set.notMember site removed) (authorityEffectStageUses bundle))
  where
    base = authorityEffectStageBase bundle

wrongOperationRejects :: Either String ()
wrongOperationRejects = do
  original <- steveStageClosureBundle
  site <- siteFor computeOperation
  donorSite <- siteFor checkOperation
  let authority = branchResourceStageBase (closureBranch original)
      base = authorityEffectStageBase authority
  donor <- lookupRequired "genuine digest.check link" donorSite (providerCallStageLinks base)
  let changedProvider = makeProviderCallStageBundle
        (providerCallStageBase base) (providerCallStageSelections base)
        (providerCallStageCallSites base)
        (Map.insert site (donor { providerCallMechanism = site }) (providerCallStageLinks base))
      changedAuthority = makeAuthorityEffectStageBundle changedProvider
        (authorityEffectStageSurfaces authority) (authorityEffectStageUses authority)
      mutated = mapClosureBranch (replaceAuthority changedAuthority) original
  mapLeft show $ verifyProviderCallStageBundle changedProvider
  assertMutationBoundary original mutated
  expectClosureBranchError mutated (BranchResourceBaseStageError
    (AuthorityEffectBaseStageError (ProviderCallExpectedOperationMismatch
      site computeOperation checkOperation)))

wrongEntryRejects :: Either String ()
wrongEntryRejects = do
  original <- steveStageClosureBundle
  site <- siteFor computeOperation
  expectation <- lookupRequired "independent compute expectation" site steveProviderCallExpectations
  let occurrence = expectedProviderOccurrence expectation
      authority = branchResourceStageBase (closureBranch original)
      base = authorityEffectStageBase authority
  selection <- lookupRequired "genuine digest selection" occurrence (providerCallStageSelections base)
  originalEntry <- lookupRequired "genuine compute entry" computeOperation
    (selectedProviderOperationEntries selection)
  donorEntry <- lookupRequired "genuine check entry" checkOperation
    (selectedProviderOperationEntries selection)
  assert (originalEntry /= donorEntry) "entry donor is not distinct"
  link <- lookupRequired "compute link" site (providerCallStageLinks base)
  changedLink <- case providerCallBindingBasis link of
    ExactProviderCallBinding provider admission interface operation entry -> do
      assert (provider == occurrence && operation == computeOperation && entry == originalEntry)
        "baseline compute link does not match genuine selection"
      Right (link { providerCallBindingBasis = ExactProviderCallBinding
        provider admission interface operation donorEntry })
    _ -> Left "baseline compute link is not exact"
  let changedSelection = selection
        { selectedProviderOperationEntries = Map.insert computeOperation donorEntry
            (selectedProviderOperationEntries selection) }
      changedProvider = makeProviderCallStageBundle
        (providerCallStageBase base)
        (Map.insert occurrence changedSelection (providerCallStageSelections base))
        (providerCallStageCallSites base)
        (Map.insert site changedLink (providerCallStageLinks base))
      changedAuthority = makeAuthorityEffectStageBundle changedProvider
        (authorityEffectStageSurfaces authority) (authorityEffectStageUses authority)
      mutated = mapClosureBranch (replaceAuthority changedAuthority) original
  mapLeft show $ verifyProviderCallStageBundleCompleteAgainst steveProviderCallExpectations changedProvider
  assertMutationBoundary original mutated
  expectClosureBranchError mutated (BranchResourceBaseStageError
    (AuthorityEffectOperationEntryMismatch occurrence computeOperation))

donorAuthorityRejects
  :: Either String StageClosureBundle
  -> Either String StageClosureBundle
  -> Either String ()
donorAuthorityRejects originalResult donorResult = do
  original <- originalResult
  donor <- donorResult
  mapLeft show $ verifyStageClosureBundle original
  mapLeft show $ verifyStageClosureBundle donor
  let originalBranch = closureBranch original
      donorAuthority = branchResourceStageProviderAuthority (closureBranch donor)
      changedBranch = makeBranchResourceStageBundle donorAuthority
        (branchResourceStageBase originalBranch) (branchResourceStageSites originalBranch)
      mutated = mapClosureBranch (const changedBranch) original
      donorSource = concreteSubjectStage (stageClosureConcrete donor)
      actualSource = concreteSubjectStage (stageClosureConcrete original)
  assert (donorSource /= actualSource) "donor fixture does not have a different source"
  assert (providerCallClosureAuthorityRevision donorAuthority /=
    providerCallClosureAuthorityRevision (branchResourceStageProviderAuthority originalBranch))
    "different source authorities share a context identity"
  assert (branchResourceStageRevision changedBranch /= branchResourceStageRevision originalBranch
    && stageClosureContractRevision mutated /= stageClosureContractRevision original)
    "replacing provider authority did not change cumulative identity"
  assert (concreteSubjectStage (stageClosureConcrete mutated) == actualSource
    && stageClosureNextStage mutated == stageClosureNextStage original)
    "donor-authority mutation altered either source branch"
  assertFresh mutated
  expectClosureBranchError mutated (BranchResourceProviderAuthoritySourceMismatch
    (subjectStageRevision donorSource) (subjectStageRevision actualSource))

authorityOrderIndependent :: Either String ()
authorityOrderIndependent = do
  original <- steveStageClosureBundle
  let branch = closureBranch original
      base = branchResourceStageBase branch
      reordered = Map.fromList (reverse (Map.toAscList steveProviderCallExpectations))
  authority <- mapLeft show $ certifyProviderCallClosureAuthority reordered base
  assert (authority == branchResourceStageProviderAuthority branch)
    "expectation map order changed sealed authority"
  assert (providerCallClosureAuthorityRevision authority ==
    providerCallClosureAuthorityRevision (branchResourceStageProviderAuthority branch))
    "expectation map order changed authority identity"
  let rebuilt = mapClosureBranch (\value -> makeBranchResourceStageBundle authority
        (branchResourceStageBase value) (branchResourceStageSites value)) original
  assert (rebuilt == original) "equivalent authority changed final closure identity"
  mapLeft show $ verifyStageClosureBundle rebuilt

restorationAccepted :: Either String ()
restorationAccepted = do
  original <- steveStageClosureBundle
  (mutated, _) <- prepareOmission original steveProviderCallExpectations True
  let restored = mapClosureBranch
        (replaceAuthority (branchResourceStageBase (closureBranch original))) mutated
  assert (restored == original) "restoration did not recover the complete original closure"
  mapLeft show $ verifyStageClosureBundle restored

canonicalAuthorityRetained :: Either String ()
canonicalAuthorityRetained = mapM_ check [steveStageClosureBundle, uploadStageClosureBundle]
  where
    check fixture = do
      bundle <- fixture
      let authorityRevision = providerCallClosureAuthorityRevision
            (branchResourceStageProviderAuthority (closureBranch bundle))
      assert (authorityRevision `Text.isInfixOf` renderClosedStageContractCanonical bundle)
        "final canonical closure omitted the provider authority identity"

-- Keep the independently sealed authority and every non-provider branch
-- contract intact while rebuilding the ordinary candidate identities.
replaceAuthority :: AuthorityEffectStageBundle -> BranchResourceStageBundle -> BranchResourceStageBundle
replaceAuthority base branch = makeBranchResourceStageBundle
  (branchResourceStageProviderAuthority branch) base (branchResourceStageSites branch)

closureBranch :: StageClosureBundle -> BranchResourceStageBundle
closureBranch bundle = case stageClosureConcrete bundle of
  ConcreteThroughBranch branch -> branch
  ConcreteThroughBoundary boundary ->
    controlStateStageBase (protocolStateStageBase (boundaryCommitStageBase boundary))

mapClosureBranch
  :: (BranchResourceStageBundle -> BranchResourceStageBundle)
  -> StageClosureBundle
  -> StageClosureBundle
mapClosureBranch change bundle = makeStageClosureBundle concrete (stageClosureNextStage bundle)
  where
    concrete = case stageClosureConcrete bundle of
      ConcreteThroughBranch branch -> ConcreteThroughBranch (change branch)
      ConcreteThroughBoundary boundary ->
        let protocol = boundaryCommitStageBase boundary
            control = protocolStateStageBase protocol
            changedControl = makeControlStateStageBundle
              (change (controlStateStageBase control))
              (controlStateStageBoundaries control)
              (controlStateStageProjections control)
              (controlStateStageClosureCaptures control)
            changedProtocol = makeProtocolStateStageBundle changedControl
              (protocolStateStageEndpoints protocol) (protocolStateStageTransitions protocol)
        in ConcreteThroughBoundary (makeBoundaryCommitStageBundle changedProtocol
            (boundaryCommitStageTransfers boundary))

assertMutationBoundary :: StageClosureBundle -> StageClosureBundle -> Either String ()
assertMutationBoundary original mutated = do
  let before = closureBranch original
      after = closureBranch mutated
  assert (mutated /= original) "candidate mutation was a no-op"
  assert (branchResourceStageProviderAuthority after == branchResourceStageProviderAuthority before)
    "candidate mutation changed the independent sealed authority"
  assert (branchResourceStageSites after == branchResourceStageSites before)
    "candidate mutation changed branch resource contracts"
  assert (concreteSubjectStage (stageClosureConcrete mutated) ==
    concreteSubjectStage (stageClosureConcrete original)) "candidate mutation changed the source"
  assert (stageClosureNextStage mutated == stageClosureNextStage original)
    "candidate mutation changed the next-stage branch"
  assert (branchResourceStageRevision after /= branchResourceStageRevision before
    && stageClosureContractRevision mutated /= stageClosureContractRevision original)
    "candidate changes were not rebound into cumulative identities"
  assertFresh mutated

assertFresh :: StageClosureBundle -> Either String ()
assertFresh bundle = do
  let branch = closureBranch bundle
      authority = branchResourceStageBase branch
      provider = authorityEffectStageBase authority
  assert (providerCallStageRevision provider == deriveProviderCallStageRevision provider)
    "provider revision is stale"
  assert (authorityEffectStageRevision authority == deriveAuthorityEffectStageRevision authority)
    "authority/effect revision is stale"
  assert (branchResourceStageRevision branch == deriveBranchResourceStageRevision branch)
    "branch revision is stale"
  assert (mapClosureBranch id bundle == bundle)
    "a control/protocol/boundary/final ancestor has a stale canonical identity"
  assert (stageClosureContractRevision bundle == deriveClosedStageContractRevision bundle)
    "final closure revision is stale"

expectClosureBranchError :: StageClosureBundle -> BranchResourceStageVerificationError -> Either String ()
expectClosureBranchError bundle expected = case verifyStageClosureBundle bundle of
  Right () -> Left "final cumulative verifier accepted the candidate"
  Left err -> case (stageClosureConcrete bundle, err) of
    (ConcreteThroughBranch _, StageClosureBranchError actual) -> check actual
    (ConcreteThroughBoundary _, StageClosureBoundaryError
      (BoundaryCommitBaseStageError (ProtocolStateBaseStageError (ControlStateBaseStageError actual)))) ->
        check actual
    _ -> Left ("candidate rejected outside the mandatory provider boundary: " <> show err)
  where
    check actual = assert (actual == expected)
      ("wrong cumulative provider diagnostic: " <> show actual)

computeOperation, checkOperation :: ProviderOperationKey
computeOperation = ProviderOperationKey "digest.compute"
checkOperation = ProviderOperationKey "digest.check"

siteFor :: ProviderOperationKey -> Either String SystemsMechanismKey
siteFor operation = case
    [ site | (site, expectation) <- Map.toAscList steveProviderCallExpectations
    , expectedProviderOperation expectation == operation
    ] of
  [site] -> Right site
  _ -> Left "fixture needs exactly one independently expected operation site"

lookupRequired :: Ord k => String -> k -> Map.Map k a -> Either String a
lookupRequired label key = maybe (Left ("missing " <> label)) Right . Map.lookup key

assertLeft :: (Eq e, Show e) => e -> Either e a -> Either String ()
assertLeft expected result = case result of
  Left actual -> assert (actual == expected) ("wrong rejection: " <> show actual)
  Right _ -> Left "candidate unexpectedly accepted"

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
