{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.CallableScope (LoanScopeKey (..))
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..), Outcome (..))
import Phil.Systems.CallableLowering
import Phil.Systems.IR (CostShape (..), emptyCostShape)
import System.Directory (doesFileExist)
import System.Exit (exitFailure)

data PortableCase = PortableCase
  { caseId :: Text
  , caseExpected :: Text
  , caseLayer :: Text
  , caseAuthorities :: Text
  }
  deriving (Eq, Ord, Show)

data PortableProjection = PortableProjection
  { projectionFixtureId :: Text
  , projectionContractRevision :: Bool
  , projectionMachineShape :: Bool
  , projectionOccurrence :: Bool
  , projectionStructuralMode :: Bool
  , projectionCaptures :: Bool
  , projectionCalleeTransition :: Bool
  , projectionCallerAuthority :: Bool
  , projectionInternalAuthority :: Bool
  , projectionEffectBound :: Bool
  , projectionFailureSurface :: Bool
  , projectionLoanScope :: Bool
  , projectionEffectAccounting :: Bool
  , projectionFailureAccounting :: Bool
  , projectionAssumptionAccounting :: Bool
  , projectionCarrierAccounting :: Bool
  , projectionCostAccounting :: Bool
  }
  deriving (Eq, Ord, Show)

data PortableAuthority = PortableAuthority
  { authorityRef :: Text
  , authorityKind :: Text
  , authorityCanonicalId :: Text
  , authorityCanonicalSource :: Text
  }
  deriving (Eq, Ord, Show)

root :: FilePath
root = "test/fixtures/phase1-negative/callable-lowering-v1"

manifestPath, projectionPath, authoritiesPath :: FilePath
manifestPath = root <> "/manifest.tsv"
projectionPath = root <> "/projection-v1.tsv"
authoritiesPath = root <> "/authority-registry-v1.tsv"

main :: IO ()
main = do
  cases <- readParsed manifestPath parseManifest "manifest"
  projections <- readParsed projectionPath parseProjections "projection"
  authorities <- readParsed authoritiesPath parseAuthorities "authority registry"
  integrity <- checkIntegrity cases projections authorities
  results <- forM cases (replayCase projections)
  unless (integrity && and results) exitFailure
  putStrLn
    ("PASS: INT-004 portable CALL-016 lowering negatives ("
      <> show (length cases) <> " fixtures)")

readParsed :: FilePath -> (Text -> Either String a) -> String -> IO a
readParsed path parser label = do
  input <- TextIO.readFile path
  case parser input of
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> exitFailure
    Right value -> pure value

parseManifest :: Text -> Either String [PortableCase]
parseManifest = parseTable
  ["fixture_id", "expect", "competent_layer", "governing_authority"] parseRow
  where
    parseRow row = case row of
      [fixtureId, expectedResult, layer, authorities]
        | all (not . Text.null) row ->
            Right (PortableCase fixtureId expectedResult layer authorities)
      _ -> Left ("invalid manifest row: " <> show row)

parseProjections :: Text -> Either String [PortableProjection]
parseProjections = parseTable expected parseRow
  where
    expected =
      [ "fixture_id"
      , "contract-revision"
      , "machine-shape"
      , "occurrence"
      , "structural-mode"
      , "captures"
      , "callee-transition"
      , "caller-authority"
      , "internal-authority"
      , "effect-bound"
      , "failure-surface"
      , "loan-scope"
      , "effect-accounting"
      , "failure-accounting"
      , "assumption-accounting"
      , "carrier-accounting"
      , "cost-accounting"
      ]
    parseRow row = case row of
      [ fixtureId, contract, machineShape, occurrence, structuralMode, captures
        , transition, callerAuthority, internalAuthority, effectBound, failureSurface
        , loanScope, effectAccounting, failureAccounting, assumptionAccounting
        , carrierAccounting, costAccounting
        ]
        | not (Text.null fixtureId) -> do
            contract' <- parseRelation contract
            machineShape' <- parseRelation machineShape
            occurrence' <- parseRelation occurrence
            structuralMode' <- parseRelation structuralMode
            captures' <- parseRelation captures
            transition' <- parseRelation transition
            callerAuthority' <- parseRelation callerAuthority
            internalAuthority' <- parseRelation internalAuthority
            effectBound' <- parseRelation effectBound
            failureSurface' <- parseRelation failureSurface
            loanScope' <- parseRelation loanScope
            effectAccounting' <- parseRelation effectAccounting
            failureAccounting' <- parseRelation failureAccounting
            assumptionAccounting' <- parseRelation assumptionAccounting
            carrierAccounting' <- parseRelation carrierAccounting
            costAccounting' <- parseRelation costAccounting
            Right PortableProjection
              { projectionFixtureId = fixtureId
              , projectionContractRevision = contract'
              , projectionMachineShape = machineShape'
              , projectionOccurrence = occurrence'
              , projectionStructuralMode = structuralMode'
              , projectionCaptures = captures'
              , projectionCalleeTransition = transition'
              , projectionCallerAuthority = callerAuthority'
              , projectionInternalAuthority = internalAuthority'
              , projectionEffectBound = effectBound'
              , projectionFailureSurface = failureSurface'
              , projectionLoanScope = loanScope'
              , projectionEffectAccounting = effectAccounting'
              , projectionFailureAccounting = failureAccounting'
              , projectionAssumptionAccounting = assumptionAccounting'
              , projectionCarrierAccounting = carrierAccounting'
              , projectionCostAccounting = costAccounting'
              }
      _ -> Left ("invalid projection row: " <> show row)

parseRelation :: Text -> Either String Bool
parseRelation value = case value of
  "match" -> Right True
  "mismatch" -> Right False
  _ -> Left ("unknown CALL-016 relation vocabulary: " <> Text.unpack value)

parseAuthorities :: Text -> Either String [PortableAuthority]
parseAuthorities = parseTable
  ["authority_ref", "authority_kind", "canonical_id", "canonical_source"] parseRow
  where
    parseRow row = case row of
      [ref, kind, canonicalId, source]
        | all (not . Text.null) row ->
            Right (PortableAuthority ref kind canonicalId source)
      _ -> Left ("invalid authority row: " <> show row)

parseTable :: [Text] -> ([Text] -> Either String a) -> Text -> Either String [a]
parseTable expectedHeader parseRow input = case Text.lines input of
  [] -> Left "empty TSV"
  header : rows
    | Text.splitOn "\t" header /= expectedHeader ->
        Left ("unexpected header: " <> Text.unpack header)
    | otherwise ->
        traverse (parseRow . Text.splitOn "\t") (filter (not . Text.null) rows)

checkIntegrity
  :: [PortableCase]
  -> [PortableProjection]
  -> [PortableAuthority]
  -> IO Bool
checkIntegrity cases projections authorities = do
  let fixtureIds = map caseId cases
      fixtureDomain = Set.fromList fixtureIds
      projectionIds = map projectionFixtureId projections
      projectionDomain = Set.fromList projectionIds
      exactCount = length cases == 16
      uniqueFixtures = Set.size fixtureDomain == length fixtureIds
      uniqueProjections = Set.size projectionDomain == length projectionIds
      domainsExact = fixtureDomain == projectionDomain
      layerExact = all ((== "callable-lowering") . caseLayer) cases
      expectedVocabulary = Set.fromList (map caseExpected cases)
      expectedVocabularyExact = expectedVocabulary == Set.fromList allPortableRejections
      singleMismatch = all ((== 1) . mismatchCount) projections
      projectionById = Map.fromList
        [(projectionFixtureId projection, projection) | projection <- projections]
      expectationExact = all (caseMatchesProjection projectionById) cases
      registryRefs = Set.fromList (map authorityRef authorities)
      registryUnique = Set.size registryRefs == length authorities
      registryRowsValid = all authorityRowWellFormed authorities
      parsedRefs = traverse caseAuthorityRefs cases
      usedRefs = either (const Set.empty) (Set.fromList . concat) parsedRefs
      authorityDomainExact =
        either (const False) (const True) parsedRefs && usedRefs == registryRefs
      certifiedPaths =
        [ Text.unpack (authorityCanonicalSource authority)
        | authority <- authorities
        , authorityKind authority == "certified"
        ]
  certifiedPresent <- and <$> mapM doesFileExist certifiedPaths
  report "sixteen CALL-016 negative fixtures are manifest-owned" exactCount
  report "portable fixture identities are unique" uniqueFixtures
  report "portable projection identities are unique" uniqueProjections
  report "manifest and projection domains agree exactly" domainsExact
  report "competent layer is callable-lowering" layerExact
  report "portable rejection vocabulary covers all sixteen certified coordinates" expectedVocabularyExact
  report "each fixture disagrees on exactly one certified coordinate" singleMismatch
  report "each manifest rejection matches its projection coordinate" expectationExact
  report "authority registry is unique and well formed" (registryUnique && registryRowsValid)
  report "manifest authority domain resolves exactly" authorityDomainExact
  report "every Certified authority proof artifact exists" certifiedPresent
  pure (and
    [ exactCount
    , uniqueFixtures
    , uniqueProjections
    , domainsExact
    , layerExact
    , expectedVocabularyExact
    , singleMismatch
    , expectationExact
    , registryUnique
    , registryRowsValid
    , authorityDomainExact
    , certifiedPresent
    ])

allPortableRejections :: [Text]
allPortableRejections =
  [ "contract-revision-mismatch"
  , "machine-shape-mismatch"
  , "occurrence-mismatch"
  , "structural-mode-mismatch"
  , "capture-mismatch"
  , "callee-transition-mismatch"
  , "caller-authority-mismatch"
  , "internal-authority-mismatch"
  , "effect-bound-mismatch"
  , "failure-surface-mismatch"
  , "loan-scope-mismatch"
  , "effect-accounting-mismatch"
  , "failure-accounting-mismatch"
  , "assumption-accounting-mismatch"
  , "carrier-accounting-mismatch"
  , "cost-accounting-mismatch"
  ]

projectionRelations :: PortableProjection -> [(Text, Bool)]
projectionRelations projection =
  [ ("contract-revision-mismatch", projectionContractRevision projection)
  , ("machine-shape-mismatch", projectionMachineShape projection)
  , ("occurrence-mismatch", projectionOccurrence projection)
  , ("structural-mode-mismatch", projectionStructuralMode projection)
  , ("capture-mismatch", projectionCaptures projection)
  , ("callee-transition-mismatch", projectionCalleeTransition projection)
  , ("caller-authority-mismatch", projectionCallerAuthority projection)
  , ("internal-authority-mismatch", projectionInternalAuthority projection)
  , ("effect-bound-mismatch", projectionEffectBound projection)
  , ("failure-surface-mismatch", projectionFailureSurface projection)
  , ("loan-scope-mismatch", projectionLoanScope projection)
  , ("effect-accounting-mismatch", projectionEffectAccounting projection)
  , ("failure-accounting-mismatch", projectionFailureAccounting projection)
  , ("assumption-accounting-mismatch", projectionAssumptionAccounting projection)
  , ("carrier-accounting-mismatch", projectionCarrierAccounting projection)
  , ("cost-accounting-mismatch", projectionCostAccounting projection)
  ]

mismatchCount :: PortableProjection -> Int
mismatchCount = length . filter (not . snd) . projectionRelations

projectionExpected :: PortableProjection -> Maybe Text
projectionExpected projection = case
    [label | (label, matches) <- projectionRelations projection, not matches] of
  [label] -> Just label
  _ -> Nothing

caseMatchesProjection :: Map.Map Text PortableProjection -> PortableCase -> Bool
caseMatchesProjection projections portableCase =
  case Map.lookup (caseId portableCase) projections of
    Nothing -> False
    Just projection -> projectionExpected projection == Just (caseExpected portableCase)

caseAuthorityRefs :: PortableCase -> Either String [Text]
caseAuthorityRefs portableCase =
  let refs = Text.splitOn ";" (caseAuthorities portableCase)
  in if null refs || any Text.null refs || length refs /= Set.size (Set.fromList refs)
      then Left ("invalid authority list for " <> Text.unpack (caseId portableCase))
      else Right refs

authorityRowWellFormed :: PortableAuthority -> Bool
authorityRowWellFormed authority = case authorityKind authority of
  "matrix" ->
    authorityRef authority == "matrix:" <> authorityCanonicalId authority
      && authorityCanonicalSource authority == "Phil Phase 1 Conformance Matrix"
  "certified" ->
    authorityRef authority == "certified:" <> authorityCanonicalId authority
      && "proof/" `Text.isPrefixOf` authorityCanonicalSource authority
  _ -> False

replayCase :: [PortableProjection] -> PortableCase -> IO Bool
replayCase projections portableCase =
  case lookupProjection (caseId portableCase) projections of
    Nothing -> reportCase portableCase False "missing portable projection"
    Just projection ->
      let (source, target, accounting) = materializeProjection projection
      in case checkCallableLoweringCorrespondence source target accounting of
          Left err ->
            let actual = portableRejection err
            in reportCase portableCase (actual == caseExpected portableCase)
                ("expected " <> Text.unpack (caseExpected portableCase)
                  <> ", got " <> Text.unpack actual)
          Right _ -> reportCase portableCase False "unexpected acceptance"

lookupProjection :: Text -> [PortableProjection] -> Maybe PortableProjection
lookupProjection fixtureId = go
  where
    go [] = Nothing
    go (projection : rest)
      | projectionFixtureId projection == fixtureId = Just projection
      | otherwise = go rest

portableRejection :: CallableLoweringError -> Text
portableRejection err = case err of
  CallableLoweringContractRevisionMismatch _ _ -> "contract-revision-mismatch"
  CallableLoweringMachineShapeMismatch _ _ -> "machine-shape-mismatch"
  CallableLoweringOccurrenceMismatch _ _ -> "occurrence-mismatch"
  CallableLoweringStructuralModeMismatch _ _ -> "structural-mode-mismatch"
  CallableLoweringCaptureMismatch _ _ -> "capture-mismatch"
  CallableLoweringCalleeTransitionMismatch _ _ -> "callee-transition-mismatch"
  CallableLoweringCallerAuthorityMismatch _ _ -> "caller-authority-mismatch"
  CallableLoweringInternalAuthorityMismatch _ _ -> "internal-authority-mismatch"
  CallableLoweringEffectBoundMismatch _ _ -> "effect-bound-mismatch"
  CallableLoweringFailureMismatch _ _ -> "failure-surface-mismatch"
  CallableLoweringLoanScopeMismatch _ _ -> "loan-scope-mismatch"
  CallableLoweringEffectAccountingMismatch _ _ -> "effect-accounting-mismatch"
  CallableLoweringFailureAccountingMismatch _ _ -> "failure-accounting-mismatch"
  CallableLoweringAssumptionAccountingMismatch _ _ -> "assumption-accounting-mismatch"
  CallableLoweringCarrierAccountingMismatch _ _ -> "carrier-accounting-mismatch"
  CallableLoweringCostAccountingMismatch _ _ -> "cost-accounting-mismatch"
  CallableLoweringRepresentationBridgeMismatch _ -> "representation-bridge-mismatch"

materializeProjection
  :: PortableProjection
  -> (SourceCallableLoweringFacts, TargetCallableLoweringFacts, CallableRealizationAccounting)
materializeProjection projection = (sourceFacts, target, accounting)
  where
    target = targetFacts
      { targetCallableContractRevision = choose
          (projectionContractRevision projection) contractRevision otherContractRevision
      , targetCallableMachineShape = choose
          (projectionMachineShape projection) machineShape otherMachineShape
      , targetCallableOccurrence = Just (choose
          (projectionOccurrence projection) callableOccurrence otherCallableOccurrence)
      , targetCallableStructuralMode = choose
          (projectionStructuralMode projection) Linear Unrestricted
      , targetCallableCaptures = choose
          (projectionCaptures projection) sourceCaptures badCaptures
      , targetCallableCalleeTransition = choose
          (projectionCalleeTransition projection) PreserveCallee ConsumeCallee
      , targetCallableCallerAuthority = choose
          (projectionCallerAuthority projection)
          (Set.singleton readAuthority)
          (Set.fromList [readAuthority, writeAuthority])
      , targetCallableInternalAuthority = choose
          (projectionInternalAuthority projection)
          internalAuthority
          (Set.singleton readAuthority)
      , targetCallableEffectBound = choose
          (projectionEffectBound projection)
          (Set.singleton readEffect)
          (Set.fromList [readEffect, writeEffect])
      , targetCallableFailures = choose
          (projectionFailureSurface projection)
          (Set.singleton notFoundFailure)
          (Set.fromList [notFoundFailure, targetAbortFailure])
      , targetCallableLiveLoans = choose
          (projectionLoanScope projection)
          sourceLoans
          (Set.insert expiredLoan sourceLoans)
      }
    accounting = baselineAccounting
      { accountedCallableEffects = choose
          (projectionEffectAccounting projection)
          (Set.singleton allocationEffect)
          Set.empty
      , accountedCallableFailures = choose
          (projectionFailureAccounting projection)
          (Set.singleton allocatorFailure)
          Set.empty
      , accountedCallableAssumptions = choose
          (projectionAssumptionAccounting projection)
          (Set.singleton allocatorAssumption)
          Set.empty
      , accountedCallableCarriers = choose
          (projectionCarrierAccounting projection)
          (Set.singleton environmentCarrier)
          Set.empty
      , accountedCallableCost = choose
          (projectionCostAccounting projection) allocationCost emptyCostShape
      }

choose :: Bool -> a -> a -> a
choose relation matching mismatching
  | relation = matching
  | otherwise = mismatching

contractRevision, otherContractRevision :: InterfaceRevision
contractRevision = InterfaceRevision "callable.read-closure.v1"
otherContractRevision = InterfaceRevision "callable.other.v1"

machineShape, otherMachineShape :: CallableMachineShape
machineShape = CallableMachineShape "fn(blob)->bytes"
otherMachineShape = CallableMachineShape "fn(blob)->status"

callableOccurrence, otherCallableOccurrence :: CallableOccurrenceKey
callableOccurrence = CallableOccurrenceKey "closure.read.001"
otherCallableOccurrence = CallableOccurrenceKey "closure.read.002"

capturedOwner :: CaptureOccurrenceKey
capturedOwner = CaptureOccurrenceKey "owner.blob.001"

readAuthority, writeAuthority, deleteAuthority :: CallableAuthorityRequirement
readAuthority = CallableAuthorityRequirement "storage.read"
writeAuthority = CallableAuthorityRequirement "storage.write"
deleteAuthority = CallableAuthorityRequirement "storage.delete"

internalAuthority :: Set.Set CallableAuthorityRequirement
internalAuthority = Set.fromList [readAuthority, deleteAuthority]

readEffect, writeEffect, allocationEffect :: SemanticEffect
readEffect = SemanticEffect "read"
writeEffect = SemanticEffect "write"
allocationEffect = SemanticEffect "target.allocate-closure-environment"

notFoundFailure, targetAbortFailure, allocatorFailure :: CallableFailure
notFoundFailure = CallableTypedNegative (Outcome "not-found")
targetAbortFailure = CallableFatal "target-abort"
allocatorFailure = CallableFatal "allocator-failure"

sourceLoan, expiredLoan :: LoanScopeKey
sourceLoan = LoanScopeKey "loan.local.001"
expiredLoan = LoanScopeKey "loan.expired"

sourceLoans :: Set.Set LoanScopeKey
sourceLoans = Set.singleton sourceLoan

capturedSemantic, badCapturedSemantic :: CallableCaptureSemantic
capturedSemantic = CallableCaptureSemantic
  { callableCaptureSemanticMode = Linear
  , callableCaptureSemanticSubject = Just "blob.001"
  , callableCaptureSemanticAuthority = internalAuthority
  }
badCapturedSemantic = capturedSemantic
  { callableCaptureSemanticSubject = Just "blob.002" }

sourceCaptures, badCaptures :: Map.Map CaptureOccurrenceKey CallableCaptureSemantic
sourceCaptures = Map.singleton capturedOwner capturedSemantic
badCaptures = Map.singleton capturedOwner badCapturedSemantic

sourceFacts :: SourceCallableLoweringFacts
sourceFacts = SourceCallableLoweringFacts
  { sourceCallableContractRevision = contractRevision
  , sourceCallableMachineShape = machineShape
  , sourceCallableOccurrence = Just callableOccurrence
  , sourceCallableStructuralMode = Linear
  , sourceCallableCaptures = sourceCaptures
  , sourceCallableCalleeTransition = PreserveCallee
  , sourceCallableCallerAuthority = Set.singleton readAuthority
  , sourceCallableInternalAuthority = internalAuthority
  , sourceCallableEffectBound = Set.singleton readEffect
  , sourceCallableFailures = Set.singleton notFoundFailure
  , sourceCallableLiveLoans = sourceLoans
  }

allocatorAssumption, environmentCarrier :: Text
allocatorAssumption = "allocator.available"
environmentCarrier = "closure-environment-pointer"

allocationCost :: CostShape
allocationCost = emptyCostShape
  { costAllocationCount = Just "1 per closure construction"
  , costPeakLiveMemory = Just "closure environment size"
  , costFrequency = Just "once per constructed closure"
  }

targetFacts :: TargetCallableLoweringFacts
targetFacts = TargetCallableLoweringFacts
  { targetCallableRepresentation = CodePointerEnvironment
  , targetCallableRepresentationIdentity = Just "nonsemantic-representation-id"
  , targetCallableContractRevision = contractRevision
  , targetCallableMachineShape = machineShape
  , targetCallableOccurrence = Just callableOccurrence
  , targetCallableStructuralMode = Linear
  , targetCallableCaptures = sourceCaptures
  , targetCallableCalleeTransition = PreserveCallee
  , targetCallableCallerAuthority = Set.singleton readAuthority
  , targetCallableInternalAuthority = internalAuthority
  , targetCallableEffectBound = Set.singleton readEffect
  , targetCallableFailures = Set.singleton notFoundFailure
  , targetCallableLiveLoans = sourceLoans
  , targetCallableIntroducedEffects = Set.singleton allocationEffect
  , targetCallableIntroducedFailures = Set.singleton allocatorFailure
  , targetCallableIntroducedAssumptions = Set.singleton allocatorAssumption
  , targetCallableIntroducedCarriers = Set.singleton environmentCarrier
  , targetCallableIntroducedCost = allocationCost
  }

baselineAccounting :: CallableRealizationAccounting
baselineAccounting = CallableRealizationAccounting
  { accountedCallableEffects = Set.singleton allocationEffect
  , accountedCallableFailures = Set.singleton allocatorFailure
  , accountedCallableAssumptions = Set.singleton allocatorAssumption
  , accountedCallableCarriers = Set.singleton environmentCarrier
  , accountedCallableCost = allocationCost
  }

report :: String -> Bool -> IO ()
report label passed =
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)

reportCase :: PortableCase -> Bool -> String -> IO Bool
reportCase portableCase passed detail = do
  putStrLn
    ((if passed then "PASS: " else "FAIL: ")
      <> Text.unpack (caseId portableCase)
      <> " -- " <> detail)
  pure passed
