{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Outcome (..), Ty (..))
import Phil.Surface.Check
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  , SurfaceFile (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-014 exact declared simple release is selected" exactReleaseAccepts
    , test "EXEC-014 structural linearity cannot invent release competence" missingReleaseRejects
    , test "EXEC-014 equal-type multiple releases are ambiguous" ambiguousReleaseRejects
    , test "EXEC-014 release prerequisites must already be satisfied" requirementsReject
    , test "EXEC-014 successor-producing cleanup requires explicit operation" replacementRejects
    , test "EXEC-014 branch-sensitive cleanup requires explicit operation" branchSensitiveRejects
    , test "EXEC-014 selected release retains exact semantic account" semanticAccountRetained
    , test "EXEC-014 surface release invokes exact declared consumer" surfaceReleaseAccepts
    , test "EXEC-014 surface release rejects arbitrary equal-mode linear owner" surfaceArbitraryLinearRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactReleaseAccepts :: Either String ()
exactReleaseAccepts = do
  selected <- mapLeft show $ selectReleaseTransition admittedEnvironment ownerTy
  assert (selected == releaseTransition)
    "release selector did not return the exact declared transition"

missingReleaseRejects :: Either String ()
missingReleaseRejects =
  case selectReleaseTransition emptyEnvironment ownerTy of
    Left (NoApplicableReleaseTransition actualTy) ->
      assert (actualTy == ownerTy)
        "missing-release rejection lost exact owner type"
    other -> Left ("arbitrary restricted owner acquired release competence: " <> show other)

ambiguousReleaseRejects :: Either String ()
ambiguousReleaseRejects =
  let second = releaseTransition { releaseTransitionKey = "release.owner.alternate" }
      environment = admittedEnvironment
        { surfaceReleaseTransitions = [releaseTransition, second] }
  in case selectReleaseTransition environment ownerTy of
      Left (AmbiguousReleaseTransitions actualTy keys) ->
        assert
          ( actualTy == ownerTy
            && keys == ["release.owner.v1", "release.owner.alternate"]
          )
          "ambiguous-release rejection lost exact type/transition identities"
      other -> Left ("ambiguous release transitions were silently chosen: " <> show other)

requirementsReject :: Either String ()
requirementsReject =
  let requirement = ReleaseAuthorityRequirement "authority.release.owner"
      guarded = releaseTransition
        { releaseTransitionRequirements = Set.singleton requirement }
      environment = emptyOwnerEnvironment
        { surfaceReleaseTransitions = [guarded] }
  in case selectReleaseTransition environment ownerTy of
      Left (UnsatisfiedReleaseRequirements key missing) ->
        assert
          ( key == releaseTransitionKey guarded
            && missing == Set.singleton requirement
          )
          "release prerequisite rejection lost exact requirement"
      other -> Left ("release ignored an unsatisfied prerequisite: " <> show other)

replacementRejects :: Either String ()
replacementRejects =
  let successorTy = TyOpaque "SuccessorOwner"
      replacing = releaseTransition
        { releaseTransitionResidue = ReleaseReplacesOwner successorTy }
      environment = admittedEnvironment
        { surfaceReleaseTransitions = [replacing] }
  in case selectReleaseTransition environment ownerTy of
      Left (ReleaseReplacementRequiresExplicitOperation key actualSuccessor) ->
        assert
          (key == releaseTransitionKey replacing && actualSuccessor == successorTy)
          "replacement-release rejection lost exact transition/successor"
      other -> Left ("Unit release hid a live successor owner: " <> show other)

branchSensitiveRejects :: Either String ()
branchSensitiveRejects =
  let outcomes = [Outcome "released", Outcome "busy"]
      branching = releaseTransition
        { releaseTransitionOutcome = ReleaseBranchSensitive outcomes }
      environment = admittedEnvironment
        { surfaceReleaseTransitions = [branching] }
  in case selectReleaseTransition environment ownerTy of
      Left (ReleaseBranchSensitiveRequiresExplicitOperation key actualOutcomes) ->
        assert
          (key == releaseTransitionKey branching && actualOutcomes == outcomes)
          "branch-sensitive rejection lost exact transition/outcomes"
      other -> Left ("release shorthand erased branch-sensitive outcomes: " <> show other)

semanticAccountRetained :: Either String ()
semanticAccountRetained = do
  selected <- mapLeft show $ selectReleaseTransition admittedEnvironment ownerTy
  let account = releaseTransitionSemanticAccount selected
  assert
    ( account == semanticAccount
      && releaseAccountAuthorityRefs account == Set.singleton "authority.owner.release"
      && releaseAccountEvidenceRefs account == Set.singleton "evidence.owner.valid"
      && releaseAccountEffectRefs account == Set.singleton "effect.owner.release"
      && releaseAccountAssumptionRefs account == Set.singleton "assumption.device.available"
      && releaseAccountCostRefs account == Set.singleton "cost.owner.release"
      && releaseAccountSubjectRef account == "subject.owner.occurrence"
    )
    "release selection erased or rewrote semantic-account dimensions"

surfaceReleaseAccepts :: Either String ()
surfaceReleaseAccepts = do
  checked <- mapLeft show $ checkReleaseSource admittedEnvironment
  assert (checkedTerminalControls checked == [Continue])
    "simple release did not leave the declared Unit-valued continuation"

surfaceArbitraryLinearRejects :: Either String ()
surfaceArbitraryLinearRejects =
  case checkReleaseSource emptyOwnerEnvironment of
    Left errorValue ->
      assert (surfaceErrorClass errorValue == ReleaseCompetence)
        ("arbitrary linear owner rejected at wrong competence layer: " <> show errorValue)
    Right checked -> Left
      ("arbitrary linear owner was released without a consumer: " <> show checked)

checkReleaseSource :: SurfaceEnvironment -> Either SurfaceCheckError SurfaceCheckResult
checkReleaseSource environment = do
  surfaceFile <- mapLeft parseFailure $
    parseSurfaceFile "exec014" releaseSource
  component <- case surfaceFile of
    SurfaceFile [single] -> Right single
    SurfaceFile components -> Left SurfaceCheckError
      { surfaceErrorSpan = syntheticTestSpan
      , surfaceErrorClass = TypeMismatch
      , surfaceErrorDetail = "unexpected component count: " <> fromString (show (length components))
      }
  checkSurfaceComponent environment component
  where
    parseFailure diagnostic = SurfaceCheckError
      { surfaceErrorSpan = syntheticTestSpan
      , surfaceErrorClass = TypeMismatch
      , surfaceErrorDetail = fromString (show diagnostic)
      }

releaseSource :: Text
releaseSource = "component release_fixture { release owner }"

ownerTy :: Ty
ownerTy = TyOpaque "OwnedResource"

releaseTransition :: ReleaseTransitionContract
releaseTransition = ReleaseTransitionContract
  { releaseTransitionKey = "release.owner.v1"
  , releaseTransitionOwnerType = ownerTy
  , releaseTransitionRequirements = Set.empty
  , releaseTransitionSemanticAccount = semanticAccount
  , releaseTransitionOutcome = ReleaseContinuesUnit
  , releaseTransitionResidue = ReleaseConsumesOwner
  }

semanticAccount :: ReleaseSemanticAccount
semanticAccount = ReleaseSemanticAccount
  { releaseAccountAuthorityRefs = Set.singleton "authority.owner.release"
  , releaseAccountEvidenceRefs = Set.singleton "evidence.owner.valid"
  , releaseAccountEffectRefs = Set.singleton "effect.owner.release"
  , releaseAccountAssumptionRefs = Set.singleton "assumption.device.available"
  , releaseAccountCostRefs = Set.singleton "cost.owner.release"
  , releaseAccountSubjectRef = "subject.owner.occurrence"
  }

emptyEnvironment :: SurfaceEnvironment
emptyEnvironment = emptySurfaceEnvironment emptyStaticContext

emptyOwnerEnvironment :: SurfaceEnvironment
emptyOwnerEnvironment = emptyEnvironment
  { surfaceInitialBindings = Map.singleton "owner"
      (InitialBinding Linear ownerTy PlainShape)
  }

admittedEnvironment :: SurfaceEnvironment
admittedEnvironment = emptyOwnerEnvironment
  { surfaceReleaseTransitions = [releaseTransition]
  , surfaceSatisfiedReleaseRequirements = Set.empty
  }

syntheticTestSpan :: SourceSpan
syntheticTestSpan = SourceSpan
  (SourcePoint "exec014" 1 1 0)
  (SourcePoint "exec014" 1 1 0)

fromString :: String -> Text
fromString = Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
