{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCorePolicy
import Phil.Compiler.SourceSystems
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.Check
  ( PrimitiveSemantics (PrimitiveShouldCancel)
  , SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.Lineage
  ( GrammarRevision (..)
  , InstanceLineageSiteId (..)
  , canonicalGrammarRevisionV1
  , decodePortableSourceBundle
  )
import Phil.Systems.GenericLowering
import Phil.Systems.IR (CompilationProfile (CheckedRuntime))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "complete call and branch policy accepts exact Core"
        exactPolicyAccepts
    , test "missing source call disposition rejects"
        missingCallPolicyRejects
    , test "extra source call disposition rejects"
        extraCallPolicyRejects
    , test "ordinary call target mismatch rejects"
        runtimeOperationMismatchRejects
    , test "provider target substitution rejects"
        providerTargetSubstitutionRejects
    , test "missing branch disposition rejects"
        missingBranchPolicyRejects
    , test "branch arm-label mismatch rejects"
        branchLabelMismatchRejects
    , test "runtime-choice successor substitution rejects"
        branchTargetSubstitutionRejects
    , test "Systems admission requires the complete policy"
        systemsAdmissionRequiresPolicy
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactPolicyAccepts :: Either String ()
exactPolicyAccepts = do
  architecture <- checkedArchitecture
  mapLeft show (verifySourceCorePolicy exactPolicy architecture goodCore)

missingCallPolicyRejects :: Either String ()
missingCallPolicyRejects = do
  architecture <- checkedArchitecture
  let incomplete = exactPolicy
        { sourceCoreCallPolicy = Map.delete callSite1 (sourceCoreCallPolicy exactPolicy) }
  case verifySourceCorePolicy incomplete architecture goodCore of
    Left (SourceCoreCallPolicyDomainMismatch expected supplied) ->
      assert (Set.size expected == 2 && Set.size supplied == 1)
        "missing-call diagnostic lost exact source/policy domains"
    other -> Left ("missing call policy crossed correspondence boundary: " <> show other)

extraCallPolicyRejects :: Either String ()
extraCallPolicyRejects = do
  architecture <- checkedArchitecture
  let extra = exactPolicy
        { sourceCoreCallPolicy = Map.insert
            (SourceCoreSite "Alpha" 2)
            SourceCallErasedStatic
            (sourceCoreCallPolicy exactPolicy)
        }
  case verifySourceCorePolicy extra architecture goodCore of
    Left (SourceCoreCallPolicyDomainMismatch expected supplied) ->
      assert (Set.size expected == 2 && Set.size supplied == 3)
        "extra-call diagnostic lost exact source/policy domains"
    other -> Left ("extra call policy crossed correspondence boundary: " <> show other)

runtimeOperationMismatchRejects :: Either String ()
runtimeOperationMismatchRejects = do
  architecture <- checkedArchitecture
  let wrong = exactPolicy
        { sourceCoreCallPolicy = Map.insert callSite0
            (SourceCallRuntimeOperation "ordinary.wrong")
            (sourceCoreCallPolicy exactPolicy)
        }
  case verifySourceCorePolicy wrong architecture goodCore of
    Left (SourceCoreRuntimeOperationMissing site "ordinary.wrong") ->
      assert (site == callSite0) "runtime-operation mismatch lost exact source site"
    other -> Left ("wrong ordinary runtime operation accepted: " <> show other)

providerTargetSubstitutionRejects :: Either String ()
providerTargetSubstitutionRejects = do
  architecture <- checkedArchitecture
  let donor = exactPolicy
        { sourceCoreCallPolicy = Map.insert callSite1
            (SourceCallRuntimeChoice "OtherProvider.compute")
            (sourceCoreCallPolicy exactPolicy)
        }
  case verifySourceCorePolicy donor architecture goodCore of
    Left (SourceCoreRuntimeChoiceMissing site "OtherProvider.compute") ->
      assert (site == callSite1) "provider substitution lost exact source site"
    other -> Left ("different provider target accepted: " <> show other)

missingBranchPolicyRejects :: Either String ()
missingBranchPolicyRejects = do
  architecture <- checkedArchitecture
  let incomplete = exactPolicy { sourceCoreBranchPolicy = Map.empty }
  case verifySourceCorePolicy incomplete architecture goodCore of
    Left (SourceCoreBranchPolicyDomainMismatch expected supplied) ->
      assert (Set.size expected == 1 && Set.null supplied)
        "missing-branch diagnostic lost exact source/policy domains"
    other -> Left ("missing branch policy crossed correspondence boundary: " <> show other)

branchLabelMismatchRejects :: Either String ()
branchLabelMismatchRejects = do
  architecture <- checkedArchitecture
  let wrong = exactPolicy
        { sourceCoreBranchPolicy = Map.singleton branchSite0
            (SourceBranchDisposition "entry"
              (Map.fromList [("left", "yes"), ("right", "no")]))
        }
  case verifySourceCorePolicy wrong architecture goodCore of
    Left (SourceCoreBranchLabelMismatch site sourceLabels suppliedLabels) ->
      assert
        (site == branchSite0
          && sourceLabels == Set.fromList ["true", "false"]
          && suppliedLabels == Set.fromList ["left", "right"])
        "branch-label mismatch lost exact labels"
    other -> Left ("wrong branch labels accepted: " <> show other)

branchTargetSubstitutionRejects :: Either String ()
branchTargetSubstitutionRejects = do
  architecture <- checkedArchitecture
  let wrong = exactPolicy
        { sourceCoreBranchPolicy = Map.singleton branchSite0
            (SourceBranchDisposition "entry"
              (Map.fromList [("true", "no"), ("false", "yes")]))
        }
  case verifySourceCorePolicy wrong architecture goodCore of
    Left (SourceCoreBranchTargetsMismatch site expected actual) ->
      assert
        (site == branchSite0 && expected /= actual)
        "branch-target substitution diagnostic lost exact mapping"
    other -> Left ("swapped branch targets accepted: " <> show other)

systemsAdmissionRequiresPolicy :: Either String ()
systemsAdmissionRequiresPolicy = do
  architecture <- checkedArchitecture
  case prepareSourceSystemsAdmission emptySourceCoreCorrespondencePolicy architecture goodCore of
    Left (SourceSystemsPolicyRejected
      (SourceCoreCallPolicyDomainMismatch expected supplied)) ->
        assert (Set.size expected == 2 && Set.null supplied)
          "Systems admission did not expose complete call-policy failure"
    other -> Left ("Systems admission accepted incomplete source-Core policy: " <> show other)

exactPolicy :: SourceCoreCorrespondencePolicy
exactPolicy = SourceCoreCorrespondencePolicy
  { sourceCoreCallPolicy = Map.fromList
      [ (callSite0, SourceCallRuntimeOperation "ordinary.compute")
      , (callSite1, SourceCallRuntimeChoice "DigestProvider.compute")
      ]
  , sourceCoreBranchPolicy = Map.singleton branchSite0
      (SourceBranchDisposition "entry"
        (Map.fromList [("true", "yes"), ("false", "no")]))
  }

callSite0, callSite1, branchSite0 :: SourceCoreSite
callSite0 = SourceCoreSite "Alpha" 0
callSite1 = SourceCoreSite "Alpha" 1
branchSite0 = SourceCoreSite "Alpha" 0

checkedArchitecture :: Either String CheckedSourceArchitecture
checkedArchitecture = do
  bundle <- mapLeft show (decodePortableSourceBundle bundleText)
  checked <- mapLeft show $ checkPortableSourceBundle
    (Map.singleton "program:demo" (DeclarationKey "decl:alpha"))
    (Map.singleton (DeclarationKey "decl:alpha") unitEnvironment)
    bundle
  architecture <- mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:demo" (InstanceLineageSiteId "instance.alpha"))
    checked
  assert
    (Map.keysSet (sourceCoreCallSites architecture) == Set.fromList [callSite0, callSite1])
    "fixture did not produce the expected two canonical call sites"
  assert
    (Map.lookup branchSite0 (sourceCoreBranchSites architecture)
      == Just (Set.fromList ["true", "false"]))
    "fixture did not produce the expected canonical branch site"
  Right architecture

bundleText :: Text
bundleText = Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "grammar\t" <> unGrammarRevision canonicalGrammarRevisionV1
  , "root\tprogram:demo"
  , "unit\tunit.alpha\tsite.alpha\tdecl:alpha\tcomponent Alpha provides Unit { let ordinary = should_cancel_upload() let provider = should_cancel_upload() decide ordinary { true => { return unit } false => { return unit } } }"
  , "instance\tinstance.alpha\tinst:alpha"
  ]

unitEnvironment :: SurfaceEnvironment
unitEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfacePrimitives = Map.singleton "should_cancel_upload" PrimitiveShouldCancel
  , surfaceExpectedProvides = Just TyUnit
  }

goodCore :: CoreSystemsProgram
goodCore = CoreSystemsProgram
  { coreProgramLabel = "policy-fixture"
  , coreProgramProfile = CheckedRuntime
  , coreProgramFunctions = Map.singleton "Alpha" alphaFunction
  , coreProgramFacts = Map.singleton "policy.source.checked" Nothing
  }

alphaFunction :: CoreSystemsFunction
alphaFunction = CoreSystemsFunction
  { coreFunctionKey = "Alpha"
  , coreFunctionEntry = "entry"
  , coreFunctionValues = Map.empty
  , coreFunctionBlocks = Map.fromList
      [ ("entry", CoreSystemsBlock "entry"
          [CoreRuntimeCall "ordinary-decision" "ordinary.compute" [] [] Nothing]
          (CoreSystemsRuntimeChoice "DigestProvider.compute" [] Nothing
            (Map.fromList [("true", "yes"), ("false", "no")])))
      , ("yes", CoreSystemsBlock "yes" [] (CoreSystemsEnd "return"))
      , ("no", CoreSystemsBlock "no" [] (CoreSystemsEnd "return"))
      ]
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
