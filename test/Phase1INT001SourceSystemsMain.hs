{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCore
import Phil.Compiler.SourceSystems
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , DeclarationKey (..)
  , InstanceKey (..)
  , SemanticForm (..)
  , emptyStaticContext
  , identityInstanceRevision
  )
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.Check
  ( SurfaceEnvironment (..)
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
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle
  , phase1StageInstanceRevision
  , phase1StageRealizationRevision
  , verifyPhase1StageBundle
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "corresponded admission lowers through generic Systems producer"
        correspondedLoweringAccepts
    , test "lowered Systems bundle retains exact source-derived instance revision"
        instanceRevisionRetained
    , test "different realization context changes realization but not source instance"
        realizationVariationPreservesSource
    , test "tampered Core cannot be sealed into source Systems admission"
        tamperedCoreCannotBeSealed
    , test "admission records exact source Architecture and Core semantics"
        admissionIdentityIsExact
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

correspondedLoweringAccepts :: Either String ()
correspondedLoweringAccepts = do
  admission <- admissionFor goodCore
  bundle <- mapLeft show (lowerSourceSystems admission contextA)
  mapLeft show (verifyPhase1StageBundle bundle)

instanceRevisionRetained :: Either String ()
instanceRevisionRetained = do
  admission <- admissionFor goodCore
  bundle <- mapLeft show (lowerSourceSystems admission contextA)
  assert
    (phase1StageInstanceRevision bundle
      == identityInstanceRevision (sourceSystemsArchitectureIdentity admission))
    "generic Systems bundle did not retain admitted source Architecture revision"

realizationVariationPreservesSource :: Either String ()
realizationVariationPreservesSource = do
  admission <- admissionFor goodCore
  left <- mapLeft show (lowerSourceSystems admission contextA)
  right <- mapLeft show (lowerSourceSystems admission contextB)
  assert
    (phase1StageInstanceRevision left == phase1StageInstanceRevision right)
    "realization variation changed admitted source instance revision"
  assert
    (phase1StageRealizationRevision left /= phase1StageRealizationRevision right)
    "distinct realization contexts did not change realization revision"

tamperedCoreCannotBeSealed :: Either String ()
tamperedCoreCannotBeSealed = do
  architecture <- checkedArchitecture
  let betaFunction = alphaFunction { coreFunctionKey = "Beta" }
      tampered = goodCore
        { coreProgramFunctions = Map.singleton "Beta" betaFunction }
  case prepareSourceSystemsAdmission architecture tampered of
    Left (SourceSystemsCorrespondenceRejected
      (SourceCoreFunctionSetMismatch expected actual)) ->
        assert (expected /= actual) "tampered Core rejection lost function-domain mismatch"
    other -> Left ("tampered Core crossed source Systems admission: " <> show other)

admissionIdentityIsExact :: Either String ()
admissionIdentityIsExact = do
  architecture <- checkedArchitecture
  admission <- mapLeft show (prepareSourceSystemsAdmission architecture goodCore)
  correspondence <- mapLeft show (verifySourceCoreCorrespondence architecture goodCore)
  assert
    (sourceSystemsArchitectureIdentity admission
      == sourceCoreArchitectureIdentity correspondence)
    "sealed admission changed source Architecture identity"
  assert
    (sourceSystemsProgramSemantics admission
      == sourceCoreProgramSemantics correspondence)
    "sealed admission changed Core semantic identity"

admissionFor :: CoreSystemsProgram -> Either String SourceSystemsAdmission
admissionFor program = do
  architecture <- checkedArchitecture
  mapLeft show (prepareSourceSystemsAdmission architecture program)

checkedArchitecture :: Either String CheckedSourceArchitecture
checkedArchitecture = do
  bundle <- mapLeft show $ decodePortableSourceBundle bundleText
  checked <- mapLeft show $ checkPortableSourceBundle
    (Map.singleton "program:demo" (DeclarationKey "decl:alpha"))
    (Map.singleton (DeclarationKey "decl:alpha") unitEnvironment)
    bundle
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:demo" (InstanceLineageSiteId "instance.alpha"))
    checked

bundleText :: Text
bundleText = Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "grammar\t" <> unGrammarRevision canonicalGrammarRevisionV1
  , "root\tprogram:demo"
  , "unit\tunit.alpha\tsite.alpha\tdecl:alpha\tcomponent Alpha provides Unit { return unit }"
  , "instance\tinstance.alpha\tinst:alpha"
  ]

unitEnvironment :: SurfaceEnvironment
unitEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceExpectedProvides = Just TyUnit }

goodCore :: CoreSystemsProgram
goodCore = CoreSystemsProgram
  { coreProgramLabel = "presentation-only"
  , coreProgramProfile = CheckedRuntime
  , coreProgramFunctions = Map.singleton "Alpha" alphaFunction
  , coreProgramFacts = Map.singleton "source.checked" Nothing
  }

alphaFunction :: CoreSystemsFunction
alphaFunction = CoreSystemsFunction
  { coreFunctionKey = "Alpha"
  , coreFunctionEntry = "entry"
  , coreFunctionValues = Map.empty
  , coreFunctionBlocks = Map.singleton "entry"
      (CoreSystemsBlock "entry" [CoreTrace "source.checked"] (CoreSystemsEnd "return"))
  }

contextA :: GenericRealizationContext
contextA = context "context.source-systems.a" "realization:source-systems.a"

contextB :: GenericRealizationContext
contextB = context "context.source-systems.b" "realization:source-systems.b"

context :: Text -> Text -> GenericRealizationContext
context revision realizationRef = GenericRealizationContext
  { genericContextRevision = revision
  , genericContextSemantics = SemanticRecord (Map.fromList
      [ ("target", SemanticAtom "test-host")
      , ("path", SemanticAtom "corresponded-source")
      ])
  , genericContextVerifierProfile = "phase1-stage-verifier.v1"
  , genericContextRealizationRefs = Set.singleton realizationRef
  , genericContextQualificationRefs = Set.empty
  , genericContextAssumptions = Set.empty
  , genericContextDecisions = Map.empty
  , genericContextRuntimeSites = Map.empty
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
