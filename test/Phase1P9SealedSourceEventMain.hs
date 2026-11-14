{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCorePolicy (emptySourceCoreCorrespondencePolicy)
import Phil.Compiler.SourceSystems
import Phil.Core.Static
  ( DeclarationKey (..), SemanticForm (..), emptyStaticContext )
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.Check
  ( SourceEvidenceEvent (..), SourceEvidenceUse (..)
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.Lineage
  ( DeclarationSiteId (..), InstanceLineageSiteId (..)
  , PortableInstanceLineage (..), PortableSourceBundle (..)
  , PortableSourceUnit (..), SourceUnitId (..), canonicalGrammarRevisionV1 )
import Phil.Systems.GenericLowering
  ( CoreSystemsBlock (..), CoreSystemsFunction (..)
  , CoreSystemsOperation (..), CoreSystemsProgram (..)
  , CoreSystemsTerminator (..), GenericRealizationContext (..)
  , coreSystemsProgramSemanticForm )
import Phil.Systems.IR (CompilationProfile (CheckedRuntime))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ check "P2 sealed original source event with unit, declaration and exact Core" checkedProof
    , check "same K/I and Core cannot substitute relocated checker event" relocatedUse
    , check "valid source with no evidence has no alleged final use" emptyUse
    , check "rejected original proof cannot mint sealed source graph" invalidProof
    , check "different Core function domain fails before event graph sealing" wrongCore
    ]
  unless (and results) exitFailure

check :: String -> Either String () -> IO Bool
check label outcome = case outcome of
  Right () -> putStrLn ("PASS: P9-E2 " ++ label) >> pure True
  Left detail -> putStrLn ("FAIL: P9-E2 " ++ label ++ ": " ++ detail) >> pure False

sourceBundle :: Text -> PortableSourceBundle
sourceBundle source = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:demo"
  , portableSourceUnits =
      [ PortableSourceUnit (SourceUnitId "unit.p9.demo")
          (DeclarationSiteId "site.p9.demo") (Just "decl:p9.demo") source ]
  , portableInstanceLineage =
      [ PortableInstanceLineage (InstanceLineageSiteId "instance.p9.demo")
          "inst:p9.demo" ]
  , portableProcessLineage = []
  }

sourceEnvironment :: SurfaceEnvironment
sourceEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceExpectedProvides = Just TyUnit }

sourceCore :: CoreSystemsProgram
sourceCore = CoreSystemsProgram
  { coreProgramLabel = "p9-observation-not-core-authority"
  , coreProgramProfile = CheckedRuntime
  , coreProgramFunctions = Map.singleton "Alpha"
      (CoreSystemsFunction "Alpha" "entry" Map.empty
        (Map.singleton "entry"
          (CoreSystemsBlock "entry" [CoreTrace "source.checked"]
            (CoreSystemsEnd "return"))))
  , coreProgramFacts = Map.singleton "source.checked" Nothing
  }

sourceContext :: GenericRealizationContext
sourceContext = GenericRealizationContext
  { genericContextRevision = "p9-e2.source-context.v1"
  , genericContextSemantics = SemanticAtom "p9-e2-fixed-context"
  , genericContextVerifierProfile = "phase1-stage-verifier.v1"
  , genericContextRealizationRefs = Set.singleton "realization:p9-e2"
  , genericContextQualificationRefs = Set.empty
  , genericContextAssumptions = Set.empty
  , genericContextDecisions = Map.empty
  , genericContextRuntimeSites = Map.empty
  }

produce :: Text -> CoreSystemsProgram -> Either String VerifiedSourceSystemsProduction
produce source core = mapLeft show $
  produceVerifiedSourceSystems
    (Map.singleton "program:demo" (DeclarationKey "decl:p9.demo"))
    (Map.singleton (DeclarationKey "decl:p9.demo") sourceEnvironment)
    (Map.singleton "program:demo" (InstanceLineageSiteId "instance.p9.demo"))
    emptySourceCoreCorrespondencePolicy
    (sourceBundle source) core sourceContext

ordinary :: Text
ordinary = "component Alpha provides Unit { prove true\n return unit }"

eventFor :: VerifiedSourceSystemsProduction -> Either String SourceEvidenceEvent
eventFor production = case verifiedSourceCheckEventOccurrences
    (verifiedSourceSystemsCheckEventGraph production) of
  [qualified] -> do
    require (checkedEvidenceUnitId qualified == SourceUnitId "unit.p9.demo")
      "wrong persisted source unit"
    require (checkedEvidenceDeclarationSite qualified == DeclarationSiteId "site.p9.demo")
      "wrong persisted declaration site"
    require (checkedEvidenceDeclarationKey qualified == DeclarationKey "decl:p9.demo")
      "wrong persisted declaration key"
    let event = checkedEvidenceEvent qualified
    case sourceEvidenceUse event of
      SourceProveEvidence _ _ -> Right event
      other -> Left ("unexpected checker event: " ++ show other)
  others -> Left ("wrong exact observed event inventory: " ++ show others)

checkedProof :: Either String ()
checkedProof = do
  production <- produce ordinary sourceCore
  _ <- eventFor production
  let graph = verifiedSourceSystemsCheckEventGraph production
  require
    (verifiedSourceCheckEventArchitectureIdentity graph
       == verifiedSourceSystemsArchitectureIdentity production)
    "graph did not seal P2 K/I"
  require (verifiedSourceCheckEventCoreSemantics graph
       == coreSystemsProgramSemanticForm sourceCore)
    "graph did not seal actual admitted whole-Core semantic identity"

relocatedUse :: Either String ()
relocatedUse = do
  before <- produce ordinary sourceCore
  after <- produce
    "component Alpha provides Unit {\n prove true\n return unit }" sourceCore
  beforeEvent <- eventFor before
  afterEvent <- eventFor after
  require
    (verifiedSourceSystemsArchitectureIdentity before
       == verifiedSourceSystemsArchitectureIdentity after)
    "whitespace-only relocation unexpectedly changed semantic K/I"
  require
    (verifiedSourceCheckEventCoreSemantics
       (verifiedSourceSystemsCheckEventGraph before)
       == verifiedSourceCheckEventCoreSemantics
            (verifiedSourceSystemsCheckEventGraph after))
    "whitespace-only source changed admitted Core"
  require (sourceEvidenceSite beforeEvent /= sourceEvidenceSite afterEvent)
    "same-K/I but relocated original event did not preserve its distinct site"
  require
    (verifiedSourceSystemsCheckEventGraph before
       /= verifiedSourceSystemsCheckEventGraph after)
    "distinct original events collapsed into one source-owned graph"

emptyUse :: Either String ()
emptyUse = do
  production <- produce "component Alpha provides Unit { return unit }" sourceCore
  require (null (verifiedSourceCheckEventOccurrences
    (verifiedSourceSystemsCheckEventGraph production)))
    "no-use source fabricated a purported checked evidence use"

invalidProof :: Either String ()
invalidProof =
  case produce "component Alpha provides Unit { prove false\n return unit }"
      sourceCore of
    Left _ -> Right ()
    Right _ -> Left "unproved false proof was accepted into the source graph"

wrongCore :: Either String ()
wrongCore =
  let badFunction = CoreSystemsFunction "Beta" "entry" Map.empty
        (Map.singleton "entry"
          (CoreSystemsBlock "entry" [CoreTrace "source.checked"]
            (CoreSystemsEnd "return")))
      bad = sourceCore
        { coreProgramFunctions = Map.singleton "Beta" badFunction }
  in case produce ordinary bad of
      Left _ -> Right ()
      Right _ -> Left "wrong Core function identity was sealed with source uses"

require :: Bool -> String -> Either String ()
require condition msg
  | condition = Right ()
  | otherwise = Left msg

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
