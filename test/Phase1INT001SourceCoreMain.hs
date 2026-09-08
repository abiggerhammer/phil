{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCore
import Phil.Core.Static
  ( ArchitectureInstanceIdentity
  , DeclarationKey (..)
  , InstanceKey (..)
  , emptyStaticContext
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
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import Phil.Systems.GenericLowering
import Phil.Systems.IR (CompilationProfile (CheckedRuntime))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "checked source corresponds to exact Core function and terminal"
        exactCorrespondenceAccepts
    , test "Core program label is not witness identity"
        coreLabelRenameInvariant
    , test "swapped Core function set rejects"
        functionSetMismatchRejects
    , test "map key cannot hide mismatched embedded Core function identity"
        embeddedFunctionKeyMismatchRejects
    , test "source return cannot correspond to fatal-only Core terminal"
        returnTerminalMismatchRejects
    , test "post-check exact-transfer mutation is detected by independent inventory"
        exactTransferUnderrepresentationRejects
    , test "correspondence retains exact source Architecture identity"
        architectureIdentityRetained
    , test "Core semantic mutation changes bound correspondence semantics"
        coreSemanticMutationChangesBinding
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactCorrespondenceAccepts :: Either String ()
exactCorrespondenceAccepts = do
  architecture <- checkedArchitecture
  correspondence <- mapLeft show $
    verifySourceCoreCorrespondence architecture goodCore
  assert
    (Map.keysSet (sourceCoreSourceDefinitions correspondence)
      == Map.keysSet (coreProgramFunctions goodCore))
    "accepted correspondence lost exact source/Core function domain"

coreLabelRenameInvariant :: Either String ()
coreLabelRenameInvariant = do
  architecture <- checkedArchitecture
  left <- mapLeft show $ verifySourceCoreCorrespondence architecture goodCore
  right <- mapLeft show $ verifySourceCoreCorrespondence architecture
    goodCore { coreProgramLabel = "presentation-only-renamed" }
  assert
    (sourceCoreProgramSemantics left == sourceCoreProgramSemantics right)
    "Core presentation label changed semantic correspondence identity"

functionSetMismatchRejects :: Either String ()
functionSetMismatchRejects = do
  architecture <- checkedArchitecture
  let foreignFunction = alphaFunction { coreFunctionKey = "Beta" }
      swapped = goodCore
        { coreProgramFunctions = Map.singleton "Beta" foreignFunction }
  case verifySourceCoreCorrespondence architecture swapped of
    Left (SourceCoreFunctionSetMismatch expected actual) ->
      assert (expected /= actual) "function-set mismatch diagnostic lost mismatch"
    other -> Left ("swapped Core function set crossed correspondence boundary: " <> show other)

embeddedFunctionKeyMismatchRejects :: Either String ()
embeddedFunctionKeyMismatchRejects = do
  architecture <- checkedArchitecture
  let tampered = goodCore
        { coreProgramFunctions = Map.singleton "Alpha"
            (alphaFunction { coreFunctionKey = "Beta" }) }
  case verifySourceCoreCorrespondence architecture tampered of
    Left (SourceCoreFunctionKeyMismatch "Alpha" "Beta") -> Right ()
    other -> Left ("embedded function-key mismatch crossed boundary: " <> show other)

returnTerminalMismatchRejects :: Either String ()
returnTerminalMismatchRejects = do
  architecture <- checkedArchitecture
  let fatalFunction = alphaFunction
        { coreFunctionBlocks = Map.singleton "entry"
            (CoreSystemsBlock "entry" [] (CoreSystemsFatal "tampered")) }
      tampered = goodCore
        { coreProgramFunctions = Map.singleton "Alpha" fatalFunction }
  case verifySourceCoreCorrespondence architecture tampered of
    Left (SourceCoreReturnTerminalMissing "Alpha") -> Right ()
    other -> Left ("fatal-only Core accepted for returning source: " <> show other)

exactTransferUnderrepresentationRejects :: Either String ()
exactTransferUnderrepresentationRejects = do
  architecture0 <- checkedArchitecture
  mutatedComponent <- parseSingle
    "component Alpha provides Unit { send_exact payload on session0 return unit }"
  let checkedBundle0 = checkedSourceArchitectureBundle architecture0
      [unit0] = checkedSourceUnits checkedBundle0
      unit1 = unit0 { checkedSourceComponent = mutatedComponent }
      checkedBundle1 = checkedBundle0 { checkedSourceUnits = [unit1] }
      architecture1 = architecture0
        { checkedSourceArchitectureBundle = checkedBundle1 }
  case verifySourceCoreCorrespondence architecture1 goodCore of
    Left (SourceCoreInventoryUnderrepresented "Alpha" expected actual) ->
      assert
        (sourceCoreSendExact expected == 1 && sourceCoreSendExact actual == 0)
        "exact-transfer mismatch lost independent inventory counts"
    other -> Left ("underrepresented exact transfer crossed boundary: " <> show other)

architectureIdentityRetained :: Either String ()
architectureIdentityRetained = do
  architecture <- checkedArchitecture
  correspondence <- mapLeft show $
    verifySourceCoreCorrespondence architecture goodCore
  assert
    (sourceCoreArchitectureIdentity correspondence == architectureIdentity architecture)
    "correspondence did not retain exact source-derived Architecture identity"

coreSemanticMutationChangesBinding :: Either String ()
coreSemanticMutationChangesBinding = do
  architecture <- checkedArchitecture
  left <- mapLeft show $ verifySourceCoreCorrespondence architecture goodCore
  right <- mapLeft show $ verifySourceCoreCorrespondence architecture
    goodCore { coreProgramFacts = Map.fromList
      [("source.checked", Nothing), ("extra.semantic.fact", Nothing)] }
  assert
    (sourceCoreProgramSemantics left /= sourceCoreProgramSemantics right)
    "Core semantic mutation was not reflected in bound correspondence semantics"

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
  { coreProgramLabel = "arbitrary-presentation"
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
      (CoreSystemsBlock "entry" [] (CoreSystemsEnd "return"))
  }

parseSingle :: Text -> Either String (Phil.Surface.Syntax.Located Phil.Surface.Syntax.Component)
parseSingle source = do
  parsed <- mapLeft show (parseSurfaceFile "mutation.phil" source)
  case parsed of
    SurfaceFile [component] -> Right component
    SurfaceFile components -> Left
      ("mutation fixture expected one component, found " <> show (length components))

architectureIdentity :: CheckedSourceArchitecture -> ArchitectureInstanceIdentity
architectureIdentity = Phil.Core.Static.checkedArchitectureIdentity . checkedSourceArchitectureRoot

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
