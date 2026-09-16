{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , CheckedArchitectureInstance (..)
  , DeclarationIdentity (..)
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
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "ordinary checked source derives exact persisted architecture identity"
        exactArchitectureAccepts
    , test "carrier and whitespace variation preserve architecture identity"
        carrierWhitespaceInvariant
    , test "component display rename preserves semantic identity"
        componentRenameInvariant
    , test "body semantic change revises definition but not interface"
        bodyChangeRevisesDefinition
    , test "public provides change revises interface"
        interfaceChangeRevisesInterface
    , test "persisted instance lineage change rekeys occurrence only"
        instanceLineageRekeysOccurrence
    , test "missing root-to-instance binding rejects"
        missingRootBindingRejects
    , test "unknown persisted instance site rejects"
        unknownInstanceSiteRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactArchitectureAccepts :: Either String ()
exactArchitectureAccepts = do
  architecture <- compileArchitecture unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:demo" unitEnvironment
  assert
    (checkedSourceArchitectureInstanceKey architecture == InstanceKey "inst:demo")
    "selected architecture did not retain persisted InstanceKey"
  assert
    (identityDeclarationKey (checkedSourceArchitectureDeclaration architecture)
      == DeclarationKey "decl:demo")
    "selected architecture did not retain persisted DeclarationKey"

carrierWhitespaceInvariant :: Either String ()
carrierWhitespaceInvariant = do
  left <- compileArchitecture unitSource "unit.left" "site.demo" "decl:demo"
    "instance.demo" "inst:demo" unitEnvironment
  right <- compileArchitecture
    "component   Alpha   provides Unit   {   return   unit   }"
    "unit.right" "site.demo" "decl:demo" "instance.demo" "inst:demo"
    unitEnvironment
  assert
    (checkedSourceArchitectureDeclaration left == checkedSourceArchitectureDeclaration right)
    "carrier/whitespace variation changed declaration identity"
  assert
    (checkedArchitectureIdentityOf left == checkedArchitectureIdentityOf right)
    "carrier/whitespace variation changed architecture occurrence identity"

componentRenameInvariant :: Either String ()
componentRenameInvariant = do
  left <- compileArchitecture unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:demo" unitEnvironment
  right <- compileArchitecture
    "component Renamed provides Unit { return unit }"
    "unit.demo" "site.demo" "decl:demo" "instance.demo" "inst:demo"
    unitEnvironment
  assert
    (checkedSourceArchitectureDeclaration left == checkedSourceArchitectureDeclaration right)
    "component display rename changed declaration semantic identity"

bodyChangeRevisesDefinition :: Either String ()
bodyChangeRevisesDefinition = do
  left <- compileArchitecture unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:demo" unitEnvironment
  right <- compileArchitecture
    "component Alpha provides Unit { let x = unit return x }"
    "unit.demo" "site.demo" "decl:demo" "instance.demo" "inst:demo"
    unitEnvironment
  let leftIdentity = checkedSourceArchitectureDeclaration left
      rightIdentity = checkedSourceArchitectureDeclaration right
  assert
    (identityInterfaceRevision leftIdentity == identityInterfaceRevision rightIdentity)
    "body-only semantic change revised interface identity"
  assert
    (identityDefinitionRevision leftIdentity /= identityDefinitionRevision rightIdentity)
    "body semantic change did not revise definition identity"

interfaceChangeRevisesInterface :: Either String ()
interfaceChangeRevisesInterface = do
  left <- compileArchitecture unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:demo" unitEnvironment
  right <- compileArchitecture
    "component Alpha provides Bool { return true }"
    "unit.demo" "site.demo" "decl:demo" "instance.demo" "inst:demo"
    boolEnvironment
  assert
    (identityInterfaceRevision (checkedSourceArchitectureDeclaration left)
      /= identityInterfaceRevision (checkedSourceArchitectureDeclaration right))
    "public provides change did not revise interface identity"

instanceLineageRekeysOccurrence :: Either String ()
instanceLineageRekeysOccurrence = do
  left <- compileArchitecture unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:one" unitEnvironment
  right <- compileArchitecture unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:two" unitEnvironment
  assert
    (checkedSourceArchitectureDeclaration left == checkedSourceArchitectureDeclaration right)
    "instance lineage change incorrectly changed declaration identity"
  assert
    (checkedArchitectureIdentityOf left /= checkedArchitectureIdentityOf right)
    "instance lineage change did not rekey architecture occurrence"

missingRootBindingRejects :: Either String ()
missingRootBindingRejects = do
  checked <- compileChecked unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:demo" unitEnvironment
  case buildCheckedSourceArchitecture Map.empty checked of
    Left (SourceArchitectureRootBindingMissing "program:demo") -> Right ()
    other -> Left ("missing root binding did not reject exactly: " <> show other)

unknownInstanceSiteRejects :: Either String ()
unknownInstanceSiteRejects = do
  checked <- compileChecked unitSource "unit.demo" "site.demo" "decl:demo"
    "instance.demo" "inst:demo" unitEnvironment
  let roots = Map.singleton "program:demo" (InstanceLineageSiteId "instance.unknown")
  case buildCheckedSourceArchitecture roots checked of
    Left (SourceArchitectureInstanceLineageMissing
      (InstanceLineageSiteId "instance.unknown")) -> Right ()
    other -> Left ("unknown instance site did not reject exactly: " <> show other)

compileArchitecture
  :: Text -> Text -> Text -> Text -> Text -> Text -> SurfaceEnvironment
  -> Either String CheckedSourceArchitecture
compileArchitecture source unitId declarationSite declarationKey instanceSite instanceKey environment = do
  checked <- compileChecked source unitId declarationSite declarationKey
    instanceSite instanceKey environment
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:demo" (InstanceLineageSiteId instanceSite)) checked

compileChecked
  :: Text -> Text -> Text -> Text -> Text -> Text -> SurfaceEnvironment
  -> Either String CheckedSourceBundle
compileChecked source unitId declarationSite declarationKey instanceSite instanceKey environment = do
  bundle <- mapLeft show $ decodePortableSourceBundle
    (bundleText source unitId declarationSite declarationKey instanceSite instanceKey)
  let roots = Map.singleton "program:demo" (DeclarationKey declarationKey)
      environments = Map.singleton (DeclarationKey declarationKey) environment
  mapLeft show $ checkPortableSourceBundle roots environments bundle

bundleText :: Text -> Text -> Text -> Text -> Text -> Text -> Text
bundleText source unitId declarationSite declarationKey instanceSite instanceKey =
  Text.unlines
    [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
    , "grammar\t" <> unGrammarRevision canonicalGrammarRevisionV1
    , "root\tprogram:demo"
    , Text.intercalate "\t"
        ["unit", unitId, declarationSite, declarationKey, source]
    , Text.intercalate "\t"
        ["instance", instanceSite, instanceKey]
    ]

unitEnvironment :: SurfaceEnvironment
unitEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceExpectedProvides = Just TyUnit }

boolEnvironment :: SurfaceEnvironment
boolEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceExpectedProvides = Just TyBool }

unitSource :: Text
unitSource = "component Alpha provides Unit { return unit }"

checkedArchitectureIdentityOf :: CheckedSourceArchitecture -> ArchitectureInstanceIdentity
checkedArchitectureIdentityOf = checkedArchitectureIdentity . checkedSourceArchitectureRoot

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
