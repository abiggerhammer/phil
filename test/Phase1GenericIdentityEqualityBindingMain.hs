{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Generic
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Core.Syntax (Proposition (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "equal application facts compare equal" equalApplication
    , test "argument map order is extensional" reorderedArgumentsEqual
    , test "declaration key changes application" declarationChangesApplication
    , test "interface revision changes application" interfaceChangesApplication
    , test "semantic argument changes application" argumentChangesApplication
    , test "equal discharge lineage compares equal" equalLineage
    , test "definition revision changes lineage" definitionChangesLineage
    , test "discharge evidence changes lineage" evidenceChangesLineage
    , test "application change changes lineage" applicationChangesLineage
    , test "application Eq agrees with Ord" applicationEqOrdAgreement
    , test "lineage Eq agrees with Ord" lineageEqOrdAgreement
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

equalApplication :: Either String ()
equalApplication = assert (applicationA == applicationA) "application was not reflexive"

reorderedArgumentsEqual :: Either String ()
reorderedArgumentsEqual =
  assert (applicationA == applicationReordered)
    "canonical Map equality depended on insertion order"

declarationChangesApplication :: Either String ()
declarationChangesApplication =
  assert (applicationA /= applicationDifferentDeclaration)
    "declaration key difference was ignored"

interfaceChangesApplication :: Either String ()
interfaceChangesApplication =
  assert (applicationA /= applicationDifferentInterface)
    "interface revision difference was ignored"

argumentChangesApplication :: Either String ()
argumentChangesApplication =
  assert (applicationA /= applicationDifferentArgument)
    "semantic argument difference was ignored"

equalLineage :: Either String ()
equalLineage = assert (lineageA == lineageA) "lineage was not reflexive"

definitionChangesLineage :: Either String ()
definitionChangesLineage =
  assert (lineageA /= lineageDifferentDefinition)
    "definition revision difference was ignored"

evidenceChangesLineage :: Either String ()
evidenceChangesLineage =
  assert (lineageA /= lineageDifferentEvidence)
    "discharge evidence difference was ignored"

applicationChangesLineage :: Either String ()
applicationChangesLineage =
  assert (lineageA /= lineageDifferentApplication)
    "semantic application difference was ignored in lineage"

applicationEqOrdAgreement :: Either String ()
applicationEqOrdAgreement =
  assert
    ((applicationA == applicationReordered)
      == (compare applicationA applicationReordered == EQ))
    "application Eq and Ord disagree"

lineageEqOrdAgreement :: Either String ()
lineageEqOrdAgreement =
  assert
    ((lineageA == lineageA) == (compare lineageA lineageA == EQ))
    "lineage Eq and Ord disagree"

applicationA :: GenericApplicationIdentity
applicationA = GenericApplicationIdentity
  declarationA
  interfaceA
  (Map.fromList
    [ (parameterA, SemanticAtom "Blob")
    , (parameterB, SemanticAtom "provider.compare.v1")
    ])

applicationReordered :: GenericApplicationIdentity
applicationReordered = GenericApplicationIdentity
  declarationA
  interfaceA
  (Map.fromList
    [ (parameterB, SemanticAtom "provider.compare.v1")
    , (parameterA, SemanticAtom "Blob")
    ])

applicationDifferentDeclaration :: GenericApplicationIdentity
applicationDifferentDeclaration =
  applicationA { genericApplicationDeclarationKey = declarationB }

applicationDifferentInterface :: GenericApplicationIdentity
applicationDifferentInterface =
  applicationA { genericApplicationInterfaceRevision = interfaceB }

applicationDifferentArgument :: GenericApplicationIdentity
applicationDifferentArgument = GenericApplicationIdentity
  declarationA
  interfaceA
  (Map.fromList
    [ (parameterA, SemanticAtom "OtherBlob")
    , (parameterB, SemanticAtom "provider.compare.v1")
    ])

lineageA :: GenericDischargeLineage
lineageA = GenericDischargeLineage applicationA definitionA Map.empty

lineageDifferentDefinition :: GenericDischargeLineage
lineageDifferentDefinition = GenericDischargeLineage applicationA definitionB Map.empty

lineageDifferentEvidence :: GenericDischargeLineage
lineageDifferentEvidence = GenericDischargeLineage
  applicationA
  definitionA
  (Map.singleton evidenceRequirement (GenericExported "proof.changed"))

lineageDifferentApplication :: GenericDischargeLineage
lineageDifferentApplication = GenericDischargeLineage
  applicationDifferentArgument
  definitionA
  Map.empty

declarationA, declarationB :: DeclarationKey
declarationA = DeclarationKey "generic.map"
declarationB = DeclarationKey "generic.filter"

interfaceA, interfaceB :: InterfaceRevision
interfaceA = InterfaceRevision "generic.map.interface.v1"
interfaceB = InterfaceRevision "generic.map.interface.v2"

definitionA, definitionB :: DefinitionRevision
definitionA = DefinitionRevision "generic.map.definition.v1"
definitionB = DefinitionRevision "generic.map.definition.v2"

parameterA, parameterB :: GenericStaticParameterKey
parameterA = GenericStaticParameterKey "T"
parameterB = GenericStaticParameterKey "P"

evidenceRequirement :: GenericRequirement
evidenceRequirement = GenericPropositionRequirement (Atom "Ordering" [])
