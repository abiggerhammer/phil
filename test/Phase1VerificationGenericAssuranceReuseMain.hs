{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance
  ( ArtifactIdentity (..)
  , ArtifactRef (..)
  , Digest (..)
  )
import Phil.Core.Generic
  ( GenericApplicationIdentity
  , GenericDischargeLineage
  , GenericEvidence (..)
  , GenericRequirement (..)
  , GenericRequirementDisposition (..)
  , GenericStaticParameterKey (..)
  , checkGenericInstantiation
  , deriveGenericApplicationIdentity
  , deriveGenericDischargeLineage
  , genericDischargeApplicationIdentity
  , strictGenericInstantiationPolicy
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Core.Syntax (Proposition (..))
import Phil.Verification.GenericAssurance
  ( GenericApplicationAssurance
  , GenericAssuranceReuseError (..)
  , GenericBodyAssuranceError (..)
  , ReusableGenericBodyAssurance
  , composeGenericApplicationAssurance
  , deriveGenericPublicRequirementRevision
  , genericApplicationAssuranceBody
  , genericApplicationAssuranceLineage
  , prepareReusableGenericBodyAssurance
  , reusableGenericBodyAssuranceId
  , reusableGenericBodyEvidenceArtifact
  , reusableGenericBodyRequirementRevisions
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  body <- bodyOrFail bodyEvidenceArtifact
  applicationA <- applicationOrFail interfaceRevision "Blob"
  applicationB <- applicationOrFail interfaceRevision "Packet"
  lineageA <- lineageOrFail applicationA definitionRevision "proof.app.a"
  lineageB <- lineageOrFail applicationB definitionRevision "proof.app.b"
  compositionA <- compositionOrFail body publicRequirements lineageA
  compositionB <- compositionOrFail body publicRequirements lineageB
  let checks =
        [ ("two ordinary applications share one exact generic-body assurance artifact",
            testSharedBody body compositionA compositionB)
        , ("each application retains its own exact discharge lineage",
            testIndependentLineage compositionA compositionB)
        , ("changing one application discharge does not invalidate shared body or sibling application",
            testApplicationDischargeIndependence body compositionB applicationA)
        , ("generic definition revision change invalidates body reuse",
            testDefinitionRevisionInvalidation body applicationA)
        , ("generic interface revision change invalidates body reuse",
            testInterfaceRevisionInvalidation body)
        , ("public requirement revision change invalidates body reuse",
            testRequirementRevisionInvalidation body lineageA)
        , ("public requirement revisions are content-bound to generic interface identity",
            testRequirementRevisionIdentity)
        , ("body evidence artifact digest changes body assurance identity",
            testBodyEvidenceIdentity body)
        , ("monomorphization/backend choice does not duplicate source body assurance",
            testRealizationNonsemantic body)
        , ("malformed body artifact identity rejects before reuse",
            testMalformedBodyArtifact)
        ]
  mapM_ report checks
  unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-009 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-009 " ++ label)

bodyOrFail :: ArtifactIdentity -> IO ReusableGenericBodyAssurance
bodyOrFail artifact =
  case prepareReusableGenericBodyAssurance
      genericDeclarationKey
      interfaceRevision
      definitionRevision
      publicRequirements
      artifact of
    Left errorValue -> failCase ("could not prepare generic body assurance: " ++ show errorValue)
    Right body -> pure body

applicationOrFail :: InterfaceRevision -> Text.Text -> IO GenericApplicationIdentity
applicationOrFail applicationInterface typeActual =
  case deriveGenericApplicationIdentity
      genericDeclarationKey
      applicationInterface
      [(typeParameter, SemanticAtom typeActual)] of
    Left errorValue -> failCase ("could not derive generic application: " ++ show errorValue)
    Right application -> pure application

lineageOrFail
  :: GenericApplicationIdentity
  -> DefinitionRevision
  -> Text.Text
  -> IO GenericDischargeLineage
lineageOrFail application applicationDefinition evidenceIdentity =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      publicRequirements
      [ ( lawRequirement
        , GenericSatisfiedByEvidence GenericEvidence
            { genericEvidenceProposition = orderingLaw
            , genericEvidenceIdentity = evidenceIdentity
            }
        )
      ] of
    Left errorValue -> failCase ("could not check generic requirement discharge: " ++ show errorValue)
    Right record -> pure
      (deriveGenericDischargeLineage application applicationDefinition record)

compositionOrFail
  :: ReusableGenericBodyAssurance
  -> Set.Set GenericRequirement
  -> GenericDischargeLineage
  -> IO GenericApplicationAssurance
compositionOrFail body requirements lineage =
  case composeGenericApplicationAssurance body requirements lineage of
    Left errorValue -> failCase ("could not compose generic assurance: " ++ show errorValue)
    Right composition -> pure composition

failCase :: String -> IO a
failCase message = putStrLn ("FAIL: VER-009 " ++ message) >> exitFailure

testSharedBody
  :: ReusableGenericBodyAssurance
  -> GenericApplicationAssurance
  -> GenericApplicationAssurance
  -> Bool
testSharedBody body compositionA compositionB =
  genericApplicationAssuranceBody compositionA == body
    && genericApplicationAssuranceBody compositionB == body
    && reusableGenericBodyAssuranceId (genericApplicationAssuranceBody compositionA)
      == reusableGenericBodyAssuranceId (genericApplicationAssuranceBody compositionB)

testIndependentLineage
  :: GenericApplicationAssurance
  -> GenericApplicationAssurance
  -> Bool
testIndependentLineage compositionA compositionB =
  let lineageA = genericApplicationAssuranceLineage compositionA
      lineageB = genericApplicationAssuranceLineage compositionB
  in lineageA /= lineageB
      && genericDischargeApplicationIdentity lineageA
        /= genericDischargeApplicationIdentity lineageB

testApplicationDischargeIndependence
  :: ReusableGenericBodyAssurance
  -> GenericApplicationAssurance
  -> GenericApplicationIdentity
  -> Bool
testApplicationDischargeIndependence body siblingComposition applicationA =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      publicRequirements
      [ ( lawRequirement
        , GenericSatisfiedByEvidence GenericEvidence
            { genericEvidenceProposition = orderingLaw
            , genericEvidenceIdentity = "proof.app.a.replacement"
            }
        )
      ] of
    Left _ -> False
    Right replacementRecord ->
      let replacementLineage =
            deriveGenericDischargeLineage applicationA definitionRevision replacementRecord
      in case composeGenericApplicationAssurance body publicRequirements replacementLineage of
          Left _ -> False
          Right replacementComposition ->
            genericApplicationAssuranceBody replacementComposition == body
              && reusableGenericBodyAssuranceId
                  (genericApplicationAssuranceBody replacementComposition)
                == reusableGenericBodyAssuranceId body
              && genericApplicationAssuranceLineage replacementComposition
                /= genericApplicationAssuranceLineage siblingComposition
              && genericApplicationAssuranceBody siblingComposition == body

testDefinitionRevisionInvalidation
  :: ReusableGenericBodyAssurance
  -> GenericApplicationIdentity
  -> Bool
testDefinitionRevisionInvalidation body application =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      publicRequirements
      [ ( lawRequirement
        , GenericSatisfiedByEvidence GenericEvidence
            { genericEvidenceProposition = orderingLaw
            , genericEvidenceIdentity = "proof.definition.changed"
            }
        )
      ] of
    Left _ -> False
    Right record ->
      let changedDefinition = DefinitionRevision "generic.map.definition.v2"
          changedLineage = deriveGenericDischargeLineage application changedDefinition record
      in composeGenericApplicationAssurance body publicRequirements changedLineage
          == Left
              (GenericAssuranceDefinitionMismatch
                definitionRevision
                changedDefinition)

testInterfaceRevisionInvalidation :: ReusableGenericBodyAssurance -> Bool
testInterfaceRevisionInvalidation body =
  case deriveGenericApplicationIdentity
      genericDeclarationKey
      changedInterfaceRevision
      [(typeParameter, SemanticAtom "Blob")] of
    Left _ -> False
    Right application ->
      case checkGenericInstantiation
          strictGenericInstantiationPolicy
          publicRequirements
          [ ( lawRequirement
            , GenericSatisfiedByEvidence GenericEvidence
                { genericEvidenceProposition = orderingLaw
                , genericEvidenceIdentity = "proof.interface.changed"
                }
            )
          ] of
        Left _ -> False
        Right record ->
          let lineage = deriveGenericDischargeLineage application definitionRevision record
          in composeGenericApplicationAssurance body publicRequirements lineage
              == Left
                  (GenericAssuranceInterfaceMismatch
                    interfaceRevision
                    changedInterfaceRevision)

testRequirementRevisionInvalidation
  :: ReusableGenericBodyAssurance
  -> GenericDischargeLineage
  -> Bool
testRequirementRevisionInvalidation body lineage =
  let changedRequirements = Set.insert extraRequirement publicRequirements
      expected = reusableGenericBodyRequirementRevisions body
      actual = Map.fromSet
        (deriveGenericPublicRequirementRevision genericDeclarationKey interfaceRevision)
        changedRequirements
  in composeGenericApplicationAssurance body changedRequirements lineage
      == Left
          (GenericAssurancePublicRequirementRevisionMismatch expected actual)

testRequirementRevisionIdentity :: Bool
testRequirementRevisionIdentity =
  deriveGenericPublicRequirementRevision
      genericDeclarationKey
      interfaceRevision
      lawRequirement
    /= deriveGenericPublicRequirementRevision
      genericDeclarationKey
      changedInterfaceRevision
      lawRequirement

testBodyEvidenceIdentity :: ReusableGenericBodyAssurance -> Bool
testBodyEvidenceIdentity body =
  let replacementArtifact = bodyEvidenceArtifact
        { artifactDigest = Digest "sha256.generic.body.v2" }
  in case prepareReusableGenericBodyAssurance
      genericDeclarationKey
      interfaceRevision
      definitionRevision
      publicRequirements
      replacementArtifact of
    Left _ -> False
    Right replacement ->
      reusableGenericBodyAssuranceId replacement /= reusableGenericBodyAssuranceId body
        && reusableGenericBodyEvidenceArtifact replacement == replacementArtifact

testRealizationNonsemantic :: ReusableGenericBodyAssurance -> Bool
testRealizationNonsemantic body =
  case (prepareForRealization "native.mono.blob", prepareForRealization "wasm.mono.blob") of
    (Right nativeBody, Right wasmBody) ->
      nativeBody == body
        && wasmBody == body
        && reusableGenericBodyAssuranceId nativeBody
          == reusableGenericBodyAssuranceId wasmBody
    _ -> False
  where
    prepareForRealization _ = prepareReusableGenericBodyAssurance
      genericDeclarationKey
      interfaceRevision
      definitionRevision
      publicRequirements
      bodyEvidenceArtifact

testMalformedBodyArtifact :: Bool
testMalformedBodyArtifact =
  let emptyReference = bodyEvidenceArtifact { artifactReference = ArtifactRef "" }
      emptyDigest = bodyEvidenceArtifact { artifactDigest = Digest "" }
      prepare artifact = prepareReusableGenericBodyAssurance
        genericDeclarationKey
        interfaceRevision
        definitionRevision
        publicRequirements
        artifact
  in prepare emptyReference == Left GenericBodyAssuranceEmptyArtifactReference
      && prepare emptyDigest == Left GenericBodyAssuranceEmptyArtifactDigest

genericDeclarationKey :: DeclarationKey
genericDeclarationKey = DeclarationKey "generic.map"

interfaceRevision :: InterfaceRevision
interfaceRevision = InterfaceRevision "generic.map.interface.v1"

changedInterfaceRevision :: InterfaceRevision
changedInterfaceRevision = InterfaceRevision "generic.map.interface.v2"

definitionRevision :: DefinitionRevision
definitionRevision = DefinitionRevision "generic.map.definition.v1"

typeParameter :: GenericStaticParameterKey
typeParameter = GenericStaticParameterKey "T"

orderingLaw :: Proposition
orderingLaw = Atom "StrictWeakOrdering" []

lawRequirement :: GenericRequirement
lawRequirement = GenericPropositionRequirement orderingLaw

extraRequirement :: GenericRequirement
extraRequirement = GenericPropositionRequirement (Atom "StableHash" [])

publicRequirements :: Set.Set GenericRequirement
publicRequirements = Set.singleton lawRequirement

bodyEvidenceArtifact :: ArtifactIdentity
bodyEvidenceArtifact = ArtifactIdentity
  { artifactReference = ArtifactRef "proof.generic.map.body.v1"
  , artifactDigest = Digest "sha256.generic.map.body.v1"
  }
