module Phil.Surface.GrammarV1.ReferenceAstRecordDataRepresentationBridge
  ( grammarV1RecordDataDeclarationToImplementation
  , grammarV1RecordDataDeclarationsToImplementation
  , grammarV1ProductionRecordDataDeclarationsToImplementation
  , grammarV1ReferenceGenericKindToImplementation
  , grammarV1ReferenceStructuralModeToImplementation
  , grammarV1ReferenceRequirementToImplementation
  ) where

import Data.Text (Text)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1SourceFile
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceFieldCore (..)
  , GrammarV1ReferenceGenericKindCore (..)
  , GrammarV1ReferenceGenericParamCore (..)
  , GrammarV1ReferenceRequirementCore (..)
  , GrammarV1ReferenceStructuralModeCore (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstRecordData
  ( GrammarV1ReferenceRecordDataDeclaration (..)
  , GrammarV1ReferenceVariantCore (..)
  , GrammarV1ReferenceVariantPayloadCore (..)
  , grammarV1ProductionRecordDataDeclarations
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( textToKernelString
  )
import qualified SurfaceGrammarAstRecordDataCarrierKernel as Representation
import qualified SurfaceGrammarRecognizerKernel as Recognizer

-- | Bind the shared record/data semantic view to the compact carrier extracted
-- from the #986 implementation representation.  This bridge intentionally
-- projects away recursive type/proposition/effect payload contents and
-- syntax-only distinctions not preserved by the production AST.
grammarV1RecordDataDeclarationToImplementation
  :: GrammarV1ReferenceRecordDataDeclaration
  -> Representation.Phase1SurfaceProductionRecordDataDeclaration
grammarV1RecordDataDeclarationToImplementation declaration = case declaration of
  GrammarV1ReferenceRecordDeclaration name params mode requirements fields ->
    Representation.phase1_surface_make_production_record
      (textToRepresentationString name)
      (map genericParamToImplementation params)
      (fmap grammarV1ReferenceStructuralModeToImplementation mode)
      (map grammarV1ReferenceRequirementToImplementation requirements)
      (map fieldNameToRepresentation fields)
  GrammarV1ReferenceDataDeclaration name params mode requirements variants ->
    Representation.phase1_surface_make_production_data
      (textToRepresentationString name)
      (map genericParamToImplementation params)
      (fmap grammarV1ReferenceStructuralModeToImplementation mode)
      (map grammarV1ReferenceRequirementToImplementation requirements)
      (map variantToImplementation variants)

grammarV1RecordDataDeclarationsToImplementation
  :: [GrammarV1ReferenceRecordDataDeclaration]
  -> [Representation.Phase1SurfaceProductionRecordDataDeclaration]
grammarV1RecordDataDeclarationsToImplementation =
  map grammarV1RecordDataDeclarationToImplementation

-- | Production entry point.  The existing stable record/data semantic view is
-- derived from the production AST first; this function then projects exactly
-- the subset certified by the compact extraction boundary.
grammarV1ProductionRecordDataDeclarationsToImplementation
  :: GrammarV1SourceFile
  -> [Representation.Phase1SurfaceProductionRecordDataDeclaration]
grammarV1ProductionRecordDataDeclarationsToImplementation =
  grammarV1RecordDataDeclarationsToImplementation
    . grammarV1ProductionRecordDataDeclarations

genericParamToImplementation
  :: GrammarV1ReferenceGenericParamCore
  -> Representation.Phase1SurfaceProductionGenericParam
genericParamToImplementation parameter =
  Representation.phase1_surface_make_production_generic_param
    (textToRepresentationString
      (grammarV1ReferenceGenericParamNameCore parameter))
    (grammarV1ReferenceGenericKindToImplementation
      (grammarV1ReferenceGenericParamKindCore parameter))

grammarV1ReferenceGenericKindToImplementation
  :: GrammarV1ReferenceGenericKindCore
  -> Representation.Phase1SurfaceProductionGenericKind
grammarV1ReferenceGenericKindToImplementation kind = case kind of
  GrammarV1ReferenceTypeKindCore ->
    Representation.Phase1ProductionTypeGenericKind
  GrammarV1ReferenceNatKindCore ->
    Representation.Phase1ProductionNatGenericKind
  GrammarV1ReferenceSessionKindCore ->
    Representation.Phase1ProductionSessionGenericKind
  GrammarV1ReferenceMessageKindCore ->
    Representation.Phase1ProductionMessageGenericKind
  GrammarV1ReferenceEffectsKindCore ->
    Representation.Phase1ProductionEffectsGenericKind
  GrammarV1ReferenceProviderKindCore _ ->
    Representation.Phase1ProductionProviderGenericKind
  GrammarV1ReferenceCallableKindCore _ ->
    Representation.Phase1ProductionCallableGenericKind
  GrammarV1ReferenceBoundaryKindCore _ ->
    Representation.Phase1ProductionBoundaryGenericKind
  GrammarV1ReferenceArchitectureKindCore _ ->
    Representation.Phase1ProductionArchitectureGenericKind

grammarV1ReferenceStructuralModeToImplementation
  :: GrammarV1ReferenceStructuralModeCore
  -> Representation.Phase1SurfaceProductionStructuralMode
grammarV1ReferenceStructuralModeToImplementation mode = case mode of
  GrammarV1ReferenceUnrestrictedMode ->
    Representation.Phase1ProductionUnrestrictedMode
  GrammarV1ReferenceAffineMode ->
    Representation.Phase1ProductionAffineMode
  GrammarV1ReferenceLinearMode ->
    Representation.Phase1ProductionLinearMode

grammarV1ReferenceRequirementToImplementation
  :: GrammarV1ReferenceRequirementCore
  -> Representation.Phase1SurfaceProductionRequirement
grammarV1ReferenceRequirementToImplementation requirement = case requirement of
  GrammarV1ReferenceStructuralRequirementCore _ _ ->
    Representation.Phase1ProductionStructuralRequirement
  GrammarV1ReferencePropositionRequirementCore _ ->
    Representation.Phase1ProductionPropositionRequirement
  GrammarV1ReferenceProviderRequirementCore _ _ ->
    Representation.Phase1ProductionProviderRequirement
  GrammarV1ReferenceCallableRequirementCore _ _ ->
    Representation.Phase1ProductionCallableRequirement
  GrammarV1ReferenceBoundaryRequirementCore _ _ ->
    Representation.Phase1ProductionBoundaryRequirement
  GrammarV1ReferenceArchitectureRequirementCore _ _ ->
    Representation.Phase1ProductionArchitectureRequirement
  GrammarV1ReferenceEffectsRequirementCore _ _ ->
    Representation.Phase1ProductionEffectsRequirement
  GrammarV1ReferenceAuthorityRequirementCore _ ->
    Representation.Phase1ProductionAuthorityRequirement
  GrammarV1ReferenceBoundaryRepresentationRequirementCore _ ->
    Representation.Phase1ProductionBoundaryRepresentationRequirement
  GrammarV1ReferenceRepresentationRequirementCore _ ->
    Representation.Phase1ProductionRepresentationRequirement
  GrammarV1ReferencePlacementRequirementCore _ ->
    Representation.Phase1ProductionPlacementRequirement
  GrammarV1ReferenceCostRequirementCore _ ->
    Representation.Phase1ProductionCostRequirement
  GrammarV1ReferenceEnvironmentRequirementCore _ ->
    Representation.Phase1ProductionEnvironmentRequirement

fieldNameToRepresentation
  :: GrammarV1ReferenceFieldCore
  -> Representation.String
fieldNameToRepresentation =
  textToRepresentationString . grammarV1ReferenceFieldNameCore

variantToImplementation
  :: GrammarV1ReferenceVariantCore
  -> Representation.Phase1SurfaceProductionVariant
variantToImplementation variant =
  Representation.phase1_surface_make_production_variant
    (textToRepresentationString (grammarV1ReferenceVariantNameCore variant))
    (fmap variantPayloadToImplementation
      (grammarV1ReferenceVariantPayloadCore variant))

variantPayloadToImplementation
  :: GrammarV1ReferenceVariantPayloadCore
  -> Representation.Phase1SurfaceProductionVariantPayload
variantPayloadToImplementation payload = case payload of
  GrammarV1ReferenceVariantRecordCore fields ->
    Representation.phase1_surface_make_production_record_payload
      (map fieldNameToRepresentation fields)
  GrammarV1ReferenceVariantTupleCore types ->
    Representation.phase1_surface_make_production_tuple_payload
      (replicate (length types) ())

textToRepresentationString :: Text -> Representation.String
textToRepresentationString =
  recognizerStringToRepresentation . textToKernelString

recognizerStringToRepresentation
  :: Recognizer.String
  -> Representation.String
recognizerStringToRepresentation value = case value of
  Recognizer.EmptyString -> Representation.EmptyString
  Recognizer.String0 ascii rest ->
    Representation.String0
      (recognizerAsciiToRepresentation ascii)
      (recognizerStringToRepresentation rest)

recognizerAsciiToRepresentation
  :: Recognizer.Ascii0
  -> Representation.Ascii0
recognizerAsciiToRepresentation ascii = case ascii of
  Recognizer.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 ->
    Representation.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7
