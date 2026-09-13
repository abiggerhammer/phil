module Phil.Surface.GrammarV1.ReferenceAstTopLevelRepresentationBridge
  ( grammarV1ReferenceAttributeSpineToImplementation
  , grammarV1ReferenceDeclarationTagToImplementation
  , grammarV1ReferenceTopLevelSpineToImplementation
  , grammarV1ReferenceTopLevelSpinesToImplementation
  , grammarV1ProductionTopLevelSpinesToImplementation
  ) where

import Data.Text (Text)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1SourceFile
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceAttributeSpine (..)
  , GrammarV1ReferenceDeclarationTag (..)
  , GrammarV1ReferenceTopLevelSpine (..)
  , grammarV1ProductionTopLevelSpines
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( textToKernelString
  )
import qualified SurfaceGrammarAstTopLevelCarrierKernel as Representation
import qualified SurfaceGrammarRecognizerKernel as Recognizer

-- | Bind one stable reference attribute spine to the exact compact carrier
-- extracted from the implementation representation staged by #964. Text
-- crosses the proof/production boundary through the repository's existing
-- explicit UTF-8 Rocq String convention.
grammarV1ReferenceAttributeSpineToImplementation
  :: GrammarV1ReferenceAttributeSpine
  -> Representation.Phase1SurfaceImplementationAttribute
grammarV1ReferenceAttributeSpineToImplementation attribute =
  Representation.phase1_surface_make_implementation_attribute
    (textToRepresentationString
      (grammarV1ReferenceAttributeName attribute))
    (textToRepresentationString
      (grammarV1ReferenceAttributeValue attribute))

-- | Exhaustive constructor mapping for the closed fifteen-way declaration
-- family certified by the proof-side top-level spine. Declaration payloads are
-- intentionally not represented here; #964 retains them as separate ParseTree
-- holes for later refinement slices.
grammarV1ReferenceDeclarationTagToImplementation
  :: GrammarV1ReferenceDeclarationTag
  -> Representation.Phase1SurfaceDeclarationTag
grammarV1ReferenceDeclarationTagToImplementation tag = case tag of
  GrammarV1ReferenceRecordDeclaration ->
    Representation.Phase1RecordDeclaration
  GrammarV1ReferenceDataDeclaration ->
    Representation.Phase1DataDeclaration
  GrammarV1ReferenceTypeAliasDeclaration ->
    Representation.Phase1TypeAliasDeclaration
  GrammarV1ReferenceClaimDeclaration ->
    Representation.Phase1ClaimDeclaration
  GrammarV1ReferenceCallableContractDeclaration ->
    Representation.Phase1CallableContractDeclaration
  GrammarV1ReferenceFunctionDeclaration ->
    Representation.Phase1FunctionDeclaration
  GrammarV1ReferenceProviderContractDeclaration ->
    Representation.Phase1ProviderContractDeclaration
  GrammarV1ReferenceProviderImplementationDeclaration ->
    Representation.Phase1ProviderImplementationDeclaration
  GrammarV1ReferenceOpaqueProviderImplementationDeclaration ->
    Representation.Phase1OpaqueProviderImplementationDeclaration
  GrammarV1ReferenceProtocolDeclaration ->
    Representation.Phase1ProtocolDeclaration
  GrammarV1ReferenceCapabilityDeclaration ->
    Representation.Phase1CapabilityDeclaration
  GrammarV1ReferenceBoundaryDeclaration ->
    Representation.Phase1BoundaryDeclaration
  GrammarV1ReferenceArchitectureDeclaration ->
    Representation.Phase1ArchitectureDeclaration
  GrammarV1ReferenceComponentDeclaration ->
    Representation.Phase1ComponentDeclaration
  GrammarV1ReferenceProgramDeclaration ->
    Representation.Phase1ProgramDeclaration

-- | Bind the span-insensitive top-level spine shared by the certified parse
-- tree and production AST to the exact extracted implementation carrier.
grammarV1ReferenceTopLevelSpineToImplementation
  :: GrammarV1ReferenceTopLevelSpine
  -> Representation.Phase1SurfaceImplementationTopLevel
grammarV1ReferenceTopLevelSpineToImplementation topLevel =
  Representation.phase1_surface_make_implementation_top_level
    (map grammarV1ReferenceAttributeSpineToImplementation
      (grammarV1ReferenceTopLevelAttributes topLevel))
    (grammarV1ReferenceDeclarationTagToImplementation
      (grammarV1ReferenceTopLevelDeclarationTag topLevel))

grammarV1ReferenceTopLevelSpinesToImplementation
  :: [GrammarV1ReferenceTopLevelSpine]
  -> [Representation.Phase1SurfaceImplementationTopLevel]
grammarV1ReferenceTopLevelSpinesToImplementation =
  map grammarV1ReferenceTopLevelSpineToImplementation

-- | Production binding at the same already-proved surface. This deliberately
-- goes through 'grammarV1ProductionTopLevelSpines' so the only production data
-- admitted here are attributes and the declaration-family tag already shared
-- with the certified reference spine.
grammarV1ProductionTopLevelSpinesToImplementation
  :: GrammarV1SourceFile
  -> [Representation.Phase1SurfaceImplementationTopLevel]
grammarV1ProductionTopLevelSpinesToImplementation =
  grammarV1ReferenceTopLevelSpinesToImplementation
    . grammarV1ProductionTopLevelSpines

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
