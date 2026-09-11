{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceDeclarationCommonError (..)
  , GrammarV1ReferenceStructuralModeCore (..)
  , GrammarV1ReferenceGenericKindCore (..)
  , GrammarV1ReferenceGenericParamCore (..)
  , GrammarV1ReferenceRequirementCore (..)
  , GrammarV1ReferenceFieldCore (..)
  , grammarV1ProductionStructuralModeCore
  , grammarV1ReferenceStructuralModeCore
  , grammarV1ProductionGenericParamCore
  , grammarV1ReferenceGenericParamCore
  , grammarV1ReferenceOptionalGenericParamsCore
  , grammarV1ProductionRequirementCore
  , grammarV1ReferenceRequirementCore
  , grammarV1ReferenceOptionalRequirementsCore
  , grammarV1ProductionFieldCore
  , grammarV1ReferenceFieldCore
  , grammarV1ReferenceIdentifierCore
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Field (..)
  , GrammarV1GenericKind (..)
  , GrammarV1GenericParam (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1StructuralMode (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstEffects
  ( GrammarV1ReferenceEffectSetSpine
  , grammarV1ProductionEffectSetSpine
  , grammarV1ReferenceEffectSetSpine
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceTypePayload
  , grammarV1ProductionTypePayload
  , grammarV1ReferenceTypePayload
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceDeclarationCommonError =
  GrammarV1ReferenceDeclarationCommonError Text
  deriving (Eq, Show)

data GrammarV1ReferenceStructuralModeCore
  = GrammarV1ReferenceUnrestrictedMode
  | GrammarV1ReferenceAffineMode
  | GrammarV1ReferenceLinearMode
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceGenericKindCore
  = GrammarV1ReferenceTypeKindCore
  | GrammarV1ReferenceNatKindCore
  | GrammarV1ReferenceSessionKindCore
  | GrammarV1ReferenceMessageKindCore
  | GrammarV1ReferenceEffectsKindCore
  | GrammarV1ReferenceProviderKindCore GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceCallableKindCore GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceBoundaryKindCore GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceArchitectureKindCore GrammarV1ReferenceTypePayload
  deriving (Eq, Show)

data GrammarV1ReferenceGenericParamCore = GrammarV1ReferenceGenericParamCore
  { grammarV1ReferenceGenericParamNameCore :: Text
  , grammarV1ReferenceGenericParamKindCore :: GrammarV1ReferenceGenericKindCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceRequirementCore
  = GrammarV1ReferenceStructuralRequirementCore Text Text
  | GrammarV1ReferencePropositionRequirementCore GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceProviderRequirementCore Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceCallableRequirementCore Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceBoundaryRequirementCore Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceArchitectureRequirementCore Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceEffectsRequirementCore Text GrammarV1ReferenceEffectSetSpine
  | GrammarV1ReferenceAuthorityRequirementCore GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceBoundaryRepresentationRequirementCore GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceRepresentationRequirementCore GrammarV1ReferencePropositionCore
  | GrammarV1ReferencePlacementRequirementCore GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceCostRequirementCore GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceEnvironmentRequirementCore GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceFieldCore = GrammarV1ReferenceFieldCore
  { grammarV1ReferenceFieldNameCore :: Text
  , grammarV1ReferenceFieldTypeCore :: GrammarV1ReferenceTypePayload
  }
  deriving (Eq, Show)

grammarV1ProductionStructuralModeCore
  :: GrammarV1StructuralMode
  -> GrammarV1ReferenceStructuralModeCore
grammarV1ProductionStructuralModeCore mode = case mode of
  GrammarV1Unrestricted -> GrammarV1ReferenceUnrestrictedMode
  GrammarV1Affine -> GrammarV1ReferenceAffineMode
  GrammarV1Linear -> GrammarV1ReferenceLinearMode

grammarV1ReferenceStructuralModeCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceStructuralModeCore
grammarV1ReferenceStructuralModeCore tree = do
  body <- expectNonterminal "structural_mode" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected ->
      expectLiteral "unrestricted" selected >> pure GrammarV1ReferenceUnrestrictedMode
    GrammarV1ReferenceAlternative 1 selected ->
      expectLiteral "affine" selected >> pure GrammarV1ReferenceAffineMode
    GrammarV1ReferenceAlternative 2 selected ->
      expectLiteral "linear" selected >> pure GrammarV1ReferenceLinearMode
    GrammarV1ReferenceAlternative index _ ->
      failCommon ("structural_mode alternative out of range: " <> showText index)
    _ -> failCommon "structural_mode body is not an alternative node"

grammarV1ProductionGenericParamCore
  :: GrammarV1GenericParam
  -> GrammarV1ReferenceGenericParamCore
grammarV1ProductionGenericParamCore parameter = GrammarV1ReferenceGenericParamCore
  { grammarV1ReferenceGenericParamNameCore = locatedValue (grammarV1GenericParamName parameter)
  , grammarV1ReferenceGenericParamKindCore =
      productionGenericKind (locatedValue (grammarV1GenericParamKind parameter))
  }

productionGenericKind
  :: GrammarV1GenericKind
  -> GrammarV1ReferenceGenericKindCore
productionGenericKind kind = case kind of
  GrammarV1TypeKind -> GrammarV1ReferenceTypeKindCore
  GrammarV1NatKind -> GrammarV1ReferenceNatKindCore
  GrammarV1SessionKind -> GrammarV1ReferenceSessionKindCore
  GrammarV1MessageKind -> GrammarV1ReferenceMessageKindCore
  GrammarV1EffectsKind -> GrammarV1ReferenceEffectsKindCore
  GrammarV1ProviderKind sourceType ->
    GrammarV1ReferenceProviderKindCore (grammarV1ProductionTypePayload sourceType)
  GrammarV1CallableKind sourceType ->
    GrammarV1ReferenceCallableKindCore (grammarV1ProductionTypePayload sourceType)
  GrammarV1BoundaryKind sourceType ->
    GrammarV1ReferenceBoundaryKindCore (grammarV1ProductionTypePayload sourceType)
  GrammarV1ArchitectureKind sourceType ->
    GrammarV1ReferenceArchitectureKindCore (grammarV1ProductionTypePayload sourceType)

grammarV1ReferenceGenericParamCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceGenericParamCore
grammarV1ReferenceGenericParamCore tree = do
  body <- expectNonterminal "generic_param" tree
  fields <- expectSequence "generic_param" body
  case fields of
    [nameTree, colon, kindTree] -> do
      name <- grammarV1ReferenceIdentifierCore nameTree
      expectLiteral ":" colon
      kind <- parseGenericKind kindTree
      pure GrammarV1ReferenceGenericParamCore
        { grammarV1ReferenceGenericParamNameCore = name
        , grammarV1ReferenceGenericParamKindCore = kind
        }
    _ -> failCommon "generic_param body is not a three-item sequence"

parseGenericKind
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceGenericKindCore
parseGenericKind tree = do
  body <- expectNonterminal "generic_kind" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> expectLiteral "Type" selected >> pure GrammarV1ReferenceTypeKindCore
      1 -> expectLiteral "Nat" selected >> pure GrammarV1ReferenceNatKindCore
      2 -> expectLiteral "Session" selected >> pure GrammarV1ReferenceSessionKindCore
      3 -> expectLiteral "Message" selected >> pure GrammarV1ReferenceMessageKindCore
      4 -> expectLiteral "Effects" selected >> pure GrammarV1ReferenceEffectsKindCore
      5 -> parseContractKind "provider" GrammarV1ReferenceProviderKindCore selected
      6 -> parseContractKind "callable" GrammarV1ReferenceCallableKindCore selected
      7 -> parseContractKind "boundary" GrammarV1ReferenceBoundaryKindCore selected
      8 -> parseContractKind "architecture" GrammarV1ReferenceArchitectureKindCore selected
      _ -> failCommon ("generic_kind alternative out of range: " <> showText index)
    _ -> failCommon "generic_kind body is not an alternative node"

parseContractKind
  :: Text
  -> (GrammarV1ReferenceTypePayload -> GrammarV1ReferenceGenericKindCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceGenericKindCore
parseContractKind keyword constructor tree = do
  fields <- expectSequence (keyword <> " generic kind") tree
  case fields of
    [keywordTree, typeTree] -> do
      expectLiteral keyword keywordTree
      constructor <$> mapTypeError (grammarV1ReferenceTypePayload typeTree)
    _ -> failCommon (keyword <> " generic kind is not a two-item sequence")

grammarV1ReferenceOptionalGenericParamsCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError [GrammarV1ReferenceGenericParamCore]
grammarV1ReferenceOptionalGenericParamsCore tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome paramsTree -> do
    body <- expectNonterminal "generic_params" paramsTree
    fields <- expectSequence "generic_params" body
    case fields of
      [openBracket, firstTree, restTree, closeBracket] -> do
        expectLiteral "[" openBracket
        first <- grammarV1ReferenceGenericParamCore firstTree
        rest <- expectRepetition "generic_params suffixes" restTree
          >>= traverse parseGenericParamSuffix
        expectLiteral "]" closeBracket
        pure (first : rest)
      _ -> failCommon "generic_params body is not a four-item sequence"
  _ -> failCommon "generic parameter slot is not optional"

parseGenericParamSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceGenericParamCore
parseGenericParamSuffix tree = do
  fields <- expectSequence "generic_params suffix" tree
  case fields of
    [comma, parameterTree] -> do
      expectLiteral "," comma
      grammarV1ReferenceGenericParamCore parameterTree
    _ -> failCommon "generic_params suffix is not a two-item sequence"

grammarV1ProductionRequirementCore
  :: GrammarV1GenericRequirement
  -> GrammarV1ReferenceRequirementCore
grammarV1ProductionRequirementCore requirement = case requirement of
  GrammarV1StructuralRequirement name required ->
    GrammarV1ReferenceStructuralRequirementCore (locatedValue name) (locatedValue required)
  GrammarV1PropositionRequirement proposition ->
    GrammarV1ReferencePropositionRequirementCore
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1ProviderRequirement name sourceType ->
    GrammarV1ReferenceProviderRequirementCore
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1CallableRequirement name sourceType ->
    GrammarV1ReferenceCallableRequirementCore
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1BoundaryRequirement name sourceType ->
    GrammarV1ReferenceBoundaryRequirementCore
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1ArchitectureRequirement name sourceType ->
    GrammarV1ReferenceArchitectureRequirementCore
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1EffectsRequirement name effects ->
    GrammarV1ReferenceEffectsRequirementCore
      (locatedValue name)
      (grammarV1ProductionEffectSetSpine (locatedValue effects))
  GrammarV1AuthorityRequirement sourceType ->
    GrammarV1ReferenceAuthorityRequirementCore
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1BoundaryRepresentationRequirement sourceType ->
    GrammarV1ReferenceBoundaryRepresentationRequirementCore
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1RepresentationRequirement proposition ->
    GrammarV1ReferenceRepresentationRequirementCore
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1PlacementRequirement proposition ->
    GrammarV1ReferencePlacementRequirementCore
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1CostRequirement proposition ->
    GrammarV1ReferenceCostRequirementCore
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1EnvironmentRequirement proposition ->
    GrammarV1ReferenceEnvironmentRequirementCore
      (grammarV1ProductionPropositionCore (locatedValue proposition))

grammarV1ReferenceRequirementCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
grammarV1ReferenceRequirementCore tree = do
  body <- expectNonterminal "generic_requirement" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> parseStructuralRequirement selected
      1 -> parsePropositionRequirement selected
      2 -> parseNamedTypeRequirement "provider" GrammarV1ReferenceProviderRequirementCore selected
      3 -> parseNamedTypeRequirement "callable" GrammarV1ReferenceCallableRequirementCore selected
      4 -> parseNamedTypeRequirement "boundary" GrammarV1ReferenceBoundaryRequirementCore selected
      5 -> parseNamedTypeRequirement "architecture" GrammarV1ReferenceArchitectureRequirementCore selected
      6 -> parseEffectsRequirement selected
      7 -> parseTypeOnlyRequirement "authority" GrammarV1ReferenceAuthorityRequirementCore selected
      8 -> parseBoundaryRepresentationRequirement selected
      9 -> parsePropositionOnlyRequirement "representation" GrammarV1ReferenceRepresentationRequirementCore selected
      10 -> parsePropositionOnlyRequirement "placement" GrammarV1ReferencePlacementRequirementCore selected
      11 -> parsePropositionOnlyRequirement "cost" GrammarV1ReferenceCostRequirementCore selected
      12 -> parsePropositionOnlyRequirement "environment" GrammarV1ReferenceEnvironmentRequirementCore selected
      _ -> failCommon ("generic_requirement alternative out of range: " <> showText index)
    _ -> failCommon "generic_requirement body is not an alternative node"

parseStructuralRequirement
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
parseStructuralRequirement tree = do
  fields <- expectSequence "structural requirement" tree
  case fields of
    [keyword, nameTree, colon, requiredTree, terminator] -> do
      expectLiteral "structural" keyword
      name <- grammarV1ReferenceIdentifierCore nameTree
      expectLiteral ":" colon
      required <- grammarV1ReferenceIdentifierCore requiredTree
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceStructuralRequirementCore name required)
    _ -> failCommon "structural requirement is not a five-item sequence"

parsePropositionRequirement
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
parsePropositionRequirement tree = do
  fields <- expectSequence "proposition requirement" tree
  case fields of
    [keyword, propositionTree, terminator] -> do
      expectLiteral "proposition" keyword
      proposition <- mapPropositionError (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferencePropositionRequirementCore proposition)
    _ -> failCommon "proposition requirement is not a three-item sequence"

parseNamedTypeRequirement
  :: Text
  -> (Text -> GrammarV1ReferenceTypePayload -> GrammarV1ReferenceRequirementCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
parseNamedTypeRequirement keyword constructor tree = do
  fields <- expectSequence (keyword <> " requirement") tree
  case fields of
    [keywordTree, nameTree, colon, typeTree, terminator] -> do
      expectLiteral keyword keywordTree
      name <- grammarV1ReferenceIdentifierCore nameTree
      expectLiteral ":" colon
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      expectLiteral ";" terminator
      pure (constructor name sourceType)
    _ -> failCommon (keyword <> " requirement is not a five-item sequence")

parseEffectsRequirement
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
parseEffectsRequirement tree = do
  fields <- expectSequence "effects requirement" tree
  case fields of
    [keyword, nameTree, withinKeyword, effectsTree, terminator] -> do
      expectLiteral "effects" keyword
      name <- grammarV1ReferenceIdentifierCore nameTree
      expectLiteral "within" withinKeyword
      effects <- mapEffectsError (grammarV1ReferenceEffectSetSpine effectsTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceEffectsRequirementCore name effects)
    _ -> failCommon "effects requirement is not a five-item sequence"

parseTypeOnlyRequirement
  :: Text
  -> (GrammarV1ReferenceTypePayload -> GrammarV1ReferenceRequirementCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
parseTypeOnlyRequirement keyword constructor tree = do
  fields <- expectSequence (keyword <> " requirement") tree
  case fields of
    [keywordTree, typeTree, terminator] -> do
      expectLiteral keyword keywordTree
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      expectLiteral ";" terminator
      pure (constructor sourceType)
    _ -> failCommon (keyword <> " requirement is not a three-item sequence")

parseBoundaryRepresentationRequirement
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
parseBoundaryRepresentationRequirement tree = do
  fields <- expectSequence "boundary representation requirement" tree
  case fields of
    [boundaryKeyword, representationKeyword, typeTree, terminator] -> do
      expectLiteral "boundary" boundaryKeyword
      expectLiteral "representation" representationKeyword
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceBoundaryRepresentationRequirementCore sourceType)
    _ -> failCommon "boundary representation requirement is not a four-item sequence"

parsePropositionOnlyRequirement
  :: Text
  -> (GrammarV1ReferencePropositionCore -> GrammarV1ReferenceRequirementCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceRequirementCore
parsePropositionOnlyRequirement keyword constructor tree = do
  fields <- expectSequence (keyword <> " requirement") tree
  case fields of
    [keywordTree, propositionTree, terminator] -> do
      expectLiteral keyword keywordTree
      proposition <- mapPropositionError (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral ";" terminator
      pure (constructor proposition)
    _ -> failCommon (keyword <> " requirement is not a three-item sequence")

grammarV1ReferenceOptionalRequirementsCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError [GrammarV1ReferenceRequirementCore]
grammarV1ReferenceOptionalRequirementsCore tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome requirementsTree -> do
    body <- expectNonterminal "generic_requirements" requirementsTree
    fields <- expectSequence "generic_requirements" body
    case fields of
      [requiresKeyword, openBrace, entriesTree, closeBrace] -> do
        expectLiteral "requires" requiresKeyword
        expectLiteral "{" openBrace
        entries <- expectRepetition "generic_requirements entries" entriesTree
          >>= traverse grammarV1ReferenceRequirementCore
        expectLiteral "}" closeBrace
        pure entries
      _ -> failCommon "generic_requirements body is not a four-item sequence"
  _ -> failCommon "generic requirement slot is not optional"

grammarV1ProductionFieldCore
  :: GrammarV1Field
  -> GrammarV1ReferenceFieldCore
grammarV1ProductionFieldCore field = GrammarV1ReferenceFieldCore
  { grammarV1ReferenceFieldNameCore = locatedValue (grammarV1FieldName field)
  , grammarV1ReferenceFieldTypeCore =
      grammarV1ProductionTypePayload (locatedValue (grammarV1FieldType field))
  }

grammarV1ReferenceFieldCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceFieldCore
grammarV1ReferenceFieldCore tree = do
  body <- expectNonterminal "field_decl" tree
  fields <- expectSequence "field_decl" body
  case fields of
    [nameTree, colon, typeTree] -> do
      name <- grammarV1ReferenceIdentifierCore nameTree
      expectLiteral ":" colon
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      pure GrammarV1ReferenceFieldCore
        { grammarV1ReferenceFieldNameCore = name
        , grammarV1ReferenceFieldTypeCore = sourceType
        }
    _ -> failCommon "field_decl body is not a three-item sequence"

grammarV1ReferenceIdentifierCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError Text
grammarV1ReferenceIdentifierCore tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> pure value
    GrammarV1ReferenceLexical className _ ->
      failCommon ("identifier lexical class mismatch: " <> className)
    _ -> failCommon "identifier body is not an IDENTIFIER lexical leaf"

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failCommon ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failCommon ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failCommon (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failCommon (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceDeclarationCommonError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failCommon ("expected literal " <> expected <> ", got " <> actual)
  _ -> failCommon ("expected literal " <> expected)

mapTypeError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceDeclarationCommonError a
mapTypeError result = case result of
  Left errorValue -> failCommon ("type correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

mapPropositionError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceDeclarationCommonError a
mapPropositionError result = case result of
  Left errorValue -> failCommon ("proposition correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

mapEffectsError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceDeclarationCommonError a
mapEffectsError result = case result of
  Left errorValue -> failCommon ("effect-set correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failCommon
  :: Text
  -> Either GrammarV1ReferenceDeclarationCommonError a
failCommon = Left . GrammarV1ReferenceDeclarationCommonError
