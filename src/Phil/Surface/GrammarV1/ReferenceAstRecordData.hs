{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstRecordData
  ( GrammarV1ReferenceRecordDataError (..)
  , GrammarV1ReferenceVariantPayloadCore (..)
  , GrammarV1ReferenceVariantCore (..)
  , GrammarV1ReferenceRecordDataDeclaration (..)
  , grammarV1ProductionRecordDataDeclaration
  , grammarV1ReferenceRecordDataDeclaration
  , grammarV1ProductionRecordDataDeclarations
  , grammarV1ReferenceRecordDataDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1RecordDecl (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1VariantDecl (..)
  , GrammarV1VariantPayload (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceDeclarationCommonError
  , GrammarV1ReferenceFieldCore
  , GrammarV1ReferenceGenericParamCore
  , GrammarV1ReferenceRequirementCore
  , GrammarV1ReferenceStructuralModeCore
  , grammarV1ProductionFieldCore
  , grammarV1ProductionGenericParamCore
  , grammarV1ProductionRequirementCore
  , grammarV1ProductionStructuralModeCore
  , grammarV1ReferenceFieldCore
  , grammarV1ReferenceIdentifierCore
  , grammarV1ReferenceOptionalGenericParamsCore
  , grammarV1ReferenceOptionalRequirementsCore
  , grammarV1ReferenceStructuralModeCore
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

newtype GrammarV1ReferenceRecordDataError =
  GrammarV1ReferenceRecordDataError Text
  deriving (Eq, Show)

data GrammarV1ReferenceVariantPayloadCore
  = GrammarV1ReferenceVariantRecordCore [GrammarV1ReferenceFieldCore]
  | GrammarV1ReferenceVariantTupleCore [GrammarV1ReferenceTypePayload]
  deriving (Eq, Show)

data GrammarV1ReferenceVariantCore = GrammarV1ReferenceVariantCore
  { grammarV1ReferenceVariantNameCore :: Text
  , grammarV1ReferenceVariantPayloadCore :: Maybe GrammarV1ReferenceVariantPayloadCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceRecordDataDeclaration
  = GrammarV1ReferenceRecordDeclaration
      Text
      [GrammarV1ReferenceGenericParamCore]
      (Maybe GrammarV1ReferenceStructuralModeCore)
      [GrammarV1ReferenceRequirementCore]
      [GrammarV1ReferenceFieldCore]
  | GrammarV1ReferenceDataDeclaration
      Text
      [GrammarV1ReferenceGenericParamCore]
      (Maybe GrammarV1ReferenceStructuralModeCore)
      [GrammarV1ReferenceRequirementCore]
      [GrammarV1ReferenceVariantCore]
  deriving (Eq, Show)

grammarV1ProductionRecordDataDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceRecordDataDeclaration
grammarV1ProductionRecordDataDeclaration declaration = case declaration of
  GrammarV1RecordDeclaration record ->
    Just (productionRecord record)
  GrammarV1DataDeclaration dataDecl ->
    Just (productionData dataDecl)
  _ -> Nothing

productionRecord
  :: GrammarV1RecordDecl
  -> GrammarV1ReferenceRecordDataDeclaration
productionRecord record = GrammarV1ReferenceRecordDeclaration
  (locatedValue (grammarV1RecordName record))
  (map (grammarV1ProductionGenericParamCore . locatedValue)
    (grammarV1RecordGenericParams record))
  (fmap grammarV1ProductionStructuralModeCore (grammarV1RecordMode record))
  (map (grammarV1ProductionRequirementCore . locatedValue)
    (grammarV1RecordRequirements record))
  (map (grammarV1ProductionFieldCore . locatedValue) (grammarV1RecordFields record))

productionData
  :: GrammarV1DataDecl
  -> GrammarV1ReferenceRecordDataDeclaration
productionData dataDecl = GrammarV1ReferenceDataDeclaration
  (locatedValue (grammarV1DataName dataDecl))
  (map (grammarV1ProductionGenericParamCore . locatedValue)
    (grammarV1DataGenericParams dataDecl))
  (fmap grammarV1ProductionStructuralModeCore (grammarV1DataMode dataDecl))
  (map (grammarV1ProductionRequirementCore . locatedValue)
    (grammarV1DataRequirements dataDecl))
  (map (productionVariant . locatedValue) (grammarV1DataVariants dataDecl))

productionVariant :: GrammarV1VariantDecl -> GrammarV1ReferenceVariantCore
productionVariant variant = GrammarV1ReferenceVariantCore
  { grammarV1ReferenceVariantNameCore = locatedValue (grammarV1VariantName variant)
  , grammarV1ReferenceVariantPayloadCore =
      fmap productionVariantPayload (grammarV1VariantPayload variant)
  }

productionVariantPayload
  :: GrammarV1VariantPayload
  -> GrammarV1ReferenceVariantPayloadCore
productionVariantPayload payload = case payload of
  GrammarV1VariantRecord fields ->
    GrammarV1ReferenceVariantRecordCore
      (map (grammarV1ProductionFieldCore . locatedValue) fields)
  GrammarV1VariantTuple types ->
    GrammarV1ReferenceVariantTupleCore
      (map (grammarV1ProductionTypePayload . locatedValue) types)

grammarV1ReferenceRecordDataDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError
      (Maybe GrammarV1ReferenceRecordDataDeclaration)
grammarV1ReferenceRecordDataDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> Just <$> parseRecord selected
    GrammarV1ReferenceAlternative 1 selected -> Just <$> parseData selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failRecordData
          ("declaration alternative out of range: " <> showText index)
    _ -> failRecordData "declaration body is not an alternative node"

parseRecord
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceRecordDataDeclaration
parseRecord tree = do
  fields <- namedSequence "record_decl" tree
  case fields of
    [keyword, nameTree, genericTree, modeTree, requirementsTree, openBrace, fieldsTree, closeBrace] -> do
      expectLiteral "record" keyword
      name <- mapCommonError (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommonError
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      mode <- parseOptionalMode modeTree
      requirements <- mapCommonError
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "{" openBrace
      recordFields <- parseOptionalFields fieldsTree
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceRecordDeclaration
        name genericParams mode requirements recordFields)
    _ -> failRecordData "record_decl body is not an eight-item sequence"

parseData
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceRecordDataDeclaration
parseData tree = do
  fields <- namedSequence "data_decl" tree
  case fields of
    [keyword, nameTree, genericTree, modeTree, requirementsTree, equalsTree, firstVariantTree, restTree, terminator] -> do
      expectLiteral "data" keyword
      name <- mapCommonError (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommonError
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      mode <- parseOptionalMode modeTree
      requirements <- mapCommonError
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "=" equalsTree
      first <- parseVariant firstVariantTree
      restItems <- expectRepetition "data variant suffixes" restTree
      rest <- traverse parseVariantSuffix restItems
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceDataDeclaration
        name genericParams mode requirements (first : rest))
    _ -> failRecordData "data_decl body is not a nine-item sequence"

parseOptionalMode
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError (Maybe GrammarV1ReferenceStructuralModeCore)
parseOptionalMode tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "mode clause" payload
    case fields of
      [modeKeyword, modeTree] -> do
        expectLiteral "mode" modeKeyword
        Just <$> mapCommonError (grammarV1ReferenceStructuralModeCore modeTree)
      _ -> failRecordData "mode clause is not a two-item sequence"
  _ -> failRecordData "mode clause slot is not optional"

parseOptionalFields
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError [GrammarV1ReferenceFieldCore]
parseOptionalFields tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "field list" payload
    case fields of
      [firstTree, restTree, trailingComma] -> do
        first <- mapCommonError (grammarV1ReferenceFieldCore firstTree)
        restItems <- expectRepetition "field suffixes" restTree
        rest <- traverse parseFieldSuffix restItems
        parseOptionalTrailingComma trailingComma
        pure (first : rest)
      _ -> failRecordData "field list is not a three-item sequence"
  _ -> failRecordData "field list slot is not optional"

parseFieldSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceFieldCore
parseFieldSuffix tree = do
  fields <- expectSequence "field suffix" tree
  case fields of
    [comma, fieldTree] -> do
      expectLiteral "," comma
      mapCommonError (grammarV1ReferenceFieldCore fieldTree)
    _ -> failRecordData "field suffix is not a two-item sequence"

parseOptionalTrailingComma
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError ()
parseOptionalTrailingComma tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure ()
  GrammarV1ReferenceOptionalSome comma -> expectLiteral "," comma
  _ -> failRecordData "trailing comma slot is not optional"

parseVariant
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceVariantCore
parseVariant tree = do
  fields <- namedSequence "variant_decl" tree
  case fields of
    [nameTree, payloadTree] -> do
      name <- mapCommonError (grammarV1ReferenceIdentifierCore nameTree)
      payload <- parseOptionalVariantPayload payloadTree
      pure GrammarV1ReferenceVariantCore
        { grammarV1ReferenceVariantNameCore = name
        , grammarV1ReferenceVariantPayloadCore = payload
        }
    _ -> failRecordData "variant_decl body is not a two-item sequence"

parseVariantSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceVariantCore
parseVariantSuffix tree = do
  fields <- expectSequence "variant suffix" tree
  case fields of
    [bar, variantTree] -> expectLiteral "|" bar >> parseVariant variantTree
    _ -> failRecordData "variant suffix is not a two-item sequence"

parseOptionalVariantPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError (Maybe GrammarV1ReferenceVariantPayloadCore)
parseOptionalVariantPayload tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payloadTree -> Just <$> parseVariantPayload payloadTree
  _ -> failRecordData "variant payload slot is not optional"

parseVariantPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceVariantPayloadCore
parseVariantPayload tree = do
  body <- expectNonterminal "variant_payload" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> parseRecordVariantPayload selected
    GrammarV1ReferenceAlternative 1 selected -> parseTupleVariantPayload selected
    GrammarV1ReferenceAlternative index _ ->
      failRecordData ("variant_payload alternative out of range: " <> showText index)
    _ -> failRecordData "variant_payload body is not an alternative node"

parseRecordVariantPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceVariantPayloadCore
parseRecordVariantPayload tree = do
  fields <- expectSequence "record variant payload" tree
  case fields of
    [openBrace, fieldsTree, closeBrace] -> do
      expectLiteral "{" openBrace
      values <- parseOptionalFields fieldsTree
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceVariantRecordCore values)
    _ -> failRecordData "record variant payload is not a three-item sequence"

parseTupleVariantPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceVariantPayloadCore
parseTupleVariantPayload tree = do
  fields <- expectSequence "tuple variant payload" tree
  case fields of
    [openParen, typesTree, closeParen] -> do
      expectLiteral "(" openParen
      values <- parseOptionalTypes typesTree
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceVariantTupleCore values)
    _ -> failRecordData "tuple variant payload is not a three-item sequence"

parseOptionalTypes
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError [GrammarV1ReferenceTypePayload]
parseOptionalTypes tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "type list" payload
    case fields of
      [firstTree, restTree] -> do
        first <- mapTypeError (grammarV1ReferenceTypePayload firstTree)
        restItems <- expectRepetition "type suffixes" restTree
        rest <- traverse parseTypeSuffix restItems
        pure (first : rest)
      _ -> failRecordData "type list is not a two-item sequence"
  _ -> failRecordData "type list slot is not optional"

parseTypeSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceTypePayload
parseTypeSuffix tree = do
  fields <- expectSequence "type suffix" tree
  case fields of
    [comma, typeTree] -> do
      expectLiteral "," comma
      mapTypeError (grammarV1ReferenceTypePayload typeTree)
    _ -> failRecordData "type suffix is not a two-item sequence"

grammarV1ProductionRecordDataDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceRecordDataDeclaration]
grammarV1ProductionRecordDataDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let declaration = locatedValue (grammarV1Declaration (locatedValue locatedTopLevel))
  , Just value <- [grammarV1ProductionRecordDataDeclaration declaration]
  ]

grammarV1ReferenceRecordDataDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError [GrammarV1ReferenceRecordDataDeclaration]
grammarV1ReferenceRecordDataDeclarations tree = do
  body <- expectNonterminal "source_file" tree
  fields <- expectSequence "source_file" body
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failRecordData "source_file body is not a three-item sequence"

parseTopLevel
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError (Maybe GrammarV1ReferenceRecordDataDeclaration)
parseTopLevel tree = do
  body <- expectNonterminal "top_level_decl" tree
  fields <- expectSequence "top_level_decl" body
  case fields of
    [_attributesTree, declarationTree] -> grammarV1ReferenceRecordDataDeclaration declarationTree
    _ -> failRecordData "top_level_decl body is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failRecordData ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failRecordData ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failRecordData (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failRecordData (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceRecordDataError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failRecordData ("expected literal " <> expected <> ", got " <> actual)
  _ -> failRecordData ("expected literal " <> expected)

mapCommonError
  :: Either GrammarV1ReferenceDeclarationCommonError a
  -> Either GrammarV1ReferenceRecordDataError a
mapCommonError result = case result of
  Left errorValue -> failRecordData
    ("declaration common correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

mapTypeError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceRecordDataError a
mapTypeError result = case result of
  Left errorValue -> failRecordData
    ("type correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failRecordData :: Text -> Either GrammarV1ReferenceRecordDataError a
failRecordData = Left . GrammarV1ReferenceRecordDataError
