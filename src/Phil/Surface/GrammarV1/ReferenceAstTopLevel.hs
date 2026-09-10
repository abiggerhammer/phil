{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceTopLevelError (..)
  , GrammarV1ReferenceAttributeSpine (..)
  , GrammarV1ReferenceDeclarationTag (..)
  , GrammarV1ReferenceTopLevelSpine (..)
  , grammarV1ProductionTopLevelSpines
  , grammarV1ReferenceDeclarationTag
  , grammarV1ReferenceTopLevelSpine
  , grammarV1ReferenceTopLevelSpines
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Attribute (..)
  , GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceTopLevelError = GrammarV1ReferenceTopLevelError Text
  deriving (Eq, Show)

data GrammarV1ReferenceAttributeSpine = GrammarV1ReferenceAttributeSpine
  { grammarV1ReferenceAttributeName :: Text
  , grammarV1ReferenceAttributeValue :: Text
  }
  deriving (Eq, Show)

data GrammarV1ReferenceDeclarationTag
  = GrammarV1ReferenceRecordDeclaration
  | GrammarV1ReferenceDataDeclaration
  | GrammarV1ReferenceTypeAliasDeclaration
  | GrammarV1ReferenceClaimDeclaration
  | GrammarV1ReferenceCallableContractDeclaration
  | GrammarV1ReferenceFunctionDeclaration
  | GrammarV1ReferenceProviderContractDeclaration
  | GrammarV1ReferenceProviderImplementationDeclaration
  | GrammarV1ReferenceOpaqueProviderImplementationDeclaration
  | GrammarV1ReferenceProtocolDeclaration
  | GrammarV1ReferenceCapabilityDeclaration
  | GrammarV1ReferenceBoundaryDeclaration
  | GrammarV1ReferenceArchitectureDeclaration
  | GrammarV1ReferenceComponentDeclaration
  | GrammarV1ReferenceProgramDeclaration
  deriving (Eq, Ord, Show, Enum, Bounded)

data GrammarV1ReferenceTopLevelSpine = GrammarV1ReferenceTopLevelSpine
  { grammarV1ReferenceTopLevelAttributes :: [GrammarV1ReferenceAttributeSpine]
  , grammarV1ReferenceTopLevelDeclarationTag :: GrammarV1ReferenceDeclarationTag
  }
  deriving (Eq, Show)

grammarV1ProductionTopLevelSpines
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceTopLevelSpine]
grammarV1ProductionTopLevelSpines =
  map productionTopLevel . grammarV1TopLevelDecls
  where
    productionTopLevel locatedTopLevel =
      let topLevel = locatedValue locatedTopLevel
      in GrammarV1ReferenceTopLevelSpine
          { grammarV1ReferenceTopLevelAttributes =
              map productionAttribute (grammarV1Attributes topLevel)
          , grammarV1ReferenceTopLevelDeclarationTag =
              productionDeclarationTag
                (locatedValue (grammarV1Declaration topLevel))
          }

    productionAttribute locatedAttribute =
      let attribute = locatedValue locatedAttribute
      in GrammarV1ReferenceAttributeSpine
          { grammarV1ReferenceAttributeName =
              locatedValue (grammarV1AttributeName attribute)
          , grammarV1ReferenceAttributeValue =
              locatedValue (grammarV1AttributeValue attribute)
          }

productionDeclarationTag
  :: GrammarV1Declaration
  -> GrammarV1ReferenceDeclarationTag
productionDeclarationTag declaration = case declaration of
  GrammarV1RecordDeclaration _ ->
    GrammarV1ReferenceRecordDeclaration
  GrammarV1DataDeclaration _ ->
    GrammarV1ReferenceDataDeclaration
  GrammarV1TypeAliasDeclaration _ ->
    GrammarV1ReferenceTypeAliasDeclaration
  GrammarV1ClaimDeclaration _ ->
    GrammarV1ReferenceClaimDeclaration
  GrammarV1CallableContractDeclaration _ ->
    GrammarV1ReferenceCallableContractDeclaration
  GrammarV1FunctionDeclaration _ ->
    GrammarV1ReferenceFunctionDeclaration
  GrammarV1ProviderContractDeclaration _ ->
    GrammarV1ReferenceProviderContractDeclaration
  GrammarV1ProviderImplementationDeclaration _ ->
    GrammarV1ReferenceProviderImplementationDeclaration
  GrammarV1OpaqueProviderImplementationDeclaration _ ->
    GrammarV1ReferenceOpaqueProviderImplementationDeclaration
  GrammarV1ProtocolDeclaration _ ->
    GrammarV1ReferenceProtocolDeclaration
  GrammarV1CapabilityDeclaration _ ->
    GrammarV1ReferenceCapabilityDeclaration
  GrammarV1BoundaryDeclaration _ ->
    GrammarV1ReferenceBoundaryDeclaration
  GrammarV1ArchitectureDeclaration _ ->
    GrammarV1ReferenceArchitectureDeclaration
  GrammarV1ComponentDeclaration _ ->
    GrammarV1ReferenceComponentDeclaration
  GrammarV1ProgramDeclaration _ ->
    GrammarV1ReferenceProgramDeclaration

grammarV1ReferenceTopLevelSpines
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError [GrammarV1ReferenceTopLevelSpine]
grammarV1ReferenceTopLevelSpines tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      traverse grammarV1ReferenceTopLevelSpine topLevels
    _ -> failTopLevel "source_file body is not a three-item sequence"

grammarV1ReferenceTopLevelSpine
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError GrammarV1ReferenceTopLevelSpine
grammarV1ReferenceTopLevelSpine tree = do
  body <- expectNonterminal "top_level_decl" tree
  fields <- expectSequence "top_level_decl" body
  case fields of
    [attributeTree, declarationTree] -> do
      attributeNodes <- expectRepetition "top_level_decl attributes" attributeTree
      attributes <- traverse parseAttribute attributeNodes
      declarationTag <- grammarV1ReferenceDeclarationTag declarationTree
      pure GrammarV1ReferenceTopLevelSpine
        { grammarV1ReferenceTopLevelAttributes = attributes
        , grammarV1ReferenceTopLevelDeclarationTag = declarationTag
        }
    _ -> failTopLevel "top_level_decl body is not a two-item sequence"

parseAttribute
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError GrammarV1ReferenceAttributeSpine
parseAttribute tree = do
  body <- expectNonterminal "attribute" tree
  fields <- expectSequence "attribute" body
  case fields of
    [atSign, nameTree, openParen, valueTree, closeParen] -> do
      expectLiteral "@" atSign
      name <- parseIdentifier nameTree
      expectLiteral "(" openParen
      value <- parseMetadataString valueTree
      expectLiteral ")" closeParen
      pure GrammarV1ReferenceAttributeSpine
        { grammarV1ReferenceAttributeName = name
        , grammarV1ReferenceAttributeValue = value
        }
    _ -> failTopLevel "attribute body is not a five-item sequence"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failTopLevel ("identifier uses lexical class " <> className)
    _ -> failTopLevel "identifier body is not an IDENTIFIER lexical leaf"

parseMetadataString
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError Text
parseMetadataString tree = do
  body <- expectNonterminal "metadata_string_literal" tree
  case body of
    GrammarV1ReferenceLexical "STRING_LITERAL" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failTopLevel ("metadata string uses lexical class " <> className)
    _ -> failTopLevel "metadata_string_literal body is not a STRING_LITERAL lexical leaf"

grammarV1ReferenceDeclarationTag
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError GrammarV1ReferenceDeclarationTag
grammarV1ReferenceDeclarationTag tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> do
      (expectedName, tag) <- declarationAlternative index
      _ <- expectNonterminal expectedName selected
      pure tag
    _ -> failTopLevel "declaration body is not an alternative node"

declarationAlternative
  :: Integer
  -> Either GrammarV1ReferenceTopLevelError (Text, GrammarV1ReferenceDeclarationTag)
declarationAlternative index = case index of
  0 -> pair "record_decl" GrammarV1ReferenceRecordDeclaration
  1 -> pair "data_decl" GrammarV1ReferenceDataDeclaration
  2 -> pair "type_alias_decl" GrammarV1ReferenceTypeAliasDeclaration
  3 -> pair "claim_decl" GrammarV1ReferenceClaimDeclaration
  4 -> pair "callable_contract_decl" GrammarV1ReferenceCallableContractDeclaration
  5 -> pair "function_decl" GrammarV1ReferenceFunctionDeclaration
  6 -> pair "provider_contract_decl" GrammarV1ReferenceProviderContractDeclaration
  7 -> pair "provider_implementation_decl" GrammarV1ReferenceProviderImplementationDeclaration
  8 -> pair "opaque_provider_implementation_decl" GrammarV1ReferenceOpaqueProviderImplementationDeclaration
  9 -> pair "protocol_decl" GrammarV1ReferenceProtocolDeclaration
  10 -> pair "capability_decl" GrammarV1ReferenceCapabilityDeclaration
  11 -> pair "boundary_decl" GrammarV1ReferenceBoundaryDeclaration
  12 -> pair "architecture_decl" GrammarV1ReferenceArchitectureDeclaration
  13 -> pair "component_decl" GrammarV1ReferenceComponentDeclaration
  14 -> pair "program_decl" GrammarV1ReferenceProgramDeclaration
  _ -> failTopLevel ("declaration alternative index out of range: " <> showText index)
  where
    pair name tag = Right (name, tag)

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failTopLevel
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failTopLevel ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failTopLevel (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failTopLevel (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTopLevelError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failTopLevel
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failTopLevel ("expected literal " <> expected)

showText :: Show a => a -> Text
showText = Text.pack . show

failTopLevel :: Text -> Either GrammarV1ReferenceTopLevelError a
failTopLevel = Left . GrammarV1ReferenceTopLevelError
