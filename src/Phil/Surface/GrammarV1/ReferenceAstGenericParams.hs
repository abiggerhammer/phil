{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstGenericParams
  ( GrammarV1ReferenceGenericParamError (..)
  , GrammarV1ReferenceGenericKindSpine (..)
  , GrammarV1ReferenceGenericParamSpine (..)
  , GrammarV1ReferenceTypeAliasGenericParams (..)
  , grammarV1ProductionTypeAliasGenericParams
  , grammarV1ReferenceTypeAliasGenericParams
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1GenericKind (..)
  , GrammarV1GenericParam (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeTag
  , grammarV1ProductionTypeTag
  , grammarV1ReferenceTypeTag
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceGenericParamError =
  GrammarV1ReferenceGenericParamError Text
  deriving (Eq, Show)

data GrammarV1ReferenceGenericKindSpine
  = GrammarV1ReferenceTypeKind
  | GrammarV1ReferenceNatKind
  | GrammarV1ReferenceSessionKind
  | GrammarV1ReferenceMessageKind
  | GrammarV1ReferenceEffectsKind
  | GrammarV1ReferenceProviderKind GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceCallableKind GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceBoundaryKind GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceArchitectureKind GrammarV1ReferenceTypeTag
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceGenericParamSpine = GrammarV1ReferenceGenericParamSpine
  { grammarV1ReferenceGenericParamName :: Text
  , grammarV1ReferenceGenericParamKind :: GrammarV1ReferenceGenericKindSpine
  }
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceTypeAliasGenericParams =
  GrammarV1ReferenceTypeAliasGenericParams
    { grammarV1ReferenceGenericParamsAliasName :: Text
    , grammarV1ReferenceGenericParams :: [GrammarV1ReferenceGenericParamSpine]
    }
  deriving (Eq, Show)

grammarV1ProductionTypeAliasGenericParams
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceTypeAliasGenericParams]
grammarV1ProductionTypeAliasGenericParams sourceFile =
  [ GrammarV1ReferenceTypeAliasGenericParams
      { grammarV1ReferenceGenericParamsAliasName =
          locatedValue (grammarV1TypeAliasName alias)
      , grammarV1ReferenceGenericParams =
          map productionGenericParam (grammarV1TypeAliasGenericParams alias)
      }
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]
  where
    productionGenericParam locatedParam =
      let param = locatedValue locatedParam
      in GrammarV1ReferenceGenericParamSpine
          { grammarV1ReferenceGenericParamName =
              locatedValue (grammarV1GenericParamName param)
          , grammarV1ReferenceGenericParamKind =
              productionGenericKind
                (locatedValue (grammarV1GenericParamKind param))
          }

productionGenericKind
  :: GrammarV1GenericKind
  -> GrammarV1ReferenceGenericKindSpine
productionGenericKind kind = case kind of
  GrammarV1TypeKind -> GrammarV1ReferenceTypeKind
  GrammarV1NatKind -> GrammarV1ReferenceNatKind
  GrammarV1SessionKind -> GrammarV1ReferenceSessionKind
  GrammarV1MessageKind -> GrammarV1ReferenceMessageKind
  GrammarV1EffectsKind -> GrammarV1ReferenceEffectsKind
  GrammarV1ProviderKind sourceType ->
    GrammarV1ReferenceProviderKind (grammarV1ProductionTypeTag sourceType)
  GrammarV1CallableKind sourceType ->
    GrammarV1ReferenceCallableKind (grammarV1ProductionTypeTag sourceType)
  GrammarV1BoundaryKind sourceType ->
    GrammarV1ReferenceBoundaryKind (grammarV1ProductionTypeTag sourceType)
  GrammarV1ArchitectureKind sourceType ->
    GrammarV1ReferenceArchitectureKind (grammarV1ProductionTypeTag sourceType)

grammarV1ReferenceTypeAliasGenericParams
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError
      [GrammarV1ReferenceTypeAliasGenericParams]
grammarV1ReferenceTypeAliasGenericParams tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAlias topLevels
      pure [value | Just value <- values]
    _ -> failGenericParam "source_file body is not a three-item sequence"

parseTopLevelTypeAlias
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError
      (Maybe GrammarV1ReferenceTypeAliasGenericParams)
parseTopLevelTypeAlias tree = do
  topLevelBody <- expectNonterminal "top_level_decl" tree
  fields <- expectSequence "top_level_decl" topLevelBody
  case fields of
    [_attributes, declarationTree] -> do
      declarationBody <- expectNonterminal "declaration" declarationTree
      case declarationBody of
        GrammarV1ReferenceAlternative 2 selected ->
          Just <$> parseTypeAliasDecl selected
        GrammarV1ReferenceAlternative _ _ -> Right Nothing
        _ -> failGenericParam "declaration body is not an alternative node"
    _ -> failGenericParam "top_level_decl body is not a two-item sequence"

parseTypeAliasDecl
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError
      GrammarV1ReferenceTypeAliasGenericParams
parseTypeAliasDecl tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [typeKeyword, nameTree, genericTree, _requirementTree, equalsSign, _targetTree, terminator] -> do
      expectLiteral "type" typeKeyword
      name <- parseIdentifier nameTree
      params <- parseOptionalGenericParams genericTree
      expectLiteral "=" equalsSign
      expectLiteral ";" terminator
      pure GrammarV1ReferenceTypeAliasGenericParams
        { grammarV1ReferenceGenericParamsAliasName = name
        , grammarV1ReferenceGenericParams = params
        }
    _ -> failGenericParam "type_alias_decl body is not a seven-item sequence"

parseOptionalGenericParams
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError
      [GrammarV1ReferenceGenericParamSpine]
parseOptionalGenericParams tree = case tree of
  GrammarV1ReferenceOptionalNone -> Right []
  GrammarV1ReferenceOptionalSome paramsTree -> do
    body <- expectNonterminal "generic_params" paramsTree
    fields <- expectSequence "generic_params" body
    case fields of
      [openBracket, firstParam, restTree, closeBracket] -> do
        expectLiteral "[" openBracket
        first <- parseGenericParam firstParam
        restItems <- expectRepetition "generic_params suffix" restTree
        rest <- traverse parseGenericParamSuffix restItems
        expectLiteral "]" closeBracket
        pure (first : rest)
      _ -> failGenericParam "generic_params body is not a four-item sequence"
  _ -> failGenericParam "type_alias_decl generic-parameter slot is not optional"

parseGenericParamSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError GrammarV1ReferenceGenericParamSpine
parseGenericParamSuffix tree = do
  fields <- expectSequence "generic_params suffix item" tree
  case fields of
    [comma, param] -> do
      expectLiteral "," comma
      parseGenericParam param
    _ -> failGenericParam "generic_params suffix item is not a two-item sequence"

parseGenericParam
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError GrammarV1ReferenceGenericParamSpine
parseGenericParam tree = do
  body <- expectNonterminal "generic_param" tree
  fields <- expectSequence "generic_param" body
  case fields of
    [nameTree, colon, kindTree] -> do
      name <- parseIdentifier nameTree
      expectLiteral ":" colon
      kind <- parseGenericKind kindTree
      pure GrammarV1ReferenceGenericParamSpine
        { grammarV1ReferenceGenericParamName = name
        , grammarV1ReferenceGenericParamKind = kind
        }
    _ -> failGenericParam "generic_param body is not a three-item sequence"

parseGenericKind
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError GrammarV1ReferenceGenericKindSpine
parseGenericKind tree = do
  body <- expectNonterminal "generic_kind" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> expectLiteral "Type" selected >> pure GrammarV1ReferenceTypeKind
      1 -> expectLiteral "Nat" selected >> pure GrammarV1ReferenceNatKind
      2 -> expectLiteral "Session" selected >> pure GrammarV1ReferenceSessionKind
      3 -> expectLiteral "Message" selected >> pure GrammarV1ReferenceMessageKind
      4 -> expectLiteral "Effects" selected >> pure GrammarV1ReferenceEffectsKind
      5 -> parseContractKind "provider" GrammarV1ReferenceProviderKind selected
      6 -> parseContractKind "callable" GrammarV1ReferenceCallableKind selected
      7 -> parseContractKind "boundary" GrammarV1ReferenceBoundaryKind selected
      8 -> parseContractKind "architecture" GrammarV1ReferenceArchitectureKind selected
      _ -> failGenericParam ("generic_kind alternative out of range: " <> showText index)
    _ -> failGenericParam "generic_kind body is not an alternative node"

parseContractKind
  :: Text
  -> (GrammarV1ReferenceTypeTag -> GrammarV1ReferenceGenericKindSpine)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError GrammarV1ReferenceGenericKindSpine
parseContractKind keyword constructor selected = do
  fields <- expectSequence (keyword <> " generic kind") selected
  case fields of
    [keywordTree, typeTree] -> do
      expectLiteral keyword keywordTree
      typeTag <- mapTypeAliasError (grammarV1ReferenceTypeTag typeTree)
      pure (constructor typeTag)
    _ -> failGenericParam (keyword <> " generic kind is not a two-item sequence")

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failGenericParam ("identifier uses lexical class " <> className)
    _ -> failGenericParam "identifier body is not an IDENTIFIER lexical leaf"

mapTypeAliasError
  :: Either a b
  -> Either GrammarV1ReferenceGenericParamError b
mapTypeAliasError result = case result of
  Left _ -> failGenericParam "nested type_expression failed shallow correspondence"
  Right value -> Right value

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failGenericParam
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failGenericParam ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failGenericParam (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failGenericParam (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericParamError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failGenericParam
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failGenericParam ("expected literal " <> expected)

showText :: Show a => a -> Text
showText = Text.pack . show

failGenericParam :: Text -> Either GrammarV1ReferenceGenericParamError a
failGenericParam = Left . GrammarV1ReferenceGenericParamError
