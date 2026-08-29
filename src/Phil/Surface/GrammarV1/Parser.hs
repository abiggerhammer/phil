{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.Parser
  ( GrammarV1ParseDiagnostic (..)
  , GrammarV1SourceFile (..)
  , GrammarV1ModuleDecl (..)
  , GrammarV1ImportDecl (..)
  , GrammarV1Attribute (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1StructuralMode (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1GenericKind (..)
  , GrammarV1GenericParam (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  , GrammarV1RelationOperator (..)
  , GrammarV1Proposition (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1Type (..)
  , GrammarV1Field (..)
  , GrammarV1RecordDecl (..)
  , GrammarV1VariantPayload (..)
  , GrammarV1VariantDecl (..)
  , GrammarV1DataDecl (..)
  , GrammarV1TypeAliasDecl (..)
  , GrammarV1ClaimDecl (..)
  , GrammarV1CapabilityItem (..)
  , GrammarV1CapabilityDecl (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1ProtocolDecl (..)
  , GrammarV1TermParam (..)
  , GrammarV1Pattern (..)
  , GrammarV1Expression (..)
  , GrammarV1Statement (..)
  , GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , parseGrammarV1StructuralSource
  ) where

import Data.Maybe (listToMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Lexer
import Phil.Surface.Syntax
  ( Located (..)
  , SourceSpan (..)
  )

-- This is the incremental production parser for Grammar v1. Unsupported valid
-- Grammar-v1 declaration or expression families fail closed until their exact
-- production parser is added; no balanced-token or recovery fallback exists.

data GrammarV1ParseDiagnostic
  = GrammarV1LexicalDiagnostic GrammarV1LexDiagnostic
  | GrammarV1SyntaxDiagnostic (Maybe SourceSpan) Text
  deriving (Eq, Show)

data GrammarV1SourceFile = GrammarV1SourceFile
  { grammarV1ModuleDecl :: Maybe (Located GrammarV1ModuleDecl)
  , grammarV1ImportDecls :: [Located GrammarV1ImportDecl]
  , grammarV1TopLevelDecls :: [Located GrammarV1TopLevelDecl]
  }
  deriving (Eq, Show)

newtype GrammarV1ModuleDecl = GrammarV1ModuleDecl
  { grammarV1ModuleName :: Located GrammarV1QualifiedName
  }
  deriving (Eq, Show)

data GrammarV1ImportDecl = GrammarV1ImportDecl
  { grammarV1ImportName :: Located GrammarV1QualifiedName
  , grammarV1ImportSelection :: Maybe [Located Text]
  }
  deriving (Eq, Show)

data GrammarV1Attribute = GrammarV1Attribute
  { grammarV1AttributeName :: Located Text
  , grammarV1AttributeValue :: Located Text
  }
  deriving (Eq, Show)

data GrammarV1TopLevelDecl = GrammarV1TopLevelDecl
  { grammarV1Attributes :: [Located GrammarV1Attribute]
  , grammarV1Declaration :: Located GrammarV1Declaration
  }
  deriving (Eq, Show)

data GrammarV1Declaration
  = GrammarV1RecordDeclaration GrammarV1RecordDecl
  | GrammarV1DataDeclaration GrammarV1DataDecl
  | GrammarV1TypeAliasDeclaration GrammarV1TypeAliasDecl
  | GrammarV1ClaimDeclaration GrammarV1ClaimDecl
  | GrammarV1CapabilityDeclaration GrammarV1CapabilityDecl
  | GrammarV1ProtocolDeclaration GrammarV1ProtocolDecl
  | GrammarV1ComponentDeclaration GrammarV1ComponentDecl
  deriving (Eq, Show)

data GrammarV1StructuralMode
  = GrammarV1Unrestricted
  | GrammarV1Affine
  | GrammarV1Linear
  deriving (Eq, Ord, Show)

newtype GrammarV1QualifiedName = GrammarV1QualifiedName
  { grammarV1QualifiedNameParts :: [Text]
  }
  deriving (Eq, Ord, Show)

data GrammarV1GenericKind
  = GrammarV1TypeKind
  | GrammarV1NatKind
  | GrammarV1SessionKind
  | GrammarV1MessageKind
  | GrammarV1EffectsKind
  | GrammarV1ProviderKind GrammarV1Type
  | GrammarV1CallableKind GrammarV1Type
  | GrammarV1BoundaryKind GrammarV1Type
  | GrammarV1ArchitectureKind GrammarV1Type
  deriving (Eq, Ord, Show)

data GrammarV1GenericParam = GrammarV1GenericParam
  { grammarV1GenericParamName :: Located Text
  , grammarV1GenericParamKind :: Located GrammarV1GenericKind
  }
  deriving (Eq, Show)

data GrammarV1StaticArgument
  = GrammarV1StaticTypeArgument GrammarV1Type
  | GrammarV1StaticReferenceArgument GrammarV1StaticReference
  | GrammarV1StaticBoolArgument Bool
  | GrammarV1StaticIntegerArgument Text
  deriving (Eq, Ord, Show)

data GrammarV1StaticReference = GrammarV1StaticReference
  { grammarV1StaticReferenceName :: GrammarV1QualifiedName
  , grammarV1StaticReferenceArguments :: [GrammarV1StaticArgument]
  }
  deriving (Eq, Ord, Show)

data GrammarV1RelationOperator
  = GrammarV1EqualRelation
  | GrammarV1NotEqualRelation
  | GrammarV1LessEqualRelation
  | GrammarV1GreaterEqualRelation
  | GrammarV1LessRelation
  | GrammarV1GreaterRelation
  | GrammarV1InRelation
  | GrammarV1DisjointRelation
  deriving (Eq, Ord, Show)

data GrammarV1Proposition
  = GrammarV1TrueProposition
  | GrammarV1FalseProposition
  | GrammarV1RelationProposition
      (Located GrammarV1Expression)
      (Located GrammarV1RelationOperator)
      (Located GrammarV1Expression)
  | GrammarV1NotProposition (Located GrammarV1Proposition)
  | GrammarV1AndProposition
      (Located GrammarV1Proposition)
      (Located GrammarV1Proposition)
  | GrammarV1OrProposition
      (Located GrammarV1Proposition)
      (Located GrammarV1Proposition)
  deriving (Eq, Show)

data GrammarV1GenericRequirement
  = GrammarV1StructuralRequirement (Located Text) (Located Text)
  | GrammarV1PropositionRequirement (Located GrammarV1Proposition)
  | GrammarV1ProviderRequirement (Located Text) (Located GrammarV1Type)
  | GrammarV1CallableRequirement (Located Text) (Located GrammarV1Type)
  | GrammarV1BoundaryRequirement (Located Text) (Located GrammarV1Type)
  | GrammarV1ArchitectureRequirement (Located Text) (Located GrammarV1Type)
  | GrammarV1AuthorityRequirement (Located GrammarV1Type)
  | GrammarV1BoundaryRepresentationRequirement (Located GrammarV1Type)
  | GrammarV1RepresentationRequirement (Located GrammarV1Proposition)
  | GrammarV1PlacementRequirement (Located GrammarV1Proposition)
  | GrammarV1CostRequirement (Located GrammarV1Proposition)
  | GrammarV1EnvironmentRequirement (Located GrammarV1Proposition)
  deriving (Eq, Show)

data GrammarV1Type
  = GrammarV1UnitType
  | GrammarV1BoolType
  | GrammarV1UnsignedType Text
  | GrammarV1NamedType GrammarV1StaticReference
  deriving (Eq, Ord, Show)

data GrammarV1Field = GrammarV1Field
  { grammarV1FieldName :: Located Text
  , grammarV1FieldType :: Located GrammarV1Type
  }
  deriving (Eq, Show)

data GrammarV1RecordDecl = GrammarV1RecordDecl
  { grammarV1RecordName :: Located Text
  , grammarV1RecordGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1RecordMode :: Maybe GrammarV1StructuralMode
  , grammarV1RecordRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1RecordFields :: [Located GrammarV1Field]
  }
  deriving (Eq, Show)

data GrammarV1VariantPayload
  = GrammarV1VariantRecord [Located GrammarV1Field]
  | GrammarV1VariantTuple [Located GrammarV1Type]
  deriving (Eq, Show)

data GrammarV1VariantDecl = GrammarV1VariantDecl
  { grammarV1VariantName :: Located Text
  , grammarV1VariantPayload :: Maybe GrammarV1VariantPayload
  }
  deriving (Eq, Show)

data GrammarV1DataDecl = GrammarV1DataDecl
  { grammarV1DataName :: Located Text
  , grammarV1DataGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1DataMode :: Maybe GrammarV1StructuralMode
  , grammarV1DataRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1DataVariants :: [Located GrammarV1VariantDecl]
  }
  deriving (Eq, Show)

data GrammarV1TypeAliasDecl = GrammarV1TypeAliasDecl
  { grammarV1TypeAliasName :: Located Text
  , grammarV1TypeAliasGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1TypeAliasRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1TypeAliasTarget :: Located GrammarV1Type
  }
  deriving (Eq, Show)

data GrammarV1ClaimDecl = GrammarV1ClaimDecl
  { grammarV1ClaimName :: Located Text
  , grammarV1ClaimGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1ClaimRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1ClaimTermParams :: Maybe [Located GrammarV1TermParam]
  , grammarV1ClaimProposition :: Maybe (Located GrammarV1Proposition)
  }
  deriving (Eq, Show)

data GrammarV1CapabilityItem
  = GrammarV1CapabilityPermits (Located GrammarV1StaticReference)
  deriving (Eq, Show)

data GrammarV1CapabilityDecl = GrammarV1CapabilityDecl
  { grammarV1CapabilityName :: Located Text
  , grammarV1CapabilityGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1CapabilityMode :: GrammarV1StructuralMode
  , grammarV1CapabilityRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1CapabilityItems :: [Located GrammarV1CapabilityItem]
  }
  deriving (Eq, Show)

newtype GrammarV1SessionExpression = GrammarV1SessionReference
  { grammarV1SessionReference :: GrammarV1StaticReference
  }
  deriving (Eq, Ord, Show)

data GrammarV1RoleSessionDecl = GrammarV1RoleSessionDecl
  { grammarV1RoleSessionName :: Located Text
  , grammarV1RoleSessionExpression :: Located GrammarV1SessionExpression
  }
  deriving (Eq, Show)

data GrammarV1ProtocolDecl = GrammarV1ProtocolDecl
  { grammarV1ProtocolName :: Located Text
  , grammarV1ProtocolGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1ProtocolRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1ProtocolRoles :: [Located GrammarV1RoleSessionDecl]
  }
  deriving (Eq, Show)

data GrammarV1TermParam = GrammarV1TermParam
  { grammarV1TermParamName :: Located Text
  , grammarV1TermParamType :: Located GrammarV1Type
  }
  deriving (Eq, Show)

newtype GrammarV1Pattern = GrammarV1IdentifierPattern
  { grammarV1IdentifierPatternName :: Located Text
  }
  deriving (Eq, Show)

data GrammarV1Expression
  = GrammarV1NameExpression GrammarV1StaticReference [Located GrammarV1Expression]
  | GrammarV1BoolExpression Bool
  | GrammarV1UnitExpression
  | GrammarV1IntegerExpression Text
  deriving (Eq, Show)

data GrammarV1Statement
  = GrammarV1LetStatement (Located GrammarV1Pattern) (Located GrammarV1Expression)
  | GrammarV1ReturnStatement (Located GrammarV1Expression)
  | GrammarV1ExpressionStatement (Located GrammarV1Expression)
  deriving (Eq, Show)

newtype GrammarV1Block = GrammarV1Block
  { grammarV1BlockStatements :: [Located GrammarV1Statement]
  }
  deriving (Eq, Show)

data GrammarV1ComponentDecl = GrammarV1ComponentDecl
  { grammarV1ComponentName :: Located Text
  , grammarV1ComponentGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1ComponentRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1ComponentTermParams :: Maybe [Located GrammarV1TermParam]
  , grammarV1ComponentProvides :: Maybe (Located GrammarV1Type)
  , grammarV1ComponentBody :: Located GrammarV1Block
  }
  deriving (Eq, Show)

type Tokens = [Located GrammarV1Token]

newtype Parser a = Parser
  { runParser :: Tokens -> Either GrammarV1ParseDiagnostic (a, Tokens)
  }

instance Functor Parser where
  fmap f parser = Parser $ \tokens -> do
    (value, rest) <- runParser parser tokens
    pure (f value, rest)

instance Applicative Parser where
  pure value = Parser $ \tokens -> Right (value, tokens)
  functionParser <*> valueParser = Parser $ \tokens -> do
    (function, rest) <- runParser functionParser tokens
    (value, rest') <- runParser valueParser rest
    pure (function value, rest')

instance Monad Parser where
  parser >>= next = Parser $ \tokens -> do
    (value, rest) <- runParser parser tokens
    runParser (next value) rest

parseGrammarV1StructuralSource
  :: Text
  -> Text
  -> Either GrammarV1ParseDiagnostic GrammarV1SourceFile
parseGrammarV1StructuralSource source input = do
  tokens <- case lexGrammarV1 source input of
    Left diagnostic -> Left (GrammarV1LexicalDiagnostic diagnostic)
    Right values -> Right values
  (parsed, rest) <- runParser parseSourceFile tokens
  case rest of
    [] -> Right parsed
    token : _ -> Left $ GrammarV1SyntaxDiagnostic
      (Just (locatedSpan token))
      ("unexpected trailing token " <> renderToken (locatedValue token))

parseSourceFile :: Parser GrammarV1SourceFile
parseSourceFile = do
  hasModule <- peekKeyword "module"
  moduleDecl <- if hasModule then Just <$> parseModuleDecl else pure Nothing
  imports <- parseImports
  declarations <- parseTopLevels
  pure GrammarV1SourceFile
    { grammarV1ModuleDecl = moduleDecl
    , grammarV1ImportDecls = imports
    , grammarV1TopLevelDecls = declarations
    }

parseImports :: Parser [Located GrammarV1ImportDecl]
parseImports = do
  hasImport <- peekKeyword "import"
  if hasImport
    then do
      value <- parseImportDecl
      rest <- parseImports
      pure (value : rest)
    else pure []

parseTopLevels :: Parser [Located GrammarV1TopLevelDecl]
parseTopLevels = do
  token <- peekToken
  case token of
    Nothing -> pure []
    Just _ -> do
      value <- parseTopLevelDecl
      rest <- parseTopLevels
      pure (value : rest)

parseModuleDecl :: Parser (Located GrammarV1ModuleDecl)
parseModuleDecl = do
  start <- expectKeyword "module"
  name <- parseQualifiedName
  end <- expectSymbol ";"
  pure $ locatedBetween start end (GrammarV1ModuleDecl name)

parseImportDecl :: Parser (Located GrammarV1ImportDecl)
parseImportDecl = do
  start <- expectKeyword "import"
  name <- parseQualifiedName
  hasSelection <- peekSymbol "{"
  selection <- if hasSelection then Just <$> parseImportSelection else pure Nothing
  end <- expectSymbol ";"
  pure $ locatedBetween start end GrammarV1ImportDecl
    { grammarV1ImportName = name
    , grammarV1ImportSelection = selection
    }

parseImportSelection :: Parser [Located Text]
parseImportSelection = do
  _ <- expectSymbol "{"
  emptySelection <- peekSymbol "}"
  if emptySelection
    then failParser "import selection braces require a nonempty identifier_list"
    else do
      first <- expectIdentifier
      rest <- parseCommaIdentifiers
      _ <- expectSymbol "}"
      pure (first : rest)

parseCommaIdentifiers :: Parser [Located Text]
parseCommaIdentifiers = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      value <- expectIdentifier
      rest <- parseCommaIdentifiers
      pure (value : rest)
    else pure []

parseTopLevelDecl :: Parser (Located GrammarV1TopLevelDecl)
parseTopLevelDecl = do
  attributes <- parseAttributes
  declaration <- parseDeclaration
  let span' = case attributes of
        firstAttribute : _ -> SourceSpan
          (sourceSpanStart (locatedSpan firstAttribute))
          (sourceSpanEnd (locatedSpan declaration))
        [] -> locatedSpan declaration
  pure $ Located span' GrammarV1TopLevelDecl
    { grammarV1Attributes = attributes
    , grammarV1Declaration = declaration
    }

parseAttributes :: Parser [Located GrammarV1Attribute]
parseAttributes = do
  hasAttribute <- peekSymbol "@"
  if hasAttribute
    then do
      value <- parseAttribute
      rest <- parseAttributes
      pure (value : rest)
    else pure []

parseAttribute :: Parser (Located GrammarV1Attribute)
parseAttribute = do
  start <- expectSymbol "@"
  name <- expectIdentifier
  _ <- expectSymbol "("
  value <- expectString
  end <- expectSymbol ")"
  pure $ locatedBetween start end GrammarV1Attribute
    { grammarV1AttributeName = name
    , grammarV1AttributeValue = value
    }

parseDeclaration :: Parser (Located GrammarV1Declaration)
parseDeclaration = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "record") -> parseRecordDeclaration
    Just (GrammarKeyword "data") -> parseDataDeclaration
    Just (GrammarKeyword "type") -> parseTypeAliasDeclaration
    Just (GrammarKeyword "claim") -> parseClaimDeclaration
    Just (GrammarKeyword "capability") -> parseCapabilityDeclaration
    Just (GrammarKeyword "protocol") -> parseProtocolDeclaration
    Just (GrammarKeyword "component") -> parseComponentDeclaration
    Just other -> failParser $
      "SURF-002 production parser does not yet implement declaration production beginning with "
        <> renderToken other
    Nothing -> failParser "expected Grammar-v1 declaration at end of input"

parseRecordDeclaration :: Parser (Located GrammarV1Declaration)
parseRecordDeclaration = do
  start <- expectKeyword "record"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  mode <- parseOptionalMode
  requirements <- parseOptionalGenericRequirements
  _ <- expectSymbol "{"
  fields <- parseFieldList
  end <- expectSymbol "}"
  pure $ locatedBetween start end $ GrammarV1RecordDeclaration GrammarV1RecordDecl
    { grammarV1RecordName = name
    , grammarV1RecordGenericParams = params
    , grammarV1RecordMode = mode
    , grammarV1RecordRequirements = requirements
    , grammarV1RecordFields = fields
    }

parseDataDeclaration :: Parser (Located GrammarV1Declaration)
parseDataDeclaration = do
  start <- expectKeyword "data"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  mode <- parseOptionalMode
  requirements <- parseOptionalGenericRequirements
  _ <- expectSymbol "="
  first <- parseVariantDecl
  rest <- parseMoreVariants
  end <- expectSymbol ";"
  pure $ locatedBetween start end $ GrammarV1DataDeclaration GrammarV1DataDecl
    { grammarV1DataName = name
    , grammarV1DataGenericParams = params
    , grammarV1DataMode = mode
    , grammarV1DataRequirements = requirements
    , grammarV1DataVariants = first : rest
    }

parseTypeAliasDeclaration :: Parser (Located GrammarV1Declaration)
parseTypeAliasDeclaration = do
  start <- expectKeyword "type"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  hasMode <- peekKeyword "mode"
  if hasMode
    then failParser "type_alias_decl does not admit structural mode syntax"
    else pure ()
  requirements <- parseOptionalGenericRequirements
  _ <- expectSymbol "="
  target <- parseType
  end <- expectSymbol ";"
  pure $ locatedBetween start end $ GrammarV1TypeAliasDeclaration GrammarV1TypeAliasDecl
    { grammarV1TypeAliasName = name
    , grammarV1TypeAliasGenericParams = params
    , grammarV1TypeAliasRequirements = requirements
    , grammarV1TypeAliasTarget = target
    }

parseClaimDeclaration :: Parser (Located GrammarV1Declaration)
parseClaimDeclaration = do
  start <- expectKeyword "claim"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  requirements <- parseOptionalGenericRequirements
  termParams <- parseOptionalTermParams
  hasDefinition <- peekSymbol "="
  proposition <- if hasDefinition
    then do
      _ <- expectSymbol "="
      Just <$> parseProposition
    else pure Nothing
  end <- expectSymbol ";"
  pure $ locatedBetween start end $ GrammarV1ClaimDeclaration GrammarV1ClaimDecl
    { grammarV1ClaimName = name
    , grammarV1ClaimGenericParams = params
    , grammarV1ClaimRequirements = requirements
    , grammarV1ClaimTermParams = termParams
    , grammarV1ClaimProposition = proposition
    }

parseMoreVariants :: Parser [Located GrammarV1VariantDecl]
parseMoreVariants = do
  hasPipe <- peekSymbol "|"
  if hasPipe
    then do
      _ <- expectSymbol "|"
      value <- parseVariantDecl
      rest <- parseMoreVariants
      pure (value : rest)
    else pure []

parseVariantDecl :: Parser (Located GrammarV1VariantDecl)
parseVariantDecl = do
  name <- expectIdentifier
  recordPayload <- peekSymbol "{"
  tuplePayload <- peekSymbol "("
  if recordPayload
    then do
      _ <- expectSymbol "{"
      fields <- parseFieldList
      end <- expectSymbol "}"
      pure $ locatedBetween name end GrammarV1VariantDecl
        { grammarV1VariantName = name
        , grammarV1VariantPayload = Just (GrammarV1VariantRecord fields)
        }
    else if tuplePayload
      then do
        _ <- expectSymbol "("
        values <- parseTypeList
        end <- expectSymbol ")"
        pure $ locatedBetween name end GrammarV1VariantDecl
          { grammarV1VariantName = name
          , grammarV1VariantPayload = Just (GrammarV1VariantTuple values)
          }
      else pure $ Located (locatedSpan name) GrammarV1VariantDecl
        { grammarV1VariantName = name
        , grammarV1VariantPayload = Nothing
        }

parseCapabilityDeclaration :: Parser (Located GrammarV1Declaration)
parseCapabilityDeclaration = do
  start <- expectKeyword "capability"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  _ <- expectKeyword "mode"
  mode <- parseStructuralMode
  requirements <- parseOptionalGenericRequirements
  _ <- expectSymbol "{"
  items <- parseCapabilityItems
  end <- expectSymbol "}"
  pure $ locatedBetween start end $ GrammarV1CapabilityDeclaration GrammarV1CapabilityDecl
    { grammarV1CapabilityName = name
    , grammarV1CapabilityGenericParams = params
    , grammarV1CapabilityMode = mode
    , grammarV1CapabilityRequirements = requirements
    , grammarV1CapabilityItems = items
    }

parseCapabilityItems :: Parser [Located GrammarV1CapabilityItem]
parseCapabilityItems = do
  atEnd <- peekSymbol "}"
  if atEnd
    then pure []
    else do
      item <- parseCapabilityItem
      rest <- parseCapabilityItems
      pure (item : rest)

parseCapabilityItem :: Parser (Located GrammarV1CapabilityItem)
parseCapabilityItem = do
  permits <- peekKeyword "permits"
  if permits
    then do
      start <- expectKeyword "permits"
      target <- parseStaticReference
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1CapabilityPermits target)
    else do
      token <- peekToken
      case token of
        Just value -> failParser $
          "SURF-002 production parser capability item not yet implemented: "
            <> renderToken (locatedValue value)
        Nothing -> failParser "unterminated capability declaration"

parseProtocolDeclaration :: Parser (Located GrammarV1Declaration)
parseProtocolDeclaration = do
  start <- expectKeyword "protocol"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  requirements <- parseOptionalGenericRequirements
  _ <- expectSymbol "{"
  firstRole <- parseRoleSessionDecl
  secondRole <- parseRoleSessionDecl
  end <- expectSymbol "}"
  pure $ locatedBetween start end $ GrammarV1ProtocolDeclaration GrammarV1ProtocolDecl
    { grammarV1ProtocolName = name
    , grammarV1ProtocolGenericParams = params
    , grammarV1ProtocolRequirements = requirements
    , grammarV1ProtocolRoles = [firstRole, secondRole]
    }

parseRoleSessionDecl :: Parser (Located GrammarV1RoleSessionDecl)
parseRoleSessionDecl = do
  start <- expectKeyword "role"
  name <- expectIdentifier
  _ <- expectSymbol "="
  session <- parseSessionExpression
  end <- expectSymbol ";"
  pure $ locatedBetween start end GrammarV1RoleSessionDecl
    { grammarV1RoleSessionName = name
    , grammarV1RoleSessionExpression = session
    }

parseSessionExpression :: Parser (Located GrammarV1SessionExpression)
parseSessionExpression = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarIdentifier _) -> do
      reference <- parseStaticReference
      pure $ Located
        (locatedSpan reference)
        (GrammarV1SessionReference (locatedValue reference))
    Just other -> failParser $
      "SURF-002 generic/static slice does not yet implement nonreference session_expression beginning with "
        <> renderToken other
    Nothing -> failParser "expected session_expression at end of input"

parseComponentDeclaration :: Parser (Located GrammarV1Declaration)
parseComponentDeclaration = do
  start <- expectKeyword "component"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  requirements <- parseOptionalGenericRequirements
  termParams <- parseOptionalTermParams
  provides <- parseOptionalProvides
  body <- parseBlock
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan body)))
    (GrammarV1ComponentDeclaration GrammarV1ComponentDecl
      { grammarV1ComponentName = name
      , grammarV1ComponentGenericParams = params
      , grammarV1ComponentRequirements = requirements
      , grammarV1ComponentTermParams = termParams
      , grammarV1ComponentProvides = provides
      , grammarV1ComponentBody = body
      })

parseOptionalTermParams :: Parser (Maybe [Located GrammarV1TermParam])
parseOptionalTermParams = do
  present <- peekSymbol "("
  if present then Just <$> parseTermParams else pure Nothing

parseTermParams :: Parser [Located GrammarV1TermParam]
parseTermParams = do
  _ <- expectSymbol "("
  atEnd <- peekSymbol ")"
  if atEnd
    then expectSymbol ")" >> pure []
    else do
      first <- parseTermParam
      rest <- parseMoreTermParams
      _ <- expectSymbol ")"
      pure (first : rest)

parseMoreTermParams :: Parser [Located GrammarV1TermParam]
parseMoreTermParams = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "term_params does not admit a trailing comma"
        else do
          value <- parseTermParam
          rest <- parseMoreTermParams
          pure (value : rest)
    else pure []

parseTermParam :: Parser (Located GrammarV1TermParam)
parseTermParam = do
  name <- expectIdentifier
  _ <- expectSymbol ":"
  ty <- parseType
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan name))
      (sourceSpanEnd (locatedSpan ty)))
    GrammarV1TermParam
      { grammarV1TermParamName = name
      , grammarV1TermParamType = ty
      }

parseOptionalProvides :: Parser (Maybe (Located GrammarV1Type))
parseOptionalProvides = do
  present <- peekKeyword "provides"
  if present
    then expectKeyword "provides" >> Just <$> parseType
    else pure Nothing

parseBlock :: Parser (Located GrammarV1Block)
parseBlock = do
  start <- expectSymbol "{"
  statements <- parseStatements
  end <- expectSymbol "}"
  pure $ locatedBetween start end (GrammarV1Block statements)

parseStatements :: Parser [Located GrammarV1Statement]
parseStatements = do
  atEnd <- peekSymbol "}"
  if atEnd
    then pure []
    else do
      statement <- parseStatement
      rest <- parseStatements
      pure (statement : rest)

parseStatement :: Parser (Located GrammarV1Statement)
parseStatement = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "let") -> parseLetStatement
    Just (GrammarKeyword "return") -> parseReturnStatement
    Just _ -> do
      expression <- parseExpression
      pure $ Located
        (locatedSpan expression)
        (GrammarV1ExpressionStatement expression)
    Nothing -> failParser "expected statement at end of input"

parseLetStatement :: Parser (Located GrammarV1Statement)
parseLetStatement = do
  start <- expectKeyword "let"
  pattern' <- parsePattern
  _ <- expectSymbol "="
  expression <- parseExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan expression)))
    (GrammarV1LetStatement pattern' expression)

parseReturnStatement :: Parser (Located GrammarV1Statement)
parseReturnStatement = do
  start <- expectKeyword "return"
  expression <- parseExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan expression)))
    (GrammarV1ReturnStatement expression)

parsePattern :: Parser (Located GrammarV1Pattern)
parsePattern = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarIdentifier _) -> do
      name <- expectIdentifier
      pure $ Located
        (locatedSpan name)
        (GrammarV1IdentifierPattern name)
    Just other -> failParser $
      "SURF-002 term/block slice expects an identifier pattern; found " <> renderToken other
    Nothing -> failParser "expected pattern at end of input"

parseExpression :: Parser (Located GrammarV1Expression)
parseExpression = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "true") -> do
      value <- expectKeyword "true"
      pure (Located (locatedSpan value) (GrammarV1BoolExpression True))
    Just (GrammarKeyword "false") -> do
      value <- expectKeyword "false"
      pure (Located (locatedSpan value) (GrammarV1BoolExpression False))
    Just (GrammarKeyword "unit") -> do
      value <- expectKeyword "unit"
      pure (Located (locatedSpan value) GrammarV1UnitExpression)
    Just (GrammarDecimalInteger _) -> do
      value <- takeToken
      case locatedValue value of
        GrammarDecimalInteger integer ->
          pure (Located (locatedSpan value) (GrammarV1IntegerExpression integer))
        _ -> failParser "internal DECIMAL_INTEGER expression dispatch error"
    Just (GrammarIdentifier _) -> parseNameExpression
    Just other -> failParser $
      "SURF-002 term/block slice does not yet implement expression beginning with "
        <> renderToken other
    Nothing -> failParser "expected expression at end of input"

parseNameExpression :: Parser (Located GrammarV1Expression)
parseNameExpression = do
  reference <- parseStaticReference
  hasTermArguments <- peekSymbol "("
  if hasTermArguments
    then do
      (arguments, end) <- parseTermArguments
      pure $ Located
        (SourceSpan
          (sourceSpanStart (locatedSpan reference))
          (sourceSpanEnd (locatedSpan end)))
        (GrammarV1NameExpression (locatedValue reference) arguments)
    else pure $ Located
      (locatedSpan reference)
      (GrammarV1NameExpression (locatedValue reference) [])

parseTermArguments :: Parser ([Located GrammarV1Expression], Located GrammarV1Token)
parseTermArguments = do
  _ <- expectSymbol "("
  atEnd <- peekSymbol ")"
  if atEnd
    then do
      end <- expectSymbol ")"
      pure ([], end)
    else do
      first <- parseExpression
      rest <- parseMoreTermArguments
      end <- expectSymbol ")"
      pure (first : rest, end)

parseMoreTermArguments :: Parser [Located GrammarV1Expression]
parseMoreTermArguments = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "term_arguments does not admit a trailing comma"
        else do
          value <- parseExpression
          rest <- parseMoreTermArguments
          pure (value : rest)
    else pure []

parseOptionalGenericParams :: Parser [Located GrammarV1GenericParam]
parseOptionalGenericParams = do
  present <- peekSymbol "["
  if present then parseGenericParams else pure []

parseGenericParams :: Parser [Located GrammarV1GenericParam]
parseGenericParams = do
  _ <- expectSymbol "["
  atEnd <- peekSymbol "]"
  if atEnd
    then failParser "generic_params requires at least one generic_param"
    else do
      first <- parseGenericParam
      rest <- parseMoreGenericParams
      _ <- expectSymbol "]"
      pure (first : rest)

parseMoreGenericParams :: Parser [Located GrammarV1GenericParam]
parseMoreGenericParams = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol "]"
      if atEnd
        then failParser "generic_params does not admit a trailing comma"
        else do
          value <- parseGenericParam
          rest <- parseMoreGenericParams
          pure (value : rest)
    else pure []

parseGenericParam :: Parser (Located GrammarV1GenericParam)
parseGenericParam = do
  name <- expectIdentifier
  _ <- expectSymbol ":"
  kind <- parseGenericKind
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan name))
      (sourceSpanEnd (locatedSpan kind)))
    GrammarV1GenericParam
      { grammarV1GenericParamName = name
      , grammarV1GenericParamKind = kind
      }

parseGenericKind :: Parser (Located GrammarV1GenericKind)
parseGenericKind = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "Type") -> simpleKind "Type" GrammarV1TypeKind
    Just (GrammarKeyword "Nat") -> simpleKind "Nat" GrammarV1NatKind
    Just (GrammarKeyword "Session") -> simpleKind "Session" GrammarV1SessionKind
    Just (GrammarKeyword "Message") -> simpleKind "Message" GrammarV1MessageKind
    Just (GrammarKeyword "Effects") -> simpleKind "Effects" GrammarV1EffectsKind
    Just (GrammarKeyword "provider") -> typeKind "provider" GrammarV1ProviderKind
    Just (GrammarKeyword "callable") -> typeKind "callable" GrammarV1CallableKind
    Just (GrammarKeyword "boundary") -> typeKind "boundary" GrammarV1BoundaryKind
    Just (GrammarKeyword "architecture") -> typeKind "architecture" GrammarV1ArchitectureKind
    Just other -> failParser ("expected generic_kind; found " <> renderToken other)
    Nothing -> failParser "expected generic_kind at end of input"
  where
    simpleKind keyword value = do
      consumed <- expectKeyword keyword
      pure (Located (locatedSpan consumed) value)
    typeKind keyword constructor = do
      start <- expectKeyword keyword
      ty <- parseType
      pure $ Located
        (SourceSpan
          (sourceSpanStart (locatedSpan start))
          (sourceSpanEnd (locatedSpan ty)))
        (constructor (locatedValue ty))

parseOptionalGenericRequirements :: Parser [Located GrammarV1GenericRequirement]
parseOptionalGenericRequirements = do
  present <- peekKeyword "requires"
  if present then parseGenericRequirements else pure []

parseGenericRequirements :: Parser [Located GrammarV1GenericRequirement]
parseGenericRequirements = do
  _ <- expectKeyword "requires"
  _ <- expectSymbol "{"
  values <- parseGenericRequirementList
  _ <- expectSymbol "}"
  pure values

parseGenericRequirementList :: Parser [Located GrammarV1GenericRequirement]
parseGenericRequirementList = do
  atEnd <- peekSymbol "}"
  if atEnd
    then pure []
    else do
      value <- parseGenericRequirement
      rest <- parseGenericRequirementList
      pure (value : rest)

parseGenericRequirement :: Parser (Located GrammarV1GenericRequirement)
parseGenericRequirement = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "structural") -> parseStructuralRequirement
    Just (GrammarKeyword "proposition") -> parsePropositionRequirement
    Just (GrammarKeyword "provider") -> parseNamedTypeRequirement "provider" GrammarV1ProviderRequirement
    Just (GrammarKeyword "callable") -> parseNamedTypeRequirement "callable" GrammarV1CallableRequirement
    Just (GrammarKeyword "boundary") -> parseBoundaryRequirement
    Just (GrammarKeyword "architecture") -> parseNamedTypeRequirement "architecture" GrammarV1ArchitectureRequirement
    Just (GrammarKeyword "effects") -> failParser "effects generic requirements are reserved for the later effect-set parser slice"
    Just (GrammarKeyword "authority") -> parseTypeOnlyRequirement "authority" GrammarV1AuthorityRequirement
    Just (GrammarKeyword "representation") -> parsePropositionOnlyRequirement "representation" GrammarV1RepresentationRequirement
    Just (GrammarKeyword "placement") -> parsePropositionOnlyRequirement "placement" GrammarV1PlacementRequirement
    Just (GrammarKeyword "cost") -> parsePropositionOnlyRequirement "cost" GrammarV1CostRequirement
    Just (GrammarKeyword "environment") -> parsePropositionOnlyRequirement "environment" GrammarV1EnvironmentRequirement
    Just other -> failParser ("expected generic_requirement; found " <> renderToken other)
    Nothing -> failParser "expected generic_requirement at end of input"

parseStructuralRequirement :: Parser (Located GrammarV1GenericRequirement)
parseStructuralRequirement = do
  start <- expectKeyword "structural"
  name <- expectIdentifier
  _ <- expectSymbol ":"
  requirement <- expectIdentifier
  end <- expectSymbol ";"
  pure $ locatedBetween start end (GrammarV1StructuralRequirement name requirement)

parsePropositionRequirement :: Parser (Located GrammarV1GenericRequirement)
parsePropositionRequirement = do
  start <- expectKeyword "proposition"
  proposition <- parseProposition
  end <- expectSymbol ";"
  pure $ locatedBetween start end (GrammarV1PropositionRequirement proposition)

parseNamedTypeRequirement
  :: Text
  -> (Located Text -> Located GrammarV1Type -> GrammarV1GenericRequirement)
  -> Parser (Located GrammarV1GenericRequirement)
parseNamedTypeRequirement keyword constructor = do
  start <- expectKeyword keyword
  name <- expectIdentifier
  _ <- expectSymbol ":"
  ty <- parseType
  end <- expectSymbol ";"
  pure $ locatedBetween start end (constructor name ty)

parseBoundaryRequirement :: Parser (Located GrammarV1GenericRequirement)
parseBoundaryRequirement = do
  start <- expectKeyword "boundary"
  isRepresentation <- peekKeyword "representation"
  if isRepresentation
    then do
      _ <- expectKeyword "representation"
      ty <- parseType
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1BoundaryRepresentationRequirement ty)
    else do
      name <- expectIdentifier
      _ <- expectSymbol ":"
      ty <- parseType
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1BoundaryRequirement name ty)

parseTypeOnlyRequirement
  :: Text
  -> (Located GrammarV1Type -> GrammarV1GenericRequirement)
  -> Parser (Located GrammarV1GenericRequirement)
parseTypeOnlyRequirement keyword constructor = do
  start <- expectKeyword keyword
  ty <- parseType
  end <- expectSymbol ";"
  pure $ locatedBetween start end (constructor ty)

parsePropositionOnlyRequirement
  :: Text
  -> (Located GrammarV1Proposition -> GrammarV1GenericRequirement)
  -> Parser (Located GrammarV1GenericRequirement)
parsePropositionOnlyRequirement keyword constructor = do
  start <- expectKeyword keyword
  proposition <- parseProposition
  end <- expectSymbol ";"
  pure $ locatedBetween start end (constructor proposition)

parseProposition :: Parser (Located GrammarV1Proposition)
parseProposition = parsePropositionOr

parsePropositionOr :: Parser (Located GrammarV1Proposition)
parsePropositionOr = do
  first <- parsePropositionAnd
  parseMorePropositionOr first

parseMorePropositionOr
  :: Located GrammarV1Proposition
  -> Parser (Located GrammarV1Proposition)
parseMorePropositionOr left = do
  present <- peekKeyword "or"
  if present
    then do
      _ <- expectKeyword "or"
      right <- parsePropositionAnd
      let combined = Located
            (SourceSpan
              (sourceSpanStart (locatedSpan left))
              (sourceSpanEnd (locatedSpan right)))
            (GrammarV1OrProposition left right)
      parseMorePropositionOr combined
    else pure left

parsePropositionAnd :: Parser (Located GrammarV1Proposition)
parsePropositionAnd = do
  first <- parsePropositionNot
  parseMorePropositionAnd first

parseMorePropositionAnd
  :: Located GrammarV1Proposition
  -> Parser (Located GrammarV1Proposition)
parseMorePropositionAnd left = do
  present <- peekKeyword "and"
  if present
    then do
      _ <- expectKeyword "and"
      right <- parsePropositionNot
      let combined = Located
            (SourceSpan
              (sourceSpanStart (locatedSpan left))
              (sourceSpanEnd (locatedSpan right)))
            (GrammarV1AndProposition left right)
      parseMorePropositionAnd combined
    else pure left

parsePropositionNot :: Parser (Located GrammarV1Proposition)
parsePropositionNot = do
  present <- peekKeyword "not"
  if present
    then do
      start <- expectKeyword "not"
      proposition <- parsePropositionNot
      pure $ Located
        (SourceSpan
          (sourceSpanStart (locatedSpan start))
          (sourceSpanEnd (locatedSpan proposition)))
        (GrammarV1NotProposition proposition)
    else parsePropositionAtom

parsePropositionAtom :: Parser (Located GrammarV1Proposition)
parsePropositionAtom = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "true") -> do
      value <- expectKeyword "true"
      pure (Located (locatedSpan value) GrammarV1TrueProposition)
    Just (GrammarKeyword "false") -> do
      value <- expectKeyword "false"
      pure (Located (locatedSpan value) GrammarV1FalseProposition)
    Just (GrammarSymbol "(") -> do
      start <- expectSymbol "("
      proposition <- parseProposition
      end <- expectSymbol ")"
      pure $ Located
        (SourceSpan
          (sourceSpanStart (locatedSpan start))
          (sourceSpanEnd (locatedSpan end)))
        (locatedValue proposition)
    Just _ -> parseRelationProposition
    Nothing -> failParser "expected proposition at end of input"

parseRelationProposition :: Parser (Located GrammarV1Proposition)
parseRelationProposition = do
  left <- parseExpression
  operator <- parseRelationOperator
  right <- parseExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan left))
      (sourceSpanEnd (locatedSpan right)))
    (GrammarV1RelationProposition left operator right)

parseRelationOperator :: Parser (Located GrammarV1RelationOperator)
parseRelationOperator = do
  token <- takeToken
  let relation = case locatedValue token of
        GrammarSymbol "==" -> Just GrammarV1EqualRelation
        GrammarSymbol "!=" -> Just GrammarV1NotEqualRelation
        GrammarSymbol "<=" -> Just GrammarV1LessEqualRelation
        GrammarSymbol ">=" -> Just GrammarV1GreaterEqualRelation
        GrammarSymbol "<" -> Just GrammarV1LessRelation
        GrammarSymbol ">" -> Just GrammarV1GreaterRelation
        GrammarKeyword "in" -> Just GrammarV1InRelation
        GrammarKeyword "disjoint" -> Just GrammarV1DisjointRelation
        _ -> Nothing
  case relation of
    Just value -> pure (Located (locatedSpan token) value)
    Nothing -> failAt token $
      "expected relation operator ==, !=, <=, >=, <, >, in, or disjoint; found "
        <> renderToken (locatedValue token)

parseOptionalMode :: Parser (Maybe GrammarV1StructuralMode)
parseOptionalMode = do
  hasMode <- peekKeyword "mode"
  if hasMode
    then do
      _ <- expectKeyword "mode"
      Just <$> parseStructuralMode
    else pure Nothing

parseStructuralMode :: Parser GrammarV1StructuralMode
parseStructuralMode = do
  token <- takeToken
  case locatedValue token of
    GrammarKeyword "unrestricted" -> pure GrammarV1Unrestricted
    GrammarKeyword "affine" -> pure GrammarV1Affine
    GrammarKeyword "linear" -> pure GrammarV1Linear
    other -> failAt token $
      "expected structural mode unrestricted, affine, or linear; found " <> renderToken other

parseFieldList :: Parser [Located GrammarV1Field]
parseFieldList = do
  atEnd <- peekSymbol "}"
  if atEnd
    then pure []
    else do
      first <- parseField
      rest <- parseMoreFields
      pure (first : rest)

parseMoreFields :: Parser [Located GrammarV1Field]
parseMoreFields = do
  hasComma <- peekSymbol ","
  if not hasComma
    then pure []
    else do
      _ <- expectSymbol ","
      atEnd <- peekSymbol "}"
      if atEnd
        then pure []
        else do
          value <- parseField
          rest <- parseMoreFields
          pure (value : rest)

parseField :: Parser (Located GrammarV1Field)
parseField = do
  name <- expectIdentifier
  _ <- expectSymbol ":"
  ty <- parseType
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan name))
      (sourceSpanEnd (locatedSpan ty)))
    GrammarV1Field
      { grammarV1FieldName = name
      , grammarV1FieldType = ty
      }

parseTypeList :: Parser [Located GrammarV1Type]
parseTypeList = do
  atEnd <- peekSymbol ")"
  if atEnd
    then pure []
    else do
      first <- parseType
      rest <- parseMoreTypes
      pure (first : rest)

parseMoreTypes :: Parser [Located GrammarV1Type]
parseMoreTypes = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "variant tuple payload does not admit a trailing comma"
        else do
          value <- parseType
          rest <- parseMoreTypes
          pure (value : rest)
    else pure []

parseType :: Parser (Located GrammarV1Type)
parseType = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "Unit") -> do
      value <- expectKeyword "Unit"
      pure (Located (locatedSpan value) GrammarV1UnitType)
    Just (GrammarKeyword "Bool") -> do
      value <- expectKeyword "Bool"
      pure (Located (locatedSpan value) GrammarV1BoolType)
    Just (GrammarUIntType _) -> do
      value <- takeToken
      case locatedValue value of
        GrammarUIntType width -> pure (Located (locatedSpan value) (GrammarV1UnsignedType width))
        _ -> failParser "internal UINT_TYPE dispatch error"
    Just (GrammarIdentifier _) -> do
      reference <- parseStaticReference
      pure $ Located (locatedSpan reference) $ GrammarV1NamedType (locatedValue reference)
    Just other -> failParser ("expected supported type_expression; found " <> renderToken other)
    Nothing -> failParser "expected type_expression at end of input"

parseStaticReference :: Parser (Located GrammarV1StaticReference)
parseStaticReference = do
  name <- parseQualifiedName
  present <- peekSymbol "["
  if present
    then do
      (arguments, end) <- parseStaticArguments
      pure $ Located
        (SourceSpan
          (sourceSpanStart (locatedSpan name))
          (sourceSpanEnd (locatedSpan end)))
        GrammarV1StaticReference
          { grammarV1StaticReferenceName = locatedValue name
          , grammarV1StaticReferenceArguments = arguments
          }
    else pure $ Located (locatedSpan name) GrammarV1StaticReference
      { grammarV1StaticReferenceName = locatedValue name
      , grammarV1StaticReferenceArguments = []
      }

parseStaticArguments :: Parser ([GrammarV1StaticArgument], Located GrammarV1Token)
parseStaticArguments = do
  _ <- expectSymbol "["
  atEnd <- peekSymbol "]"
  if atEnd
    then do
      end <- expectSymbol "]"
      pure ([], end)
    else do
      first <- parseStaticArgument
      rest <- parseMoreStaticArguments
      end <- expectSymbol "]"
      pure (first : rest, end)

parseMoreStaticArguments :: Parser [GrammarV1StaticArgument]
parseMoreStaticArguments = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol "]"
      if atEnd
        then failParser "static_arguments does not admit a trailing comma"
        else do
          value <- parseStaticArgument
          rest <- parseMoreStaticArguments
          pure (value : rest)
    else pure []

parseStaticArgument :: Parser GrammarV1StaticArgument
parseStaticArgument = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "Unit") -> GrammarV1StaticTypeArgument . locatedValue <$> parseType
    Just (GrammarKeyword "Bool") -> GrammarV1StaticTypeArgument . locatedValue <$> parseType
    Just (GrammarUIntType _) -> GrammarV1StaticTypeArgument . locatedValue <$> parseType
    Just (GrammarIdentifier _) -> GrammarV1StaticReferenceArgument . locatedValue <$> parseStaticReference
    Just (GrammarKeyword "true") -> expectKeyword "true" >> pure (GrammarV1StaticBoolArgument True)
    Just (GrammarKeyword "false") -> expectKeyword "false" >> pure (GrammarV1StaticBoolArgument False)
    Just (GrammarDecimalInteger _) -> do
      value <- takeToken
      case locatedValue value of
        GrammarDecimalInteger integer -> pure (GrammarV1StaticIntegerArgument integer)
        _ -> failParser "internal DECIMAL_INTEGER dispatch error"
    Just other -> failParser $
      "SURF-002 generic/static slice does not yet implement static_argument beginning with "
        <> renderToken other
    Nothing -> failParser "expected static_argument at end of input"

parseQualifiedName :: Parser (Located GrammarV1QualifiedName)
parseQualifiedName = do
  first <- expectIdentifier
  rest <- parseQualifiedTail
  let parts = first : rest
      lastPart = last parts
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan first))
      (sourceSpanEnd (locatedSpan lastPart)))
    (GrammarV1QualifiedName (map locatedValue parts))

parseQualifiedTail :: Parser [Located Text]
parseQualifiedTail = do
  hasDot <- peekSymbol "."
  if hasDot
    then do
      _ <- expectSymbol "."
      value <- expectIdentifier
      rest <- parseQualifiedTail
      pure (value : rest)
    else pure []

peekToken :: Parser (Maybe (Located GrammarV1Token))
peekToken = Parser $ \tokens -> Right (listToMaybe tokens, tokens)

peekKeyword :: Text -> Parser Bool
peekKeyword expected = do
  token <- peekToken
  pure $ case fmap locatedValue token of
    Just (GrammarKeyword actual) -> actual == expected
    _ -> False

peekSymbol :: Text -> Parser Bool
peekSymbol expected = do
  token <- peekToken
  pure $ case fmap locatedValue token of
    Just (GrammarSymbol actual) -> actual == expected
    _ -> False

takeToken :: Parser (Located GrammarV1Token)
takeToken = Parser $ \tokens -> case tokens of
  [] -> Left (GrammarV1SyntaxDiagnostic Nothing "unexpected end of input")
  token : rest -> Right (token, rest)

expectKeyword :: Text -> Parser (Located GrammarV1Token)
expectKeyword expected = satisfyToken
  ("keyword " <> expected)
  (\token -> token == GrammarKeyword expected)

expectSymbol :: Text -> Parser (Located GrammarV1Token)
expectSymbol expected = satisfyToken
  ("symbol " <> expected)
  (\token -> token == GrammarSymbol expected)

expectIdentifier :: Parser (Located Text)
expectIdentifier = do
  token <- satisfyToken "identifier" isIdentifier
  case locatedValue token of
    GrammarIdentifier value -> pure (Located (locatedSpan token) value)
    _ -> failParser "internal identifier dispatch error"
  where
    isIdentifier value = case value of
      GrammarIdentifier _ -> True
      _ -> False

expectString :: Parser (Located Text)
expectString = do
  token <- satisfyToken "string literal" isString
  case locatedValue token of
    GrammarString value -> pure (Located (locatedSpan token) value)
    _ -> failParser "internal string dispatch error"
  where
    isString value = case value of
      GrammarString _ -> True
      _ -> False

satisfyToken
  :: Text
  -> (GrammarV1Token -> Bool)
  -> Parser (Located GrammarV1Token)
satisfyToken description predicate = Parser $ \tokens -> case tokens of
  [] -> Left $ GrammarV1SyntaxDiagnostic Nothing ("expected " <> description <> " at end of input")
  token : rest
    | predicate (locatedValue token) -> Right (token, rest)
    | otherwise -> Left $ GrammarV1SyntaxDiagnostic
        (Just (locatedSpan token))
        ("expected " <> description <> "; found " <> renderToken (locatedValue token))

failParser :: Text -> Parser a
failParser message = Parser $ \tokens -> Left $ GrammarV1SyntaxDiagnostic
  (locatedSpan <$> listToMaybe tokens)
  message

failAt :: Located GrammarV1Token -> Text -> Parser a
failAt token message = Parser $ \_ -> Left $ GrammarV1SyntaxDiagnostic
  (Just (locatedSpan token))
  message

locatedBetween
  :: Located a
  -> Located b
  -> c
  -> Located c
locatedBetween start end value = Located
  (SourceSpan
    (sourceSpanStart (locatedSpan start))
    (sourceSpanEnd (locatedSpan end)))
  value

renderToken :: GrammarV1Token -> Text
renderToken token = case token of
  GrammarKeyword value -> "keyword " <> value
  GrammarIdentifier value -> "identifier " <> value
  GrammarUIntType value -> "UINT_TYPE " <> value
  GrammarDecimalInteger value -> "integer " <> value
  GrammarString value -> "string " <> Text.pack (show value)
  GrammarSymbol value -> "symbol " <> value