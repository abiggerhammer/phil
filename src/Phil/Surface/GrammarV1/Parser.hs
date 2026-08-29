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
  , GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1OutcomeKind (..)
  , GrammarV1OutcomeSpec (..)
  , GrammarV1StateSlot (..)
  , GrammarV1CalleeTransition (..)
  , GrammarV1OutcomeResidueClause (..)
  , GrammarV1OutcomeResidue (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1CapabilityItem (..)
  , GrammarV1CapabilityDecl (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1ProtocolDecl (..)
  , GrammarV1TermParam (..)
  , GrammarV1Pattern (..)
  , GrammarV1FieldBinder (..)
  , GrammarV1CaseBinders (..)
  , GrammarV1CasePattern (..)
  , GrammarV1MatchArmBody (..)
  , GrammarV1MatchArm (..)
  , GrammarV1JoinClause (..)
  , GrammarV1StateBinding (..)
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
  | GrammarV1CallableContractDeclaration GrammarV1CallableContractDecl
  | GrammarV1FunctionDeclaration GrammarV1FunctionDecl
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
  | GrammarV1ClaimApplicationProposition
      GrammarV1StaticReference
      [Located GrammarV1Expression]
  | GrammarV1NotProposition (Located GrammarV1Proposition)
  | GrammarV1AndProposition
      (Located GrammarV1Proposition)
      (Located GrammarV1Proposition)
  | GrammarV1OrProposition
      (Located GrammarV1Proposition)
      (Located GrammarV1Proposition)
  deriving (Eq, Ord, Show)

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
  | GrammarV1BytesType (Located GrammarV1Expression)
  | GrammarV1ProofType (Located GrammarV1Proposition)
  | GrammarV1RefinementType
      (Located Text)
      (Located GrammarV1Type)
      (Located GrammarV1Proposition)
  | GrammarV1TupleType [Located GrammarV1Type]
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

data GrammarV1OutcomeKind
  = GrammarV1SuccessOutcome
  | GrammarV1NegativeOutcome
  | GrammarV1TerminalOutcome
  | GrammarV1FatalOutcome
  deriving (Eq, Ord, Show)

data GrammarV1OutcomeSpec = GrammarV1OutcomeSpec
  { grammarV1OutcomeSpecKind :: Located GrammarV1OutcomeKind
  , grammarV1OutcomeSpecType :: Located GrammarV1Type
  }
  deriving (Eq, Show)

data GrammarV1StateSlot = GrammarV1StateSlot
  { grammarV1StateSlotName :: Located Text
  , grammarV1StateSlotType :: Located GrammarV1Type
  }
  deriving (Eq, Ord, Show)

data GrammarV1CalleeTransition
  = GrammarV1CalleePreserve
  | GrammarV1CalleeConsume
  | GrammarV1CalleeReplace
      (Located GrammarV1StaticReference)
      (Maybe (Located GrammarV1Expression))
  deriving (Eq, Show)

data GrammarV1OutcomeResidueClause
  = GrammarV1OutcomeState [Located GrammarV1StateSlot]
  | GrammarV1OutcomeCallee (Located GrammarV1CalleeTransition)
  | GrammarV1OutcomeEnsures (Located GrammarV1Proposition)
  | GrammarV1OutcomeObligation (Located GrammarV1Proposition)
  deriving (Eq, Show)

data GrammarV1OutcomeResidue = GrammarV1OutcomeResidue
  { grammarV1OutcomeResidueKind :: Located GrammarV1OutcomeKind
  , grammarV1OutcomeResidueType :: Located GrammarV1Type
  , grammarV1OutcomeResidueClauses :: [Located GrammarV1OutcomeResidueClause]
  }
  deriving (Eq, Show)

data GrammarV1CallableClause
  = GrammarV1CallableEnsures (Located GrammarV1Proposition)
  | GrammarV1CallableOutcomes [Located GrammarV1OutcomeSpec]
  | GrammarV1CallableOutcomeResidue (Located GrammarV1OutcomeResidue)
  | GrammarV1CallableObligation (Located GrammarV1Proposition)
  | GrammarV1CallableCallee (Located GrammarV1CalleeTransition)
  deriving (Eq, Show)

data GrammarV1CallableContractDecl = GrammarV1CallableContractDecl
  { grammarV1CallableName :: Located Text
  , grammarV1CallableGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1CallableRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1CallableTermParams :: [Located GrammarV1TermParam]
  , grammarV1CallableResultType :: Located GrammarV1Type
  , grammarV1CallableClauses :: [Located GrammarV1CallableClause]
  }
  deriving (Eq, Show)

data GrammarV1FunctionDecl = GrammarV1FunctionDecl
  { grammarV1FunctionRecursive :: Bool
  , grammarV1FunctionName :: Located Text
  , grammarV1FunctionGenericParams :: [Located GrammarV1GenericParam]
  , grammarV1FunctionRequirements :: [Located GrammarV1GenericRequirement]
  , grammarV1FunctionTermParams :: [Located GrammarV1TermParam]
  , grammarV1FunctionResultType :: Maybe (Located GrammarV1Type)
  , grammarV1FunctionSatisfies :: Located GrammarV1Type
  , grammarV1FunctionBody :: Located GrammarV1Block
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
  deriving (Eq, Ord, Show)

data GrammarV1FieldBinder = GrammarV1FieldBinder
  { grammarV1FieldBinderField :: Located Text
  , grammarV1FieldBinderAlias :: Maybe (Located Text)
  }
  deriving (Eq, Ord, Show)

data GrammarV1CaseBinders
  = GrammarV1TupleCaseBinders [Located Text]
  | GrammarV1RecordCaseBinders [Located GrammarV1FieldBinder]
  deriving (Eq, Ord, Show)

data GrammarV1CasePattern = GrammarV1CasePattern
  { grammarV1CasePatternName :: Located GrammarV1QualifiedName
  , grammarV1CasePatternBinders :: Maybe GrammarV1CaseBinders
  }
  deriving (Eq, Ord, Show)

data GrammarV1MatchArmBody
  = GrammarV1MatchArmBlock (Located GrammarV1Block)
  | GrammarV1MatchArmStatement (Located GrammarV1Statement)
  deriving (Eq, Ord, Show)

data GrammarV1MatchArm = GrammarV1MatchArm
  { grammarV1MatchArmPattern :: Located GrammarV1CasePattern
  , grammarV1MatchArmBody :: GrammarV1MatchArmBody
  }
  deriving (Eq, Ord, Show)

data GrammarV1JoinClause = GrammarV1JoinClause
  { grammarV1JoinState :: [Located GrammarV1StateSlot]
  , grammarV1JoinInvariant :: Maybe (Located GrammarV1Proposition)
  }
  deriving (Eq, Ord, Show)

data GrammarV1StateBinding = GrammarV1StateBinding
  { grammarV1StateBindingName :: Located Text
  , grammarV1StateBindingType :: Maybe (Located GrammarV1Type)
  , grammarV1StateBindingInitializer :: Located GrammarV1Expression
  }
  deriving (Eq, Ord, Show)

data GrammarV1Expression
  = GrammarV1NameExpression GrammarV1StaticReference [Located GrammarV1Expression]
  | GrammarV1BoolExpression Bool
  | GrammarV1UnitExpression
  | GrammarV1IntegerExpression Text
  | GrammarV1TransportExpression
      (Located GrammarV1Expression)
      (Located GrammarV1Type)
      (Located GrammarV1Expression)
  | GrammarV1TupleExpression [Located GrammarV1Expression]
  | GrammarV1ParenthesizedExpression (Located GrammarV1Expression)
  | GrammarV1OfferExpression
      (Located GrammarV1Expression)
      [Located GrammarV1MatchArm]
  | GrammarV1IfExpression
      (Located GrammarV1Expression)
      (Maybe (Located GrammarV1JoinClause))
      (Located GrammarV1Block)
      (Maybe (Located GrammarV1Block))
  | GrammarV1LoopExpression
      [Located GrammarV1StateBinding]
      (Maybe (Located GrammarV1Proposition))
      (Located GrammarV1Block)
  | GrammarV1ContinueExpression [Located GrammarV1Expression]
  deriving (Eq, Ord, Show)

data GrammarV1Statement
  = GrammarV1LetStatement (Located GrammarV1Pattern) (Located GrammarV1Expression)
  | GrammarV1ReturnStatement (Located GrammarV1Expression)
  | GrammarV1ExpressionStatement (Located GrammarV1Expression)
  deriving (Eq, Ord, Show)

newtype GrammarV1Block = GrammarV1Block
  { grammarV1BlockStatements :: [Located GrammarV1Statement]
  }
  deriving (Eq, Ord, Show)

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
    Just (GrammarKeyword "callable") -> parseCallableContractDeclaration
    Just (GrammarKeyword "fn") -> parseFunctionDeclaration
    Just (GrammarKeyword "recursive") -> parseFunctionDeclaration
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

parseCallableContractDeclaration :: Parser (Located GrammarV1Declaration)
parseCallableContractDeclaration = do
  start <- expectKeyword "callable"
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  requirements <- parseOptionalGenericRequirements
  termParams <- parseTermParams
  _ <- expectSymbol "->"
  resultType <- parseType
  _ <- expectSymbol "{"
  clauses <- parseCallableClauses
  end <- expectSymbol "}"
  pure $ locatedBetween start end $
    GrammarV1CallableContractDeclaration GrammarV1CallableContractDecl
      { grammarV1CallableName = name
      , grammarV1CallableGenericParams = params
      , grammarV1CallableRequirements = requirements
      , grammarV1CallableTermParams = termParams
      , grammarV1CallableResultType = resultType
      , grammarV1CallableClauses = clauses
      }

parseCallableClauses :: Parser [Located GrammarV1CallableClause]
parseCallableClauses = do
  atEnd <- peekSymbol "}"
  if atEnd
    then pure []
    else do
      clause <- parseCallableClause
      rest <- parseCallableClauses
      pure (clause : rest)

parseCallableClause :: Parser (Located GrammarV1CallableClause)
parseCallableClause = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "ensures") ->
      parseCallablePropositionClause "ensures" GrammarV1CallableEnsures
    Just (GrammarKeyword "obligation") ->
      parseCallablePropositionClause "obligation" GrammarV1CallableObligation
    Just (GrammarKeyword "outcomes") -> do
      start <- expectKeyword "outcomes"
      specs <- parseOutcomeSet
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1CallableOutcomes specs)
    Just (GrammarKeyword "outcome") -> do
      residue <- parseOutcomeResidue
      pure $ Located
        (locatedSpan residue)
        (GrammarV1CallableOutcomeResidue residue)
    Just (GrammarKeyword "callee") -> do
      start <- expectKeyword "callee"
      transition <- parseCalleeTransition
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1CallableCallee transition)
    Just other -> failParser $
      "SURF-002 outcome/callee slice does not yet implement callable_clause beginning with "
        <> renderToken other
    Nothing -> failParser "unterminated callable contract declaration"

parseCallablePropositionClause
  :: Text
  -> (Located GrammarV1Proposition -> GrammarV1CallableClause)
  -> Parser (Located GrammarV1CallableClause)
parseCallablePropositionClause keyword constructor = do
  start <- expectKeyword keyword
  proposition <- parseProposition
  end <- expectSymbol ";"
  pure $ locatedBetween start end (constructor proposition)

parseOutcomeSet :: Parser [Located GrammarV1OutcomeSpec]
parseOutcomeSet = do
  _ <- expectSymbol "{"
  atEnd <- peekSymbol "}"
  if atEnd
    then expectSymbol "}" >> pure []
    else do
      first <- parseOutcomeSpec
      rest <- parseMoreOutcomeSpecs
      _ <- expectSymbol "}"
      pure (first : rest)

parseMoreOutcomeSpecs :: Parser [Located GrammarV1OutcomeSpec]
parseMoreOutcomeSpecs = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol "}"
      if atEnd
        then failParser "outcome_set does not admit a trailing comma"
        else do
          spec <- parseOutcomeSpec
          rest <- parseMoreOutcomeSpecs
          pure (spec : rest)
    else pure []

parseOutcomeSpec :: Parser (Located GrammarV1OutcomeSpec)
parseOutcomeSpec = do
  kind <- parseOutcomeKind
  ty <- parseType
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan kind))
      (sourceSpanEnd (locatedSpan ty)))
    GrammarV1OutcomeSpec
      { grammarV1OutcomeSpecKind = kind
      , grammarV1OutcomeSpecType = ty
      }

parseOutcomeKind :: Parser (Located GrammarV1OutcomeKind)
parseOutcomeKind = do
  token <- takeToken
  case locatedValue token of
    GrammarKeyword "success" -> pure (Located (locatedSpan token) GrammarV1SuccessOutcome)
    GrammarKeyword "negative" -> pure (Located (locatedSpan token) GrammarV1NegativeOutcome)
    GrammarKeyword "terminal" -> pure (Located (locatedSpan token) GrammarV1TerminalOutcome)
    GrammarKeyword "fatal" -> pure (Located (locatedSpan token) GrammarV1FatalOutcome)
    other -> failAt token $
      "expected outcome kind success, negative, terminal, or fatal; found " <> renderToken other

parseOutcomeResidue :: Parser (Located GrammarV1OutcomeResidue)
parseOutcomeResidue = do
  start <- expectKeyword "outcome"
  kind <- parseOutcomeKind
  ty <- parseType
  _ <- expectSymbol "{"
  clauses <- parseOutcomeResidueClauses
  end <- expectSymbol "}"
  pure $ locatedBetween start end GrammarV1OutcomeResidue
    { grammarV1OutcomeResidueKind = kind
    , grammarV1OutcomeResidueType = ty
    , grammarV1OutcomeResidueClauses = clauses
    }

parseOutcomeResidueClauses :: Parser [Located GrammarV1OutcomeResidueClause]
parseOutcomeResidueClauses = do
  atEnd <- peekSymbol "}"
  if atEnd
    then pure []
    else do
      clause <- parseOutcomeResidueClause
      rest <- parseOutcomeResidueClauses
      pure (clause : rest)

parseOutcomeResidueClause :: Parser (Located GrammarV1OutcomeResidueClause)
parseOutcomeResidueClause = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "state") -> parseOutcomeStateClause
    Just (GrammarKeyword "callee") -> do
      start <- expectKeyword "callee"
      transition <- parseCalleeTransition
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1OutcomeCallee transition)
    Just (GrammarKeyword "ensures") ->
      parseOutcomePropositionClause "ensures" GrammarV1OutcomeEnsures
    Just (GrammarKeyword "obligation") ->
      parseOutcomePropositionClause "obligation" GrammarV1OutcomeObligation
    Just other -> failParser $
      "expected outcome residue clause; found " <> renderToken other
    Nothing -> failParser "unterminated outcome residue"

parseOutcomePropositionClause
  :: Text
  -> (Located GrammarV1Proposition -> GrammarV1OutcomeResidueClause)
  -> Parser (Located GrammarV1OutcomeResidueClause)
parseOutcomePropositionClause keyword constructor = do
  start <- expectKeyword keyword
  proposition <- parseProposition
  end <- expectSymbol ";"
  pure $ locatedBetween start end (constructor proposition)

parseOutcomeStateClause :: Parser (Located GrammarV1OutcomeResidueClause)
parseOutcomeStateClause = do
  start <- expectKeyword "state"
  _ <- expectSymbol "("
  atEnd <- peekSymbol ")"
  slots <- if atEnd
    then pure []
    else do
      first <- parseStateSlot
      rest <- parseMoreStateSlots
      pure (first : rest)
  _ <- expectSymbol ")"
  end <- expectSymbol ";"
  pure $ locatedBetween start end (GrammarV1OutcomeState slots)

parseMoreStateSlots :: Parser [Located GrammarV1StateSlot]
parseMoreStateSlots = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "state slot list does not admit a trailing comma"
        else do
          slot <- parseStateSlot
          rest <- parseMoreStateSlots
          pure (slot : rest)
    else pure []

parseStateSlot :: Parser (Located GrammarV1StateSlot)
parseStateSlot = do
  name <- expectIdentifier
  _ <- expectSymbol ":"
  ty <- parseType
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan name))
      (sourceSpanEnd (locatedSpan ty)))
    GrammarV1StateSlot
      { grammarV1StateSlotName = name
      , grammarV1StateSlotType = ty
      }

parseCalleeTransition :: Parser (Located GrammarV1CalleeTransition)
parseCalleeTransition = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "preserve") -> do
      value <- expectKeyword "preserve"
      pure (Located (locatedSpan value) GrammarV1CalleePreserve)
    Just (GrammarKeyword "consume") -> do
      value <- expectKeyword "consume"
      pure (Located (locatedSpan value) GrammarV1CalleeConsume)
    Just (GrammarKeyword "replace") -> do
      start <- expectKeyword "replace"
      _ <- expectKeyword "with"
      replacement <- parseStaticReference
      hasState <- peekKeyword "state"
      successorState <- if hasState
        then expectKeyword "state" >> Just <$> parseExpression
        else pure Nothing
      let endSpan = case successorState of
            Just expression -> locatedSpan expression
            Nothing -> locatedSpan replacement
      pure $ Located
        (SourceSpan
          (sourceSpanStart (locatedSpan start))
          (sourceSpanEnd endSpan))
        (GrammarV1CalleeReplace replacement successorState)
    Just other -> failParser $
      "expected callee transition preserve, consume, or replace; found " <> renderToken other
    Nothing -> failParser "expected callee transition at end of input"

parseFunctionDeclaration :: Parser (Located GrammarV1Declaration)
parseFunctionDeclaration = do
  recursive <- peekKeyword "recursive"
  start <- if recursive then expectKeyword "recursive" else expectKeyword "fn"
  if recursive then do _ <- expectKeyword "fn"; pure () else pure ()
  name <- expectIdentifier
  params <- parseOptionalGenericParams
  requirements <- parseOptionalGenericRequirements
  termParams <- parseTermParams
  hasResult <- peekSymbol "->"
  resultType <- if hasResult
    then expectSymbol "->" >> Just <$> parseType
    else pure Nothing
  _ <- expectKeyword "satisfies"
  satisfiesType <- parseType
  body <- parseBlock
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan body)))
    (GrammarV1FunctionDeclaration GrammarV1FunctionDecl
      { grammarV1FunctionRecursive = recursive
      , grammarV1FunctionName = name
      , grammarV1FunctionGenericParams = params
      , grammarV1FunctionRequirements = requirements
      , grammarV1FunctionTermParams = termParams
      , grammarV1FunctionResultType = resultType
      , grammarV1FunctionSatisfies = satisfiesType
      , grammarV1FunctionBody = body
      })

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
    Just (GrammarKeyword "transport") -> parseTransportExpression
    Just (GrammarKeyword "offer") -> parseOfferExpression
    Just (GrammarKeyword "if") -> parseIfExpression
    Just (GrammarKeyword "loop") -> parseLoopExpression
    Just (GrammarKeyword "continue") -> parseContinueExpression
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
    Just (GrammarSymbol "(") -> parseTupleOrParenthesizedExpression
    Just (GrammarIdentifier _) -> parseNameExpression
    Just other -> failParser $
      "SURF-002 term/block slice does not yet implement expression beginning with "
        <> renderToken other
    Nothing -> failParser "expected expression at end of input"

parseTransportExpression :: Parser (Located GrammarV1Expression)
parseTransportExpression = do
  start <- expectKeyword "transport"
  value <- parseExpression
  _ <- expectKeyword "to"
  target <- parseType
  _ <- expectKeyword "using"
  evidence <- parseExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan evidence)))
    (GrammarV1TransportExpression value target evidence)

parseOfferExpression :: Parser (Located GrammarV1Expression)
parseOfferExpression = do
  start <- expectKeyword "offer"
  scrutinee <- parseExpression
  _ <- expectSymbol "{"
  atEnd <- peekSymbol "}"
  if atEnd
    then failParser "offer_expression requires at least one match_arm"
    else do
      first <- parseMatchArm
      rest <- parseMatchArms
      end <- expectSymbol "}"
      pure $ locatedBetween start end (GrammarV1OfferExpression scrutinee (first : rest))

parseMatchArms :: Parser [Located GrammarV1MatchArm]
parseMatchArms = do
  atEnd <- peekSymbol "}"
  if atEnd
    then pure []
    else do
      arm <- parseMatchArm
      rest <- parseMatchArms
      pure (arm : rest)

parseMatchArm :: Parser (Located GrammarV1MatchArm)
parseMatchArm = do
  pattern' <- parseCasePattern
  _ <- expectSymbol "=>"
  isBlock <- peekSymbol "{"
  body <- if isBlock
    then GrammarV1MatchArmBlock <$> parseBlock
    else GrammarV1MatchArmStatement <$> parseStatement
  let endSpan = case body of
        GrammarV1MatchArmBlock block -> locatedSpan block
        GrammarV1MatchArmStatement statement -> locatedSpan statement
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan pattern'))
      (sourceSpanEnd endSpan))
    GrammarV1MatchArm
      { grammarV1MatchArmPattern = pattern'
      , grammarV1MatchArmBody = body
      }

parseCasePattern :: Parser (Located GrammarV1CasePattern)
parseCasePattern = do
  name <- parseQualifiedName
  tupleBinders <- peekSymbol "("
  recordBinders <- peekSymbol "{"
  if tupleBinders
    then do
      (binders, end) <- parseCaseTupleBinders
      pure $ Located
        (SourceSpan
          (sourceSpanStart (locatedSpan name))
          (sourceSpanEnd (locatedSpan end)))
        GrammarV1CasePattern
          { grammarV1CasePatternName = name
          , grammarV1CasePatternBinders = Just (GrammarV1TupleCaseBinders binders)
          }
    else if recordBinders
      then do
        (binders, end) <- parseCaseRecordBinders
        pure $ Located
          (SourceSpan
            (sourceSpanStart (locatedSpan name))
            (sourceSpanEnd (locatedSpan end)))
          GrammarV1CasePattern
            { grammarV1CasePatternName = name
            , grammarV1CasePatternBinders = Just (GrammarV1RecordCaseBinders binders)
            }
      else pure $ Located (locatedSpan name) GrammarV1CasePattern
        { grammarV1CasePatternName = name
        , grammarV1CasePatternBinders = Nothing
        }

parseCaseTupleBinders :: Parser ([Located Text], Located GrammarV1Token)
parseCaseTupleBinders = do
  _ <- expectSymbol "("
  atEnd <- peekSymbol ")"
  if atEnd
    then do
      end <- expectSymbol ")"
      pure ([], end)
    else do
      first <- expectIdentifier
      rest <- parseMoreCaseTupleBinders
      end <- expectSymbol ")"
      pure (first : rest, end)

parseMoreCaseTupleBinders :: Parser [Located Text]
parseMoreCaseTupleBinders = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "case_pattern tuple binders do not admit a trailing comma"
        else do
          binder <- expectIdentifier
          rest <- parseMoreCaseTupleBinders
          pure (binder : rest)
    else pure []

parseCaseRecordBinders
  :: Parser ([Located GrammarV1FieldBinder], Located GrammarV1Token)
parseCaseRecordBinders = do
  _ <- expectSymbol "{"
  atEnd <- peekSymbol "}"
  if atEnd
    then do
      end <- expectSymbol "}"
      pure ([], end)
    else do
      first <- parseFieldBinder
      rest <- parseMoreFieldBinders
      end <- expectSymbol "}"
      pure (first : rest, end)

parseMoreFieldBinders :: Parser [Located GrammarV1FieldBinder]
parseMoreFieldBinders = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol "}"
      if atEnd
        then pure []
        else do
          binder <- parseFieldBinder
          rest <- parseMoreFieldBinders
          pure (binder : rest)
    else pure []

parseFieldBinder :: Parser (Located GrammarV1FieldBinder)
parseFieldBinder = do
  field <- expectIdentifier
  hasAlias <- peekKeyword "as"
  alias <- if hasAlias
    then expectKeyword "as" >> Just <$> expectIdentifier
    else pure Nothing
  let endSpan = maybe (locatedSpan field) locatedSpan alias
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan field))
      (sourceSpanEnd endSpan))
    GrammarV1FieldBinder
      { grammarV1FieldBinderField = field
      , grammarV1FieldBinderAlias = alias
      }

parseIfExpression :: Parser (Located GrammarV1Expression)
parseIfExpression = do
  start <- expectKeyword "if"
  condition <- parseExpression
  hasJoin <- peekKeyword "join"
  joinClause <- if hasJoin then Just <$> parseJoinClause else pure Nothing
  thenBlock <- parseBlock
  hasElse <- peekKeyword "else"
  elseBlock <- if hasElse
    then expectKeyword "else" >> Just <$> parseBlock
    else pure Nothing
  let endSpan = maybe (locatedSpan thenBlock) locatedSpan elseBlock
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd endSpan))
    (GrammarV1IfExpression condition joinClause thenBlock elseBlock)

parseJoinClause :: Parser (Located GrammarV1JoinClause)
parseJoinClause = do
  start <- expectKeyword "join"
  _ <- expectKeyword "state"
  _ <- expectSymbol "("
  atEnd <- peekSymbol ")"
  slots <- if atEnd
    then pure []
    else do
      first <- parseStateSlot
      rest <- parseMoreStateSlots
      pure (first : rest)
  endState <- expectSymbol ")"
  hasInvariant <- peekKeyword "invariant"
  invariant <- if hasInvariant
    then expectKeyword "invariant" >> Just <$> parseProposition
    else pure Nothing
  let endSpan = maybe (locatedSpan endState) locatedSpan invariant
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd endSpan))
    GrammarV1JoinClause
      { grammarV1JoinState = slots
      , grammarV1JoinInvariant = invariant
      }

parseLoopExpression :: Parser (Located GrammarV1Expression)
parseLoopExpression = do
  start <- expectKeyword "loop"
  hasState <- peekKeyword "state"
  bindings <- if hasState then parseLoopStateBindings else pure []
  hasInvariant <- peekKeyword "invariant"
  invariant <- if hasInvariant
    then expectKeyword "invariant" >> Just <$> parseProposition
    else pure Nothing
  body <- parseBlock
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan body)))
    (GrammarV1LoopExpression bindings invariant body)

parseLoopStateBindings :: Parser [Located GrammarV1StateBinding]
parseLoopStateBindings = do
  _ <- expectKeyword "state"
  _ <- expectSymbol "("
  atEnd <- peekSymbol ")"
  if atEnd
    then expectSymbol ")" >> pure []
    else do
      first <- parseStateBinding
      rest <- parseMoreStateBindings
      _ <- expectSymbol ")"
      pure (first : rest)

parseMoreStateBindings :: Parser [Located GrammarV1StateBinding]
parseMoreStateBindings = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "loop state bindings do not admit a trailing comma"
        else do
          binding <- parseStateBinding
          rest <- parseMoreStateBindings
          pure (binding : rest)
    else pure []

parseStateBinding :: Parser (Located GrammarV1StateBinding)
parseStateBinding = do
  name <- expectIdentifier
  hasType <- peekSymbol ":"
  ty <- if hasType
    then expectSymbol ":" >> Just <$> parseType
    else pure Nothing
  _ <- expectSymbol "="
  initializer <- parseExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan name))
      (sourceSpanEnd (locatedSpan initializer)))
    GrammarV1StateBinding
      { grammarV1StateBindingName = name
      , grammarV1StateBindingType = ty
      , grammarV1StateBindingInitializer = initializer
      }

parseContinueExpression :: Parser (Located GrammarV1Expression)
parseContinueExpression = do
  start <- expectKeyword "continue"
  hasArguments <- peekSymbol "("
  if hasArguments
    then do
      (arguments, end) <- parseTermArguments
      pure $ locatedBetween start end (GrammarV1ContinueExpression arguments)
    else pure $ Located (locatedSpan start) (GrammarV1ContinueExpression [])

parseTupleOrParenthesizedExpression :: Parser (Located GrammarV1Expression)
parseTupleOrParenthesizedExpression = do
  start <- expectSymbol "("
  first <- parseExpression
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "tuple_expression requires a second expression after comma"
        else do
          second <- parseExpression
          rest <- parseMoreTupleExpressions
          end <- expectSymbol ")"
          pure $ locatedBetween start end (GrammarV1TupleExpression (first : second : rest))
    else do
      end <- expectSymbol ")"
      pure $ locatedBetween start end (GrammarV1ParenthesizedExpression first)

parseMoreTupleExpressions :: Parser [Located GrammarV1Expression]
parseMoreTupleExpressions = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "tuple_expression does not admit a trailing comma"
        else do
          value <- parseExpression
          rest <- parseMoreTupleExpressions
          pure (value : rest)
    else pure []

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
    Just (GrammarIdentifier _) -> parseNamedPropositionAtom
    Just _ -> parseRelationProposition
    Nothing -> failParser "expected proposition at end of input"

parseNamedPropositionAtom :: Parser (Located GrammarV1Proposition)
parseNamedPropositionAtom = do
  reference <- parseStaticReference
  hasTermArguments <- peekSymbol "("
  if hasTermArguments
    then do
      (arguments, end) <- parseTermArguments
      let expression = Located
            (SourceSpan
              (sourceSpanStart (locatedSpan reference))
              (sourceSpanEnd (locatedSpan end)))
            (GrammarV1NameExpression (locatedValue reference) arguments)
      hasRelation <- peekRelationOperator
      if hasRelation
        then parseRelationFromLeft expression
        else pure $ Located
          (locatedSpan expression)
          (GrammarV1ClaimApplicationProposition (locatedValue reference) arguments)
    else do
      let expression = Located
            (locatedSpan reference)
            (GrammarV1NameExpression (locatedValue reference) [])
      parseRelationFromLeft expression

parseRelationProposition :: Parser (Located GrammarV1Proposition)
parseRelationProposition = do
  left <- parseExpression
  parseRelationFromLeft left

parseRelationFromLeft
  :: Located GrammarV1Expression
  -> Parser (Located GrammarV1Proposition)
parseRelationFromLeft left = do
  operator <- parseRelationOperator
  right <- parseExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan left))
      (sourceSpanEnd (locatedSpan right)))
    (GrammarV1RelationProposition left operator right)

peekRelationOperator :: Parser Bool
peekRelationOperator = do
  token <- peekToken
  pure $ case token of
    Just value -> case relationOperatorValue (locatedValue value) of
      Just _ -> True
      Nothing -> False
    Nothing -> False

parseRelationOperator :: Parser (Located GrammarV1RelationOperator)
parseRelationOperator = do
  token <- takeToken
  case relationOperatorValue (locatedValue token) of
    Just value -> pure (Located (locatedSpan token) value)
    Nothing -> failAt token $
      "expected relation operator ==, !=, <=, >=, <, >, in, or disjoint; found "
        <> renderToken (locatedValue token)

relationOperatorValue :: GrammarV1Token -> Maybe GrammarV1RelationOperator
relationOperatorValue token = case token of
  GrammarSymbol "==" -> Just GrammarV1EqualRelation
  GrammarSymbol "!=" -> Just GrammarV1NotEqualRelation
  GrammarSymbol "<=" -> Just GrammarV1LessEqualRelation
  GrammarSymbol ">=" -> Just GrammarV1GreaterEqualRelation
  GrammarSymbol "<" -> Just GrammarV1LessRelation
  GrammarSymbol ">" -> Just GrammarV1GreaterRelation
  GrammarKeyword "in" -> Just GrammarV1InRelation
  GrammarKeyword "disjoint" -> Just GrammarV1DisjointRelation
  _ -> Nothing

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
    Just (GrammarKeyword "Bytes") -> parseBytesType
    Just (GrammarKeyword "Proof") -> parseProofType
    Just (GrammarSymbol "{") -> parseRefinementType
    Just (GrammarSymbol "(") -> parseTupleType
    Just (GrammarIdentifier _) -> do
      reference <- parseStaticReference
      pure $ Located (locatedSpan reference) $ GrammarV1NamedType (locatedValue reference)
    Just other -> failParser ("expected supported type_expression; found " <> renderToken other)
    Nothing -> failParser "expected type_expression at end of input"

parseBytesType :: Parser (Located GrammarV1Type)
parseBytesType = do
  start <- expectKeyword "Bytes"
  _ <- expectSymbol "["
  lengthExpression <- parseExpression
  end <- expectSymbol "]"
  pure $ locatedBetween start end (GrammarV1BytesType lengthExpression)

parseProofType :: Parser (Located GrammarV1Type)
parseProofType = do
  start <- expectKeyword "Proof"
  _ <- expectSymbol "["
  proposition <- parseProposition
  end <- expectSymbol "]"
  pure $ locatedBetween start end (GrammarV1ProofType proposition)

parseRefinementType :: Parser (Located GrammarV1Type)
parseRefinementType = do
  start <- expectSymbol "{"
  binder <- expectIdentifier
  _ <- expectSymbol ":"
  baseType <- parseType
  _ <- expectSymbol "|"
  proposition <- parseProposition
  end <- expectSymbol "}"
  pure $ locatedBetween start end $
    GrammarV1RefinementType binder baseType proposition

parseTupleType :: Parser (Located GrammarV1Type)
parseTupleType = do
  start <- expectSymbol "("
  first <- parseType
  _ <- expectSymbol ","
  atEnd <- peekSymbol ")"
  if atEnd
    then failParser "tuple_type requires a second type after comma"
    else do
      second <- parseType
      rest <- parseMoreTupleTypes
      end <- expectSymbol ")"
      pure $ locatedBetween start end (GrammarV1TupleType (first : second : rest))

parseMoreTupleTypes :: Parser [Located GrammarV1Type]
parseMoreTupleTypes = do
  hasComma <- peekSymbol ","
  if hasComma
    then do
      _ <- expectSymbol ","
      atEnd <- peekSymbol ")"
      if atEnd
        then failParser "tuple_type does not admit a trailing comma"
        else do
          ty <- parseType
          rest <- parseMoreTupleTypes
          pure (ty : rest)
    else pure []

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
    Just (GrammarKeyword "Bytes") -> GrammarV1StaticTypeArgument . locatedValue <$> parseType
    Just (GrammarKeyword "Proof") -> GrammarV1StaticTypeArgument . locatedValue <$> parseType
    Just (GrammarSymbol "(") -> GrammarV1StaticTypeArgument . locatedValue <$> parseType
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
