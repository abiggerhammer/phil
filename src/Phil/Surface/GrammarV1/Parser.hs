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
  , GrammarV1Type (..)
  , GrammarV1Field (..)
  , GrammarV1RecordDecl (..)
  , GrammarV1VariantPayload (..)
  , GrammarV1VariantDecl (..)
  , GrammarV1DataDecl (..)
  , GrammarV1CapabilityItem (..)
  , GrammarV1CapabilityDecl (..)
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

-- This is the first incremental production parser for Grammar v1.  It owns
-- the source-file/module/import/attribute framing and the complete structural
-- declaration subset used by the initial SURF-002 slice.  Unsupported valid
-- Grammar-v1 declaration families fail closed until their production parser
-- is added by a later slice; no balanced-token or recovery fallback exists.

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
  | GrammarV1CapabilityDeclaration GrammarV1CapabilityDecl
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

data GrammarV1Type
  = GrammarV1UnitType
  | GrammarV1BoolType
  | GrammarV1UnsignedType Text
  | GrammarV1NamedType GrammarV1QualifiedName
  deriving (Eq, Ord, Show)

data GrammarV1Field = GrammarV1Field
  { grammarV1FieldName :: Located Text
  , grammarV1FieldType :: Located GrammarV1Type
  }
  deriving (Eq, Show)

data GrammarV1RecordDecl = GrammarV1RecordDecl
  { grammarV1RecordName :: Located Text
  , grammarV1RecordMode :: Maybe GrammarV1StructuralMode
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
  , grammarV1DataMode :: Maybe GrammarV1StructuralMode
  , grammarV1DataVariants :: [Located GrammarV1VariantDecl]
  }
  deriving (Eq, Show)

data GrammarV1CapabilityItem
  = GrammarV1CapabilityPermits (Located GrammarV1QualifiedName)
  deriving (Eq, Show)

data GrammarV1CapabilityDecl = GrammarV1CapabilityDecl
  { grammarV1CapabilityName :: Located Text
  , grammarV1CapabilityMode :: GrammarV1StructuralMode
  , grammarV1CapabilityItems :: [Located GrammarV1CapabilityItem]
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
    Just (GrammarKeyword "capability") -> parseCapabilityDeclaration
    Just other -> failParser $
      "SURF-002 structural parser does not yet implement declaration production beginning with "
        <> renderToken other
    Nothing -> failParser "expected Grammar-v1 declaration at end of input"

parseRecordDeclaration :: Parser (Located GrammarV1Declaration)
parseRecordDeclaration = do
  start <- expectKeyword "record"
  name <- expectIdentifier
  rejectPendingGenericParams
  mode <- parseOptionalMode
  rejectPendingGenericRequirements
  _ <- expectSymbol "{"
  fields <- parseFieldList
  end <- expectSymbol "}"
  pure $ locatedBetween start end $ GrammarV1RecordDeclaration GrammarV1RecordDecl
    { grammarV1RecordName = name
    , grammarV1RecordMode = mode
    , grammarV1RecordFields = fields
    }

parseDataDeclaration :: Parser (Located GrammarV1Declaration)
parseDataDeclaration = do
  start <- expectKeyword "data"
  name <- expectIdentifier
  rejectPendingGenericParams
  mode <- parseOptionalMode
  rejectPendingGenericRequirements
  _ <- expectSymbol "="
  first <- parseVariantDecl
  rest <- parseMoreVariants
  end <- expectSymbol ";"
  pure $ locatedBetween start end $ GrammarV1DataDeclaration GrammarV1DataDecl
    { grammarV1DataName = name
    , grammarV1DataMode = mode
    , grammarV1DataVariants = first : rest
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
  rejectPendingGenericParams
  _ <- expectKeyword "mode"
  mode <- parseStructuralMode
  rejectPendingGenericRequirements
  _ <- expectSymbol "{"
  items <- parseCapabilityItems
  end <- expectSymbol "}"
  pure $ locatedBetween start end $ GrammarV1CapabilityDeclaration GrammarV1CapabilityDecl
    { grammarV1CapabilityName = name
    , grammarV1CapabilityMode = mode
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
      target <- parseStaticReferenceWithoutArguments
      end <- expectSymbol ";"
      pure $ locatedBetween start end (GrammarV1CapabilityPermits target)
    else do
      token <- peekToken
      case token of
        Just value -> failParser $
          "SURF-002 structural parser capability item not yet implemented: "
            <> renderToken (locatedValue value)
        Nothing -> failParser "unterminated capability declaration"

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
      name <- parseQualifiedName
      hasArguments <- peekSymbol "["
      if hasArguments
        then failParser "static_arguments in type expressions are not yet implemented by this SURF-002 slice"
        else pure $ Located (locatedSpan name) $ GrammarV1NamedType (locatedValue name)
    Just other -> failParser ("expected structural-slice type_expression; found " <> renderToken other)
    Nothing -> failParser "expected type_expression at end of input"

parseStaticReferenceWithoutArguments :: Parser (Located GrammarV1QualifiedName)
parseStaticReferenceWithoutArguments = do
  name <- parseQualifiedName
  hasArguments <- peekSymbol "["
  if hasArguments
    then failParser "static_arguments are not yet implemented by this SURF-002 slice"
    else pure name

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

rejectPendingGenericParams :: Parser ()
rejectPendingGenericParams = do
  present <- peekSymbol "["
  if present
    then failParser "generic_params are not yet implemented by the SURF-002 structural declaration slice"
    else pure ()

rejectPendingGenericRequirements :: Parser ()
rejectPendingGenericRequirements = do
  present <- peekKeyword "requires"
  if present
    then failParser "generic_requirements are not yet implemented by the SURF-002 structural declaration slice"
    else pure ()

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
