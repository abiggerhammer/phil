{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstSpine
  ( GrammarV1ReferenceAstSpineError (..)
  , GrammarV1ReferenceImportSpine (..)
  , GrammarV1ReferenceSourceSpine (..)
  , grammarV1ProductionSourceSpine
  , grammarV1ReferenceSourceSpine
  ) where

import Data.Text (Text)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ImportDecl (..)
  , GrammarV1ModuleDecl (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1SourceFile (..)
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceAstSpineError = GrammarV1ReferenceAstSpineError Text
  deriving (Eq, Show)

data GrammarV1ReferenceImportSpine = GrammarV1ReferenceImportSpine
  { grammarV1ReferenceImportName :: GrammarV1QualifiedName
  , grammarV1ReferenceImportSelection :: Maybe [Text]
  }
  deriving (Eq, Show)

data GrammarV1ReferenceSourceSpine = GrammarV1ReferenceSourceSpine
  { grammarV1ReferenceModuleName :: Maybe GrammarV1QualifiedName
  , grammarV1ReferenceImports :: [GrammarV1ReferenceImportSpine]
  , grammarV1ReferenceTopLevelCount :: Int
  }
  deriving (Eq, Show)

grammarV1ProductionSourceSpine
  :: GrammarV1SourceFile
  -> GrammarV1ReferenceSourceSpine
grammarV1ProductionSourceSpine sourceFile = GrammarV1ReferenceSourceSpine
  { grammarV1ReferenceModuleName =
      fmap
        (locatedValue . grammarV1ModuleName . locatedValue)
        (grammarV1ModuleDecl sourceFile)
  , grammarV1ReferenceImports =
      map productionImportSpine (grammarV1ImportDecls sourceFile)
  , grammarV1ReferenceTopLevelCount =
      length (grammarV1TopLevelDecls sourceFile)
  }
  where
    productionImportSpine locatedImport =
      let importDecl = locatedValue locatedImport
      in GrammarV1ReferenceImportSpine
          { grammarV1ReferenceImportName =
              locatedValue (grammarV1ImportName importDecl)
          , grammarV1ReferenceImportSelection =
              fmap (map locatedValue) (grammarV1ImportSelection importDecl)
          }

grammarV1ReferenceSourceSpine
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError GrammarV1ReferenceSourceSpine
grammarV1ReferenceSourceSpine tree = do
  body <- expectNonterminal "source_file" tree
  fields <- expectSequence "source_file" body
  case fields of
    [moduleTree, importTree, topLevelTree] -> do
      moduleName <- parseOptionalModule moduleTree
      importTrees <- expectRepetition "source_file imports" importTree
      imports <- traverse parseImportDecl importTrees
      topLevelTrees <- expectRepetition "source_file top levels" topLevelTree
      traverse_ expectTopLevelDecl topLevelTrees
      pure GrammarV1ReferenceSourceSpine
        { grammarV1ReferenceModuleName = moduleName
        , grammarV1ReferenceImports = imports
        , grammarV1ReferenceTopLevelCount = length topLevelTrees
        }
    _ -> failSpine "source_file body is not a three-item sequence"

parseOptionalModule
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError (Maybe GrammarV1QualifiedName)
parseOptionalModule tree = case tree of
  GrammarV1ReferenceOptionalNone -> Right Nothing
  GrammarV1ReferenceOptionalSome body -> Just <$> parseModuleDecl body
  _ -> failSpine "source_file module slot is not an optional node"

parseModuleDecl
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError GrammarV1QualifiedName
parseModuleDecl tree = do
  body <- expectNonterminal "module_decl" tree
  fields <- expectSequence "module_decl" body
  case fields of
    [moduleKeyword, qualifiedName, terminator] -> do
      expectLiteral "module" moduleKeyword
      name <- parseQualifiedName qualifiedName
      expectLiteral ";" terminator
      pure name
    _ -> failSpine "module_decl body is not a three-item sequence"

parseImportDecl
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError GrammarV1ReferenceImportSpine
parseImportDecl tree = do
  body <- expectNonterminal "import_decl" tree
  fields <- expectSequence "import_decl" body
  case fields of
    [importKeyword, qualifiedName, selectionTree, terminator] -> do
      expectLiteral "import" importKeyword
      name <- parseQualifiedName qualifiedName
      selection <- parseOptionalImportSelection selectionTree
      expectLiteral ";" terminator
      pure GrammarV1ReferenceImportSpine
        { grammarV1ReferenceImportName = name
        , grammarV1ReferenceImportSelection = selection
        }
    _ -> failSpine "import_decl body is not a four-item sequence"

parseOptionalImportSelection
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError (Maybe [Text])
parseOptionalImportSelection tree = case tree of
  GrammarV1ReferenceOptionalNone -> Right Nothing
  GrammarV1ReferenceOptionalSome body -> do
    fields <- expectSequence "import selection" body
    case fields of
      [openBrace, identifiers, closeBrace] -> do
        expectLiteral "{" openBrace
        values <- parseIdentifierList identifiers
        expectLiteral "}" closeBrace
        pure (Just values)
      _ -> failSpine "import selection is not a three-item sequence"
  _ -> failSpine "import selection slot is not an optional node"

parseQualifiedName
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError GrammarV1QualifiedName
parseQualifiedName tree = do
  body <- expectNonterminal "qualified_name" tree
  fields <- expectSequence "qualified_name" body
  case fields of
    [firstTree, restTree] -> do
      first <- parseIdentifier firstTree
      restItems <- expectRepetition "qualified_name suffix" restTree
      rest <- traverse parseQualifiedNameSuffix restItems
      pure (GrammarV1QualifiedName (first : rest))
    _ -> failSpine "qualified_name body is not a two-item sequence"

parseQualifiedNameSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError Text
parseQualifiedNameSuffix tree = do
  fields <- expectSequence "qualified_name suffix item" tree
  case fields of
    [dot, identifier] -> do
      expectLiteral "." dot
      parseIdentifier identifier
    _ -> failSpine "qualified_name suffix item is not a two-item sequence"

parseIdentifierList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError [Text]
parseIdentifierList tree = do
  body <- expectNonterminal "identifier_list" tree
  fields <- expectSequence "identifier_list" body
  case fields of
    [firstTree, restTree] -> do
      first <- parseIdentifier firstTree
      restItems <- expectRepetition "identifier_list suffix" restTree
      rest <- traverse parseIdentifierListSuffix restItems
      pure (first : rest)
    _ -> failSpine "identifier_list body is not a two-item sequence"

parseIdentifierListSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError Text
parseIdentifierListSuffix tree = do
  fields <- expectSequence "identifier_list suffix item" tree
  case fields of
    [comma, identifier] -> do
      expectLiteral "," comma
      parseIdentifier identifier
    _ -> failSpine "identifier_list suffix item is not a two-item sequence"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failSpine ("identifier uses lexical class " <> className)
    _ -> failSpine "identifier body is not an IDENTIFIER lexical leaf"

expectTopLevelDecl
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError ()
expectTopLevelDecl tree = do
  _ <- expectNonterminal "top_level_decl" tree
  pure ()

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failSpine
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failSpine ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failSpine (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failSpine (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceAstSpineError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failSpine
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failSpine ("expected literal " <> expected)

traverse_
  :: (a -> Either e ())
  -> [a]
  -> Either e ()
traverse_ action values = case values of
  [] -> Right ()
  value : rest -> action value >> traverse_ action rest

failSpine :: Text -> Either GrammarV1ReferenceAstSpineError a
failSpine = Left . GrammarV1ReferenceAstSpineError
