{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstProtocolDeclaration
  ( GrammarV1ReferenceProtocolDeclarationError (..)
  , GrammarV1ReferenceProtocolDeclarationCore (..)
  , grammarV1ProductionProtocolDeclaration
  , grammarV1ReferenceProtocolDeclaration
  , grammarV1ProductionProtocolDeclarations
  , grammarV1ReferenceProtocolDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceGenericParamCore
  , GrammarV1ReferenceRequirementCore
  , grammarV1ProductionGenericParamCore
  , grammarV1ProductionRequirementCore
  , grammarV1ReferenceIdentifierCore
  , grammarV1ReferenceOptionalGenericParamsCore
  , grammarV1ReferenceOptionalRequirementsCore
  )
import Phil.Surface.GrammarV1.ReferenceAstSessions
  ( GrammarV1ReferenceRoleSessionCore (..)
  , grammarV1ProductionSessionCore
  , grammarV1ReferenceSessionCore
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceProtocolDeclarationError =
  GrammarV1ReferenceProtocolDeclarationError Text
  deriving (Eq, Show)

data GrammarV1ReferenceProtocolDeclarationCore =
  GrammarV1ReferenceProtocolDeclarationCore
    { grammarV1ReferenceProtocolNameCore :: Text
    , grammarV1ReferenceProtocolGenericParamsCore :: [GrammarV1ReferenceGenericParamCore]
    , grammarV1ReferenceProtocolRequirementsCore :: [GrammarV1ReferenceRequirementCore]
    , grammarV1ReferenceProtocolRolesCore :: [GrammarV1ReferenceRoleSessionCore]
    }
  deriving (Eq, Show)

grammarV1ProductionProtocolDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceProtocolDeclarationCore
grammarV1ProductionProtocolDeclaration declaration = case declaration of
  GrammarV1ProtocolDeclaration protocol -> Just GrammarV1ReferenceProtocolDeclarationCore
    { grammarV1ReferenceProtocolNameCore =
        locatedValue (grammarV1ProtocolName protocol)
    , grammarV1ReferenceProtocolGenericParamsCore =
        map (grammarV1ProductionGenericParamCore . locatedValue)
          (grammarV1ProtocolGenericParams protocol)
    , grammarV1ReferenceProtocolRequirementsCore =
        map (grammarV1ProductionRequirementCore . locatedValue)
          (grammarV1ProtocolRequirements protocol)
    , grammarV1ReferenceProtocolRolesCore =
        map (productionRole . locatedValue) (grammarV1ProtocolRoles protocol)
    }
  _ -> Nothing

productionRole
  :: GrammarV1RoleSessionDecl
  -> GrammarV1ReferenceRoleSessionCore
productionRole role = GrammarV1ReferenceRoleSessionCore
  { grammarV1ReferenceRoleSessionName =
      locatedValue (grammarV1RoleSessionName role)
  , grammarV1ReferenceRoleSessionValue =
      grammarV1ProductionSessionCore
        (locatedValue (grammarV1RoleSessionExpression role))
  }

grammarV1ReferenceProtocolDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError
      (Maybe GrammarV1ReferenceProtocolDeclarationCore)
grammarV1ReferenceProtocolDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 9 selected -> Just <$> parseProtocol selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failProtocol
          ("declaration alternative out of range: " <> showText index)
    _ -> failProtocol "declaration body is not an alternative node"

parseProtocol
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError
      GrammarV1ReferenceProtocolDeclarationCore
parseProtocol tree = do
  fields <- namedSequence "protocol_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree,
      openBrace, firstRoleTree, secondRoleTree, closeBrace] -> do
      expectLiteral "protocol" keyword
      name <- mapNested "declaration-common"
        (grammarV1ReferenceIdentifierCore nameTree)
      generics <- mapNested "declaration-common"
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapNested "declaration-common"
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "{" openBrace
      firstRole <- parseRole firstRoleTree
      secondRole <- parseRole secondRoleTree
      expectLiteral "}" closeBrace
      pure GrammarV1ReferenceProtocolDeclarationCore
        { grammarV1ReferenceProtocolNameCore = name
        , grammarV1ReferenceProtocolGenericParamsCore = generics
        , grammarV1ReferenceProtocolRequirementsCore = requirements
        , grammarV1ReferenceProtocolRolesCore = [firstRole, secondRole]
        }
    _ -> failProtocol "protocol_decl body is not an eight-item sequence"

parseRole
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError GrammarV1ReferenceRoleSessionCore
parseRole tree = do
  fields <- namedSequence "role_session_decl" tree
  case fields of
    [keyword, nameTree, equalsTree, sessionTree, terminator] -> do
      expectLiteral "role" keyword
      name <- mapNested "declaration-common"
        (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral "=" equalsTree
      session <- mapNested "session"
        (grammarV1ReferenceSessionCore sessionTree)
      expectLiteral ";" terminator
      pure GrammarV1ReferenceRoleSessionCore
        { grammarV1ReferenceRoleSessionName = name
        , grammarV1ReferenceRoleSessionValue = session
        }
    _ -> failProtocol "role_session_decl body is not a five-item sequence"

grammarV1ProductionProtocolDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceProtocolDeclarationCore]
grammarV1ProductionProtocolDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let declaration =
          locatedValue (grammarV1Declaration (locatedValue locatedTopLevel))
  , Just value <- [grammarV1ProductionProtocolDeclaration declaration]
  ]

grammarV1ReferenceProtocolDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError
      [GrammarV1ReferenceProtocolDeclarationCore]
grammarV1ReferenceProtocolDeclarations tree = do
  fields <- namedSequence "source_file" tree
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failProtocol "source_file body is not a three-item sequence"
  where
    parseTopLevel topLevelTree = do
      topFields <- namedSequence "top_level_decl" topLevelTree
      case topFields of
        [_attributesTree, declarationTree] ->
          grammarV1ReferenceProtocolDeclaration declarationTree
        _ -> failProtocol "top_level_decl body is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failProtocol
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failProtocol ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failProtocol (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failProtocol (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProtocolDeclarationError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failProtocol
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failProtocol ("expected literal " <> expected)

mapNested
  :: Show e
  => Text
  -> Either e a
  -> Either GrammarV1ReferenceProtocolDeclarationError a
mapNested label result = case result of
  Left errorValue -> failProtocol
    (label <> " correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failProtocol
  :: Text
  -> Either GrammarV1ReferenceProtocolDeclarationError a
failProtocol = Left . GrammarV1ReferenceProtocolDeclarationError
