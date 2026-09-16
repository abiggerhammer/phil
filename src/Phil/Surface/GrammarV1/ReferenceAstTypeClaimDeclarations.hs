{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstTypeClaimDeclarations
  ( GrammarV1ReferenceTypeClaimError (..)
  , GrammarV1ReferenceTypeClaimDeclaration (..)
  , grammarV1ProductionTypeClaimDeclaration
  , grammarV1ReferenceTypeClaimDeclaration
  , grammarV1ProductionTypeClaimDeclarations
  , grammarV1ReferenceTypeClaimDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ClaimDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceDeclarationCommonError
  , GrammarV1ReferenceGenericParamCore
  , GrammarV1ReferenceRequirementCore
  , grammarV1ProductionGenericParamCore
  , grammarV1ProductionRequirementCore
  , grammarV1ReferenceIdentifierCore
  , grammarV1ReferenceOptionalGenericParamsCore
  , grammarV1ReferenceOptionalRequirementsCore
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstTermParams
  ( GrammarV1ReferenceTermParamCore
  , grammarV1ProductionTermParamCore
  , grammarV1ReferenceOptionalTermParamsCore
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

newtype GrammarV1ReferenceTypeClaimError =
  GrammarV1ReferenceTypeClaimError Text
  deriving (Eq, Show)

data GrammarV1ReferenceTypeClaimDeclaration
  = GrammarV1ReferenceTypeAliasDeclarationCore
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceClaimDeclarationCore
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      (Maybe [GrammarV1ReferenceTermParamCore])
      (Maybe GrammarV1ReferencePropositionCore)
  deriving (Eq, Show)

grammarV1ProductionTypeClaimDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceTypeClaimDeclaration
grammarV1ProductionTypeClaimDeclaration declaration = case declaration of
  GrammarV1TypeAliasDeclaration alias ->
    Just (GrammarV1ReferenceTypeAliasDeclarationCore
      (locatedValue (grammarV1TypeAliasName alias))
      (map (grammarV1ProductionGenericParamCore . locatedValue)
        (grammarV1TypeAliasGenericParams alias))
      (map (grammarV1ProductionRequirementCore . locatedValue)
        (grammarV1TypeAliasRequirements alias))
      (grammarV1ProductionTypePayload (locatedValue (grammarV1TypeAliasTarget alias))))
  GrammarV1ClaimDeclaration claim ->
    Just (GrammarV1ReferenceClaimDeclarationCore
      (locatedValue (grammarV1ClaimName claim))
      (map (grammarV1ProductionGenericParamCore . locatedValue)
        (grammarV1ClaimGenericParams claim))
      (map (grammarV1ProductionRequirementCore . locatedValue)
        (grammarV1ClaimRequirements claim))
      (fmap (map (grammarV1ProductionTermParamCore . locatedValue))
        (grammarV1ClaimTermParams claim))
      (fmap (grammarV1ProductionPropositionCore . locatedValue)
        (grammarV1ClaimProposition claim)))
  _ -> Nothing

grammarV1ReferenceTypeClaimDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError
      (Maybe GrammarV1ReferenceTypeClaimDeclaration)
grammarV1ReferenceTypeClaimDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 2 selected -> Just <$> parseTypeAlias selected
    GrammarV1ReferenceAlternative 3 selected -> Just <$> parseClaim selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failTypeClaim
          ("declaration alternative out of range: " <> showText index)
    _ -> failTypeClaim "declaration body is not an alternative node"

parseTypeAlias
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError GrammarV1ReferenceTypeClaimDeclaration
parseTypeAlias tree = do
  fields <- namedSequence "type_alias_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree, equalsTree, targetTree, terminator] -> do
      expectLiteral "type" keyword
      name <- mapCommonError (grammarV1ReferenceIdentifierCore nameTree)
      generics <- mapCommonError
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommonError
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "=" equalsTree
      target <- mapTypeError (grammarV1ReferenceTypePayload targetTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceTypeAliasDeclarationCore
        name generics requirements target)
    _ -> failTypeClaim "type_alias_decl body is not a seven-item sequence"

parseClaim
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError GrammarV1ReferenceTypeClaimDeclaration
parseClaim tree = do
  fields <- namedSequence "claim_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree, termParamsTree, propositionTree, terminator] -> do
      expectLiteral "claim" keyword
      name <- mapCommonError (grammarV1ReferenceIdentifierCore nameTree)
      generics <- mapCommonError
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommonError
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      termParams <- mapTermParamsError
        (grammarV1ReferenceOptionalTermParamsCore termParamsTree)
      proposition <- parseOptionalProposition propositionTree
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceClaimDeclarationCore
        name generics requirements termParams proposition)
    _ -> failTypeClaim "claim_decl body is not a seven-item sequence"

parseOptionalProposition
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError (Maybe GrammarV1ReferencePropositionCore)
parseOptionalProposition tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "claim proposition clause" payload
    case fields of
      [equalsTree, propositionTree] -> do
        expectLiteral "=" equalsTree
        Just <$> mapPropositionError (grammarV1ReferencePropositionCore propositionTree)
      _ -> failTypeClaim "claim proposition clause is not a two-item sequence"
  _ -> failTypeClaim "claim proposition slot is not optional"

grammarV1ProductionTypeClaimDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceTypeClaimDeclaration]
grammarV1ProductionTypeClaimDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , Just value <-
      [grammarV1ProductionTypeClaimDeclaration
        (locatedValue (grammarV1Declaration topLevel))]
  ]

grammarV1ReferenceTypeClaimDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError
      [GrammarV1ReferenceTypeClaimDeclaration]
grammarV1ReferenceTypeClaimDeclarations tree = do
  fields <- namedSequence "source_file" tree
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failTypeClaim "source_file body is not a three-item sequence"

parseTopLevel
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError
      (Maybe GrammarV1ReferenceTypeClaimDeclaration)
parseTopLevel tree = do
  fields <- namedSequence "top_level_decl" tree
  case fields of
    [_attributesTree, declarationTree] ->
      grammarV1ReferenceTypeClaimDeclaration declarationTree
    _ -> failTypeClaim "top_level_decl body is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failTypeClaim
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failTypeClaim ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failTypeClaim (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failTypeClaim (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeClaimError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failTypeClaim
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failTypeClaim ("expected literal " <> expected)

mapCommonError
  :: Either GrammarV1ReferenceDeclarationCommonError a
  -> Either GrammarV1ReferenceTypeClaimError a
mapCommonError result = case result of
  Left errorValue -> failTypeClaim
    ("declaration-common correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

mapTermParamsError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceTypeClaimError a
mapTermParamsError result = case result of
  Left errorValue -> failTypeClaim
    ("term-parameter correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

mapTypeError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceTypeClaimError a
mapTypeError result = case result of
  Left errorValue -> failTypeClaim
    ("type correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

mapPropositionError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceTypeClaimError a
mapPropositionError result = case result of
  Left errorValue -> failTypeClaim
    ("proposition correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failTypeClaim
  :: Text
  -> Either GrammarV1ReferenceTypeClaimError a
failTypeClaim = Left . GrammarV1ReferenceTypeClaimError
