{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstFunctionComponent
  ( GrammarV1ReferenceFunctionComponentError (..)
  , GrammarV1ReferenceFunctionComponentDeclaration (..)
  , grammarV1ProductionFunctionComponentDeclaration
  , grammarV1ReferenceFunctionComponentDeclaration
  , grammarV1ProductionFunctionComponentDeclarations
  , grammarV1ReferenceFunctionComponentDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstBlockStructure
  ( GrammarV1ReferenceBlockCore
  , grammarV1ProductionBlockCore
  , grammarV1ReferenceBlockCore
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
import Phil.Surface.GrammarV1.ReferenceAstTermParams
  ( GrammarV1ReferenceTermParamCore
  , grammarV1ProductionTermParamCore
  , grammarV1ReferenceOptionalTermParamsCore
  , grammarV1ReferenceTermParamsCore
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

newtype GrammarV1ReferenceFunctionComponentError =
  GrammarV1ReferenceFunctionComponentError Text
  deriving (Eq, Show)

data GrammarV1ReferenceFunctionComponentDeclaration
  = GrammarV1ReferenceFunctionDeclarationCore
      Bool
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      [GrammarV1ReferenceTermParamCore]
      (Maybe GrammarV1ReferenceTypePayload)
      GrammarV1ReferenceTypePayload
      GrammarV1ReferenceBlockCore
  | GrammarV1ReferenceComponentDeclarationCore
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      (Maybe [GrammarV1ReferenceTermParamCore])
      (Maybe GrammarV1ReferenceTypePayload)
      GrammarV1ReferenceBlockCore
  deriving (Eq, Show)

grammarV1ProductionFunctionComponentDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceFunctionComponentDeclaration
grammarV1ProductionFunctionComponentDeclaration declaration = case declaration of
  GrammarV1FunctionDeclaration function ->
    Just (GrammarV1ReferenceFunctionDeclarationCore
      (grammarV1FunctionRecursive function)
      (locatedValue (grammarV1FunctionName function))
      (map (grammarV1ProductionGenericParamCore . locatedValue)
        (grammarV1FunctionGenericParams function))
      (map (grammarV1ProductionRequirementCore . locatedValue)
        (grammarV1FunctionRequirements function))
      (map (grammarV1ProductionTermParamCore . locatedValue)
        (grammarV1FunctionTermParams function))
      (fmap (grammarV1ProductionTypePayload . locatedValue)
        (grammarV1FunctionResultType function))
      (grammarV1ProductionTypePayload
        (locatedValue (grammarV1FunctionSatisfies function)))
      (grammarV1ProductionBlockCore (locatedValue (grammarV1FunctionBody function))))
  GrammarV1ComponentDeclaration component ->
    Just (GrammarV1ReferenceComponentDeclarationCore
      (locatedValue (grammarV1ComponentName component))
      (map (grammarV1ProductionGenericParamCore . locatedValue)
        (grammarV1ComponentGenericParams component))
      (map (grammarV1ProductionRequirementCore . locatedValue)
        (grammarV1ComponentRequirements component))
      (fmap (map (grammarV1ProductionTermParamCore . locatedValue))
        (grammarV1ComponentTermParams component))
      (fmap (grammarV1ProductionTypePayload . locatedValue)
        (grammarV1ComponentProvides component))
      (grammarV1ProductionBlockCore (locatedValue (grammarV1ComponentBody component))))
  _ -> Nothing

grammarV1ReferenceFunctionComponentDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError
      (Maybe GrammarV1ReferenceFunctionComponentDeclaration)
grammarV1ReferenceFunctionComponentDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 5 selected -> Just <$> parseFunction selected
    GrammarV1ReferenceAlternative 13 selected -> Just <$> parseComponent selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failFC ("declaration alternative out of range: " <> showText index)
    _ -> failFC "declaration body is not an alternative node"

parseFunction
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError
      GrammarV1ReferenceFunctionComponentDeclaration
parseFunction tree = do
  fields <- namedSequence "function_decl" tree
  case fields of
    [recursiveTree, fnKeyword, nameTree, genericTree, requirementsTree,
      termParamsTree, resultTree, satisfiesKeyword, satisfiesTree, blockTree] -> do
      recursive <- parseOptionalRecursive recursiveTree
      expectLiteral "fn" fnKeyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      generics <- mapCommon (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      termParams <- mapTermParams (grammarV1ReferenceTermParamsCore termParamsTree)
      resultType <- parseOptionalTypedClause "->" resultTree
      expectLiteral "satisfies" satisfiesKeyword
      satisfies <- mapType (grammarV1ReferenceTypePayload satisfiesTree)
      block <- mapBlock (grammarV1ReferenceBlockCore blockTree)
      pure (GrammarV1ReferenceFunctionDeclarationCore
        recursive name generics requirements termParams resultType satisfies block)
    _ -> failFC "function_decl body is not a ten-item sequence"

parseComponent
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError
      GrammarV1ReferenceFunctionComponentDeclaration
parseComponent tree = do
  fields <- namedSequence "component_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree, termParamsTree,
      providesTree, blockTree] -> do
      expectLiteral "component" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      generics <- mapCommon (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      termParams <- mapTermParams
        (grammarV1ReferenceOptionalTermParamsCore termParamsTree)
      provides <- parseOptionalTypedClause "provides" providesTree
      block <- mapBlock (grammarV1ReferenceBlockCore blockTree)
      pure (GrammarV1ReferenceComponentDeclarationCore
        name generics requirements termParams provides block)
    _ -> failFC "component_decl body is not a seven-item sequence"

parseOptionalRecursive
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError Bool
parseOptionalRecursive tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure False
  GrammarV1ReferenceOptionalSome payload -> expectLiteral "recursive" payload >> pure True
  _ -> failFC "recursive slot is not optional"

parseOptionalTypedClause
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError (Maybe GrammarV1ReferenceTypePayload)
parseOptionalTypedClause keyword tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence (keyword <> " type clause") payload
    case fields of
      [keywordTree, typeTree] -> do
        expectLiteral keyword keywordTree
        Just <$> mapType (grammarV1ReferenceTypePayload typeTree)
      _ -> failFC (keyword <> " type clause is not a two-item sequence")
  _ -> failFC (keyword <> " type clause slot is not optional")

grammarV1ProductionFunctionComponentDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceFunctionComponentDeclaration]
grammarV1ProductionFunctionComponentDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , Just value <-
      [grammarV1ProductionFunctionComponentDeclaration
        (locatedValue (grammarV1Declaration topLevel))]
  ]

grammarV1ReferenceFunctionComponentDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError
      [GrammarV1ReferenceFunctionComponentDeclaration]
grammarV1ReferenceFunctionComponentDeclarations tree = do
  fields <- namedSequence "source_file" tree
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failFC "source_file body is not a three-item sequence"

parseTopLevel
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError
      (Maybe GrammarV1ReferenceFunctionComponentDeclaration)
parseTopLevel tree = do
  fields <- namedSequence "top_level_decl" tree
  case fields of
    [_attributesTree, declarationTree] ->
      grammarV1ReferenceFunctionComponentDeclaration declarationTree
    _ -> failFC "top_level_decl body is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failFC
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failFC ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failFC (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failFC (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFunctionComponentError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failFC ("expected literal " <> expected <> ", got " <> actual)
  _ -> failFC ("expected literal " <> expected)

mapCommon
  :: Either GrammarV1ReferenceDeclarationCommonError a
  -> Either GrammarV1ReferenceFunctionComponentError a
mapCommon = mapNested "declaration-common"

mapTermParams :: Show e => Either e a -> Either GrammarV1ReferenceFunctionComponentError a
mapTermParams = mapNested "term-parameter"

mapType :: Show e => Either e a -> Either GrammarV1ReferenceFunctionComponentError a
mapType = mapNested "type"

mapBlock :: Show e => Either e a -> Either GrammarV1ReferenceFunctionComponentError a
mapBlock = mapNested "block"

mapNested
  :: Show e
  => Text
  -> Either e a
  -> Either GrammarV1ReferenceFunctionComponentError a
mapNested label result = case result of
  Left errorValue -> failFC
    (label <> " correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failFC
  :: Text
  -> Either GrammarV1ReferenceFunctionComponentError a
failFC = Left . GrammarV1ReferenceFunctionComponentError
