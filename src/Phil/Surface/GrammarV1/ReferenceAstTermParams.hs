{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstTermParams
  ( GrammarV1ReferenceTermParamsError (..)
  , GrammarV1ReferenceTermParamCore (..)
  , grammarV1ProductionTermParamCore
  , grammarV1ReferenceTermParamCore
  , grammarV1ReferenceTermParamsCore
  , grammarV1ReferenceOptionalTermParamsCore
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1TermParam (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceDeclarationCommonError
  , grammarV1ReferenceIdentifierCore
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

newtype GrammarV1ReferenceTermParamsError =
  GrammarV1ReferenceTermParamsError Text
  deriving (Eq, Show)

data GrammarV1ReferenceTermParamCore = GrammarV1ReferenceTermParamCore
  { grammarV1ReferenceTermParamNameCore :: Text
  , grammarV1ReferenceTermParamTypeCore :: GrammarV1ReferenceTypePayload
  }
  deriving (Eq, Show)

grammarV1ProductionTermParamCore
  :: GrammarV1TermParam
  -> GrammarV1ReferenceTermParamCore
grammarV1ProductionTermParamCore parameter = GrammarV1ReferenceTermParamCore
  { grammarV1ReferenceTermParamNameCore = locatedValue (grammarV1TermParamName parameter)
  , grammarV1ReferenceTermParamTypeCore =
      grammarV1ProductionTypePayload (locatedValue (grammarV1TermParamType parameter))
  }

grammarV1ReferenceTermParamCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError GrammarV1ReferenceTermParamCore
grammarV1ReferenceTermParamCore tree = do
  body <- expectNonterminal "term_param" tree
  fields <- expectSequence "term_param" body
  case fields of
    [nameTree, colon, typeTree] -> do
      name <- mapCommonError (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral ":" colon
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      pure GrammarV1ReferenceTermParamCore
        { grammarV1ReferenceTermParamNameCore = name
        , grammarV1ReferenceTermParamTypeCore = sourceType
        }
    _ -> failTermParams "term_param body is not a three-item sequence"

grammarV1ReferenceTermParamsCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError [GrammarV1ReferenceTermParamCore]
grammarV1ReferenceTermParamsCore tree = do
  body <- expectNonterminal "term_params" tree
  fields <- expectSequence "term_params" body
  case fields of
    [openParen, optionalValues, closeParen] -> do
      expectLiteral "(" openParen
      values <- case optionalValues of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome valuesTree -> do
          valueFields <- expectSequence "term_params values" valuesTree
          case valueFields of
            [firstTree, restTree] -> do
              first <- grammarV1ReferenceTermParamCore firstTree
              rest <- expectRepetition "term_params suffixes" restTree
                >>= traverse parseTermParamSuffix
              pure (first : rest)
            _ -> failTermParams "term_params values are not a two-item sequence"
        _ -> failTermParams "term_params values slot is not optional"
      expectLiteral ")" closeParen
      pure values
    _ -> failTermParams "term_params body is not a three-item sequence"

grammarV1ReferenceOptionalTermParamsCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError (Maybe [GrammarV1ReferenceTermParamCore])
grammarV1ReferenceOptionalTermParamsCore tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome paramsTree ->
    Just <$> grammarV1ReferenceTermParamsCore paramsTree
  _ -> failTermParams "term-parameter slot is not optional"

parseTermParamSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError GrammarV1ReferenceTermParamCore
parseTermParamSuffix tree = do
  fields <- expectSequence "term_params suffix" tree
  case fields of
    [comma, parameterTree] -> do
      expectLiteral "," comma
      grammarV1ReferenceTermParamCore parameterTree
    _ -> failTermParams "term_params suffix is not a two-item sequence"

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failTermParams
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failTermParams ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failTermParams (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failTermParams (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTermParamsError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failTermParams
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failTermParams ("expected literal " <> expected)

mapCommonError
  :: Either GrammarV1ReferenceDeclarationCommonError a
  -> Either GrammarV1ReferenceTermParamsError a
mapCommonError result = case result of
  Left errorValue -> failTermParams
    ("declaration-common correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

mapTypeError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceTermParamsError a
mapTypeError result = case result of
  Left errorValue -> failTermParams
    ("type correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

failTermParams
  :: Text
  -> Either GrammarV1ReferenceTermParamsError a
failTermParams = Left . GrammarV1ReferenceTermParamsError
