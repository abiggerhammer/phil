{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ComponentReceiveClose
  ( GrammarV1CheckedComponentReceiveClose (..)
  , GrammarV1ComponentReceiveCloseError (..)
  , grammarV1CheckedComponentReceiveClose
  ) where

import Data.Text (Text)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1Pattern (..)
  , GrammarV1Statement (..)
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.PatternBinderScope
  ( grammarV1BindPattern
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact source-semantic carrier for the bounded server-side Ping body:
--
--     let (done, received) = receive U8 on endpoint;
--     close done;
--
-- The first tuple binder is the successor endpoint returned by receive; the
-- second is the received value. All identities are declaration-rooted semantic
-- binders rather than source spellings.
data GrammarV1CheckedComponentReceiveClose = GrammarV1CheckedComponentReceiveClose
  { checkedComponentReceiveEndpoint :: GrammarV1ResolvedBinder
  , checkedComponentReceiveSuccessor :: GrammarV1ResolvedBinder
  , checkedComponentReceivePayload :: GrammarV1ResolvedBinder
  , checkedComponentReceiveWrittenType :: GrammarV1Type
  }
  deriving (Eq, Show)

data GrammarV1ComponentReceiveCloseError
  = GrammarV1ComponentReceiveCloseBinderError GrammarV1BinderScopeError
  | GrammarV1ComponentReceiveCloseOperandNotLocal Text
  | GrammarV1ComponentReceiveCloseEndpointNotParameter GrammarV1ResolvedBinder
  | GrammarV1ComponentReceiveClosePatternShape
  | GrammarV1ComponentReceiveCloseCloseMismatch
      GrammarV1ResolvedBinder
      GrammarV1ResolvedBinder
  deriving (Eq, Show)

-- | Check only the two-statement tuple-receive/close body used by the internal
-- Phase 1 Ping witness. Once the structural shape matches, lexical failures are
-- semantic errors rather than a reason to fall out of competence.
grammarV1CheckedComponentReceiveClose
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1ComponentReceiveCloseError
        GrammarV1CheckedComponentReceiveClose)
grammarV1CheckedComponentReceiveClose declarationKey component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement receivePattern receiveSource)
      , Located _ (GrammarV1ExpressionStatement closeSource)
      ] ->
        case (locatedValue receiveSource, locatedValue closeSource) of
          (GrammarV1ReceiveExpression writtenType endpointSource,
            GrammarV1CloseExpression closeEndpointSource) ->
              Just $ do
                (maybeParameters, parameterScope) <- mapLeft
                  GrammarV1ComponentReceiveCloseBinderError
                  (grammarV1ComponentParameterScope declarationKey component)
                let parameters = maybe [] id maybeParameters
                endpoint <- requireLocal "receive endpoint" parameterScope endpointSource
                requireEndpointParameter parameters endpoint
                (successorBinder, payloadBinder, afterReceive) <-
                  bindReceivePattern receivePattern parameterScope
                closeEndpoint <- requireLocal
                  "close endpoint"
                  afterReceive
                  closeEndpointSource
                let closeBinder = grammarV1CheckedLocalValueBinder closeEndpoint
                if grammarV1ResolvedBinderKey closeBinder
                    == grammarV1ResolvedBinderKey successorBinder
                  then Right GrammarV1CheckedComponentReceiveClose
                    { checkedComponentReceiveEndpoint =
                        grammarV1CheckedLocalValueBinder endpoint
                    , checkedComponentReceiveSuccessor = successorBinder
                    , checkedComponentReceivePayload = payloadBinder
                    , checkedComponentReceiveWrittenType = locatedValue writtenType
                    }
                  else Left
                    (GrammarV1ComponentReceiveCloseCloseMismatch
                      successorBinder closeBinder)
          _ -> Nothing
    _ -> Nothing
  where
    requireLocal
      :: Text
      -> GrammarV1LexicalScope
      -> Located GrammarV1Expression
      -> Either
          GrammarV1ComponentReceiveCloseError
          GrammarV1CheckedLocalValueOccurrence
    requireLocal role scope source =
      maybe
        (Left (GrammarV1ComponentReceiveCloseOperandNotLocal role))
        Right
        (grammarV1CheckedLocalValueOccurrenceInScope scope source)

    requireEndpointParameter
      :: [GrammarV1ResolvedBinder]
      -> GrammarV1CheckedLocalValueOccurrence
      -> Either GrammarV1ComponentReceiveCloseError ()
    requireEndpointParameter parameters occurrence =
      let binder = grammarV1CheckedLocalValueBinder occurrence
          sameParameter candidate =
            grammarV1ResolvedBinderKey candidate == grammarV1ResolvedBinderKey binder
      in if grammarV1ResolvedBinderKind binder == GrammarV1ComponentParameterBinder
          && any sameParameter parameters
        then Right ()
        else Left (GrammarV1ComponentReceiveCloseEndpointNotParameter binder)

    bindReceivePattern
      :: Located GrammarV1Pattern
      -> GrammarV1LexicalScope
      -> Either
          GrammarV1ComponentReceiveCloseError
          (GrammarV1ResolvedBinder, GrammarV1ResolvedBinder, GrammarV1LexicalScope)
    bindReceivePattern patternSource scope =
      case locatedValue patternSource of
        GrammarV1TuplePattern
          [ Located _ (GrammarV1IdentifierPattern _)
          , Located _ (GrammarV1IdentifierPattern _)
          ] -> do
            (binders, nextScope) <- mapLeft
              GrammarV1ComponentReceiveCloseBinderError
              (grammarV1BindPattern GrammarV1LetPatternBinder patternSource scope)
            case binders of
              [successorBinder, payloadBinder] ->
                Right (successorBinder, payloadBinder, nextScope)
              _ -> Left GrammarV1ComponentReceiveClosePatternShape
        _ -> Left GrammarV1ComponentReceiveClosePatternShape

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
