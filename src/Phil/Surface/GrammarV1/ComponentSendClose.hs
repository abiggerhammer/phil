{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ComponentSendClose
  ( GrammarV1CheckedComponentSendClose (..)
  , GrammarV1ComponentSendCloseError (..)
  , grammarV1CheckedComponentSendClose
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
  )
import Phil.Surface.GrammarV1.PatternBinderScope
  ( grammarV1BindPattern
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact source-semantic carrier for the first executable INT-008 component
-- body shape:
--
--     let done = send payload on endpoint;
--     close done;
--
-- Every name in the carrier is an already-resolved semantic binder. Display
-- spelling is diagnostic only; later runtime composition can therefore connect
-- the exact provisioned component parameters and exact successor occurrence
-- without reconstructing identity from source text.
data GrammarV1CheckedComponentSendClose = GrammarV1CheckedComponentSendClose
  { checkedComponentSendPayload :: GrammarV1ResolvedBinder
  , checkedComponentSendEndpoint :: GrammarV1ResolvedBinder
  , checkedComponentSendSuccessor :: GrammarV1ResolvedBinder
  }
  deriving (Eq, Show)

data GrammarV1ComponentSendCloseError
  = GrammarV1ComponentSendCloseBinderError GrammarV1BinderScopeError
  | GrammarV1ComponentSendCloseOperandNotLocal Text
  | GrammarV1ComponentSendCloseOperandNotParameter
      Text
      GrammarV1ResolvedBinder
  | GrammarV1ComponentSendCloseSuccessorNotIdentifier
  | GrammarV1ComponentSendCloseSuccessorArity Int
  | GrammarV1ComponentSendCloseCloseMismatch
      GrammarV1ResolvedBinder
      GrammarV1ResolvedBinder
  deriving (Eq, Show)

-- | Check only the bounded two-statement send-then-close component body used by
-- the Phase 1 Ping witness. Other valid component bodies remain outside this
-- relation's competence. Once the source has this exact structural shape,
-- lexical/binder errors fail closed instead of silently falling back.
grammarV1CheckedComponentSendClose
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1ComponentSendCloseError
        GrammarV1CheckedComponentSendClose)
grammarV1CheckedComponentSendClose declarationKey component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement successorPattern sendSource)
      , Located _ (GrammarV1ExpressionStatement closeSource)
      ] ->
        case (locatedValue sendSource, locatedValue closeSource) of
          (GrammarV1SendExpression payloadSource endpointSource,
            GrammarV1CloseExpression closeEndpointSource) ->
              Just $ do
                (maybeParameters, parameterScope) <- mapLeft
                  GrammarV1ComponentSendCloseBinderError
                  (grammarV1ComponentParameterScope declarationKey component)
                let parameters = maybe [] id maybeParameters
                payload <- requireLocal "send payload" parameterScope payloadSource
                endpoint <- requireLocal "send endpoint" parameterScope endpointSource
                requireParameter "send payload" parameters payload
                requireParameter "send endpoint" parameters endpoint
                successor <- bindSuccessor successorPattern parameterScope
                closeEndpoint <- requireLocal
                  "close endpoint"
                  (snd successor)
                  closeEndpointSource
                let successorBinder = fst successor
                    closeBinder = grammarV1CheckedLocalValueBinder closeEndpoint
                if grammarV1ResolvedBinderKey closeBinder
                    == grammarV1ResolvedBinderKey successorBinder
                  then Right GrammarV1CheckedComponentSendClose
                    { checkedComponentSendPayload =
                        grammarV1CheckedLocalValueBinder payload
                    , checkedComponentSendEndpoint =
                        grammarV1CheckedLocalValueBinder endpoint
                    , checkedComponentSendSuccessor = successorBinder
                    }
                  else Left
                    (GrammarV1ComponentSendCloseCloseMismatch
                      successorBinder closeBinder)
          _ -> Nothing
    _ -> Nothing
  where
    requireLocal
      :: Text
      -> GrammarV1LexicalScope
      -> Located GrammarV1Expression
      -> Either
          GrammarV1ComponentSendCloseError
          GrammarV1CheckedLocalValueOccurrence
    requireLocal role scope source =
      maybe
        (Left (GrammarV1ComponentSendCloseOperandNotLocal role))
        Right
        (grammarV1CheckedLocalValueOccurrenceInScope scope source)

    requireParameter
      :: Text
      -> [GrammarV1ResolvedBinder]
      -> GrammarV1CheckedLocalValueOccurrence
      -> Either GrammarV1ComponentSendCloseError ()
    requireParameter role parameters occurrence =
      let binder = grammarV1CheckedLocalValueBinder occurrence
          sameParameter candidate =
            grammarV1ResolvedBinderKey candidate == grammarV1ResolvedBinderKey binder
      in if grammarV1ResolvedBinderKind binder == GrammarV1ComponentParameterBinder
          && any sameParameter parameters
        then Right ()
        else Left (GrammarV1ComponentSendCloseOperandNotParameter role binder)

    bindSuccessor
      :: Located GrammarV1Pattern
      -> GrammarV1LexicalScope
      -> Either
          GrammarV1ComponentSendCloseError
          (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
    bindSuccessor patternSource scope =
      case locatedValue patternSource of
        GrammarV1IdentifierPattern _ -> do
          (binders, nextScope) <- mapLeft
            GrammarV1ComponentSendCloseBinderError
            (grammarV1BindPattern
              GrammarV1LetPatternBinder
              patternSource
              scope)
          case binders of
            [binder] -> Right (binder, nextScope)
            other -> Left (GrammarV1ComponentSendCloseSuccessorArity (length other))
        _ -> Left GrammarV1ComponentSendCloseSuccessorNotIdentifier

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
