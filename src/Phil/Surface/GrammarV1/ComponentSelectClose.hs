{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: bounded source-selected branch, with binder identity retained.
-- This is an opt-in production source adapter, not a general offer elaborator.
module Phil.Surface.GrammarV1.ComponentSelectClose
  ( GrammarV1CheckedComponentSelectClose (..)
  , GrammarV1ComponentSelectCloseError (..)
  , grammarV1CheckedComponentSelectClose
  ) where

import Data.Text (Text)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1BranchValue (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1Pattern (..)
  , GrammarV1Statement (..)
  , grammarV1QualifiedNameParts
  )
import Phil.Surface.GrammarV1.PatternBinderScope (grammarV1BindPattern)
import Phil.Surface.Syntax (Located (..))

-- | One source-checked, payload-free "let successor = select Label on endpoint;
-- close successor;" local path. The label remains a choice INPUT, checked
-- against the caller-supplied protocol projection by Core.Protocol.
data GrammarV1CheckedComponentSelectClose = GrammarV1CheckedComponentSelectClose
  { checkedComponentSelectEndpoint :: GrammarV1ResolvedBinder
  , checkedComponentSelectSuccessor :: GrammarV1ResolvedBinder
  , checkedComponentSelectLabel :: Text
  }
  deriving (Eq, Show)

data GrammarV1ComponentSelectCloseError
  = GrammarV1ComponentSelectCloseBinderError GrammarV1BinderScopeError
  | GrammarV1ComponentSelectCloseOperandNotLocal Text
  | GrammarV1ComponentSelectCloseEndpointNotParameter GrammarV1ResolvedBinder
  | GrammarV1ComponentSelectCloseNonSimpleLabel
  | GrammarV1ComponentSelectClosePayloadUnsupported
  | GrammarV1ComponentSelectCloseSuccessorNotIdentifier
  | GrammarV1ComponentSelectCloseSuccessorArity Int
  | GrammarV1ComponentSelectCloseCloseMismatch
      GrammarV1ResolvedBinder GrammarV1ResolvedBinder
  deriving (Eq, Show)

-- | Outside the exact two-statement source shape, return Nothing (not an
-- admission). Inside it, lexical/payload/close mismatches are explicit Left.
-- Protocol label validity, role, instance and session-head are NEVER guessed:
-- the caller must pass the checked role projection to Core.Protocol.
grammarV1CheckedComponentSelectClose
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe (Either GrammarV1ComponentSelectCloseError GrammarV1CheckedComponentSelectClose)
grammarV1CheckedComponentSelectClose declarationKey component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [Located _ (GrammarV1LetStatement patternSource selectSource),
       Located _ (GrammarV1ExpressionStatement closeSource)] ->
        case (locatedValue selectSource, locatedValue closeSource) of
          (GrammarV1SelectExpression branch endpointSource Nothing,
           GrammarV1CloseExpression closeSourceEndpoint) ->
            Just $ do
              (maybeParameters, parameterScope) <- mapLeft
                GrammarV1ComponentSelectCloseBinderError
                (grammarV1ComponentParameterScope declarationKey component)
              let parameters = maybe [] id maybeParameters
              endpointOccurrence <- maybe
                (Left (GrammarV1ComponentSelectCloseOperandNotLocal "select endpoint"))
                Right (grammarV1CheckedLocalValueOccurrenceInScope parameterScope endpointSource)
              let endpoint = grammarV1CheckedLocalValueBinder endpointOccurrence
                  parameterMatches candidate =
                    grammarV1ResolvedBinderKey candidate == grammarV1ResolvedBinderKey endpoint
              if grammarV1ResolvedBinderKind endpoint /= GrammarV1ComponentParameterBinder
                  || not (any parameterMatches parameters)
                then Left (GrammarV1ComponentSelectCloseEndpointNotParameter endpoint)
                else Right ()
              label <- case grammarV1QualifiedNameParts
                  (locatedValue (grammarV1BranchValueName (locatedValue branch))) of
                [simple] -> Right simple
                _ -> Left GrammarV1ComponentSelectCloseNonSimpleLabel
              if null (grammarV1BranchValueArguments (locatedValue branch))
                then Right ()
                else Left GrammarV1ComponentSelectClosePayloadUnsupported
              (binders, afterSelect) <- case locatedValue patternSource of
                GrammarV1IdentifierPattern _ -> mapLeft
                  GrammarV1ComponentSelectCloseBinderError
                  (grammarV1BindPattern GrammarV1LetPatternBinder patternSource parameterScope)
                _ -> Left GrammarV1ComponentSelectCloseSuccessorNotIdentifier
              successor <- case binders of
                [binder] -> Right binder
                other -> Left (GrammarV1ComponentSelectCloseSuccessorArity (length other))
              closedOccurrence <- maybe
                (Left (GrammarV1ComponentSelectCloseOperandNotLocal "close successor"))
                Right
                (grammarV1CheckedLocalValueOccurrenceInScope afterSelect closeSourceEndpoint)
              let closed = grammarV1CheckedLocalValueBinder closedOccurrence
              if grammarV1ResolvedBinderKey successor /= grammarV1ResolvedBinderKey closed
                then Left (GrammarV1ComponentSelectCloseCloseMismatch successor closed)
                else Right GrammarV1CheckedComponentSelectClose
                  { checkedComponentSelectEndpoint = endpoint
                  , checkedComponentSelectSuccessor = successor
                  , checkedComponentSelectLabel = label
                  }
          _ -> Nothing
    _ -> Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
