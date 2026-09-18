{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.InterruptiblePingSource
  ( GrammarV1CheckedInterruptiblePingSource (..)
  , GrammarV1InterruptiblePingSourceError (..)
  , grammarV1CheckedInterruptiblePingSource
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  , grammarV1CheckedExpressionReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1BranchValue (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1Pattern (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type (..)
  , grammarV1QualifiedNameParts
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1CheckedInterruptiblePingSource =
  GrammarV1CheckedInterruptiblePingSource
    { interruptiblePingEndpointParameter :: GrammarV1ResolvedBinder
    , interruptiblePingCancellationParameter :: GrammarV1ResolvedBinder
    }
  deriving (Eq, Show)

data GrammarV1InterruptiblePingSourceError
  = GrammarV1InterruptiblePingParameterShape
  | GrammarV1InterruptiblePingCancellationTypeMismatch
  | GrammarV1InterruptiblePingBodyShape Text
  | GrammarV1InterruptiblePingReferenceMismatch Text
  deriving (Eq, Show)

-- | Check the exact source control boundary used by INT-009 Stage 5:
--
-- @
-- component CancelOnSignal(endpoint : Client[PingLoop], cancelled : Bool) {
--   if cancelled {
--     let done = select Done on endpoint;
--     close done;
--   };
-- }
-- @
--
-- The cancellation condition and selected endpoint resolve to the exact component
-- parameters; the Done/close sequence is explicit source syntax rather than a
-- host-side terminal shortcut.
grammarV1CheckedInterruptiblePingSource
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1InterruptiblePingSourceError
        GrammarV1CheckedInterruptiblePingSource)
grammarV1CheckedInterruptiblePingSource declarationKey component = do
  (maybeParameters, scope) <- either (const Nothing) Just
    (grammarV1ComponentParameterScope declarationKey component)
  pure $ do
    (endpoint, cancelled) <- case maybeParameters of
      Just [endpointParameter, cancellationParameter]
        | grammarV1ResolvedBinderDisplayName endpointParameter == "endpoint"
        , grammarV1ResolvedBinderDisplayName cancellationParameter == "cancelled" ->
            Right (endpointParameter, cancellationParameter)
      _ -> Left GrammarV1InterruptiblePingParameterShape

    case grammarV1ComponentTermParams component of
      Just [_endpointSource, Located _ cancellationSource]
        | locatedValue (grammarV1TermParamType cancellationSource)
            == GrammarV1BoolType -> Right ()
        | otherwise -> Left GrammarV1InterruptiblePingCancellationTypeMismatch
      _ -> Left GrammarV1InterruptiblePingParameterShape

    bodyExpression <- case locatedValue (grammarV1ComponentBody component) of
      GrammarV1Block
        [Located _ (GrammarV1ExpressionStatement expression)] -> Right expression
      _ -> bodyShape "expected one if expression"

    case locatedValue bodyExpression of
      GrammarV1IfExpression condition Nothing thenBlock Nothing -> do
        refs <- checkedReferences scope condition
        requireExactReferences "cancellation condition" [cancelled] refs
        requireSimpleName "cancellation condition syntax" "cancelled" condition
        checkDoneBlock scope endpoint thenBlock
      _ -> bodyShape "expected if cancelled { select Done; close }"

    Right GrammarV1CheckedInterruptiblePingSource
      { interruptiblePingEndpointParameter = endpoint
      , interruptiblePingCancellationParameter = cancelled
      }

checkDoneBlock
  :: GrammarV1LexicalScope
  -> GrammarV1ResolvedBinder
  -> Located GrammarV1Block
  -> Either GrammarV1InterruptiblePingSourceError ()
checkDoneBlock scope endpoint (Located _ (GrammarV1Block statements)) =
  case statements of
    [ Located _ (GrammarV1LetStatement donePattern selectSource)
      , Located _ (GrammarV1ExpressionStatement closeSource)
      ] -> do
        case locatedValue donePattern of
          GrammarV1IdentifierPattern name
            | locatedValue name == "done" -> Right ()
          _ -> bodyShape "Done selection must bind the successor as done"
        case locatedValue selectSource of
          GrammarV1SelectExpression branch selectedEndpoint Nothing
            | branchName branch == "Done" -> do
                refs <- checkedReferences scope selectedEndpoint
                requireExactReferences "Done endpoint" [endpoint] refs
                requireSimpleName "Done endpoint syntax" "endpoint" selectedEndpoint
            | otherwise -> bodyShape "cancellation branch must select Done"
          _ -> bodyShape "expected select Done on endpoint"
        case locatedValue closeSource of
          GrammarV1CloseExpression closedEndpoint ->
            requireSimpleName "close successor syntax" "done" closedEndpoint
          _ -> bodyShape "expected close done"
    _ -> bodyShape "expected let done = select Done; close done"

checkedReferences
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either
      GrammarV1InterruptiblePingSourceError
      [GrammarV1CheckedLexicalReference]
checkedReferences scope expression =
  case grammarV1CheckedExpressionReferences Set.empty scope expression of
    Just (Right refs) -> Right refs
    _ -> Left (GrammarV1InterruptiblePingReferenceMismatch "lexical reference")

requireExactReferences
  :: Text
  -> [GrammarV1ResolvedBinder]
  -> [GrammarV1CheckedLexicalReference]
  -> Either GrammarV1InterruptiblePingSourceError ()
requireExactReferences role expected actual
  | map grammarV1ResolvedBinderKey expected
      == map
        (grammarV1ResolvedBinderKey . grammarV1CheckedLexicalReferenceBinder)
        actual = Right ()
  | otherwise = Left (GrammarV1InterruptiblePingReferenceMismatch role)

requireSimpleName
  :: Text
  -> Text
  -> Located GrammarV1Expression
  -> Either GrammarV1InterruptiblePingSourceError ()
requireSimpleName role expected (Located _ expression) =
  case expression of
    GrammarV1NameExpression reference []
      | referenceName reference == [expected] -> Right ()
    GrammarV1ParenthesizedExpression inner ->
      requireSimpleName role expected inner
    _ -> bodyShape ("unexpected local syntax for " <> role)

branchName :: Located GrammarV1BranchValue -> Text
branchName (Located _ branch) =
  case grammarV1QualifiedNameParts
      (locatedValue (grammarV1BranchValueName branch)) of
    [name] -> name
    _ -> ""

referenceName :: GrammarV1StaticReference -> [Text]
referenceName = grammarV1QualifiedNameParts . grammarV1StaticReferenceName

bodyShape :: Text -> Either GrammarV1InterruptiblePingSourceError a
bodyShape = Left . GrammarV1InterruptiblePingBodyShape
