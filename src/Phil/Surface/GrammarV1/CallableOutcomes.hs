module Phil.Surface.GrammarV1.CallableOutcomes
  ( grammarV1OutcomeIdentity
  , grammarV1CallableFailure
  , grammarV1CallableFailures
  ) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Syntax (Outcome (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1OutcomeKind (..)
  , GrammarV1OutcomeSpec (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Project the bounded source form whose exact static type spelling can serve
-- as the opaque Core outcome/failure identity without erasing type structure.
-- Bare or qualified unspecialized named types preserve their dotted spelling;
-- specialization and every structured type remain outside this bridge.
grammarV1OutcomeIdentity :: GrammarV1Type -> Maybe Text.Text
grammarV1OutcomeIdentity source = case source of
  GrammarV1NamedType reference
    | null (grammarV1StaticReferenceArguments reference) ->
        case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [] -> Nothing
          parts -> Just (Text.intercalate (Text.singleton '.') parts)
  _ -> Nothing

-- | Project one public outcome specification into Core's non-success failure
-- carrier. Success is deliberately represented by Just Nothing because success
-- is not a CallableFailure. Unsupported non-success identity is structural
-- non-competence (Nothing), not a fabricated failure name.
grammarV1CallableFailure
  :: GrammarV1OutcomeSpec
  -> Maybe (Maybe CallableFailure)
grammarV1CallableFailure source =
  case locatedValue (grammarV1OutcomeSpecKind source) of
    GrammarV1SuccessOutcome -> Just Nothing
    GrammarV1NegativeOutcome -> do
      identity <- grammarV1OutcomeIdentity outcomeType
      pure (Just (CallableTypedNegative (Outcome identity)))
    GrammarV1TerminalOutcome -> do
      identity <- grammarV1OutcomeIdentity outcomeType
      pure (Just (CallableDeclaredTerminal (Outcome identity)))
    GrammarV1FatalOutcome -> do
      identity <- grammarV1OutcomeIdentity outcomeType
      pure (Just (CallableFatal identity))
  where
    outcomeType = locatedValue (grammarV1OutcomeSpecType source)

-- | Collect the exact Core failure surface from all declared public outcome
-- clauses. Source success cases contribute no failure. Set normalization is the
-- established Core callable-refinement carrier semantics; duplicate/outcome
-- domain consistency remains owned separately by CALL-018 rather than being
-- invented here. If any non-success case cannot preserve exact identity, the
-- whole projection fails closed.
grammarV1CallableFailures
  :: GrammarV1CallableContractDecl
  -> Maybe (Set.Set CallableFailure)
grammarV1CallableFailures source = do
  projected <- mapM
    (grammarV1CallableFailure . locatedValue)
    [ spec
    | Located _ (GrammarV1CallableOutcomes specs) <- grammarV1CallableClauses source
    , spec <- specs
    ]
  pure (Set.fromList [failure | Just failure <- projected])
