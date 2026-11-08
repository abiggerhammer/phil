{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: bounded source offer-arm coverage, not offer execution.
-- Local session is an explicit input from caller's separately checked projection.
module Phil.Surface.GrammarV1.ComponentOfferCoverage
  ( GrammarV1CheckedComponentOfferCoverage (..)
  , GrammarV1ComponentOfferCoverageError (..)
  , grammarV1CheckedComponentOfferCoverage
  ) where

import Data.Text (Text)
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Branch (..), Session (..))
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
  , GrammarV1CasePattern (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1MatchArm (..)
  , GrammarV1MatchArmBody (..)
  , GrammarV1Statement (..)
  , grammarV1QualifiedNameParts
  )
import Phil.Surface.Syntax (Located (..))

-- | The admitted fragment only verifies the labels of a payload-free offer
-- whose arms return unit. It does not execute those arms, manufacture session
-- continuation names, or assert that returning unit closes an endpoint.
data GrammarV1CheckedComponentOfferCoverage = GrammarV1CheckedComponentOfferCoverage
  { checkedComponentOfferEndpoint :: GrammarV1ResolvedBinder
  , checkedComponentOfferLabels :: [Text]
  }
  deriving (Eq, Show)

data GrammarV1ComponentOfferCoverageError
  = GrammarV1ComponentOfferBinderError GrammarV1BinderScopeError
  | GrammarV1ComponentOfferOperandNotLocal
  | GrammarV1ComponentOfferEndpointNotParameter GrammarV1ResolvedBinder
  | GrammarV1ComponentOfferWrongSessionHead Session
  | GrammarV1ComponentOfferNonSimpleLabel
  | GrammarV1ComponentOfferArmBindersUnsupported
  | GrammarV1ComponentOfferArmBodyUnsupported
  | GrammarV1ComponentOfferDuplicateArm Text
  | GrammarV1ComponentOfferMissingArm Text
  | GrammarV1ComponentOfferUnexpectedArm Text
  deriving (Eq, Show)

-- | None means the exact expression-statement fragment was not recognized,
-- NEVER that an arbitrary offer was checked. Within this fragment, failures
-- are explicit. Protocol authority comes ONLY from the caller's checked
-- projection; this function cannot attest the provenance of its Session input.
grammarV1CheckedComponentOfferCoverage
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Session
  -> Maybe (Either GrammarV1ComponentOfferCoverageError
                   GrammarV1CheckedComponentOfferCoverage)
grammarV1CheckedComponentOfferCoverage root component checkedLocalSession =
  case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
    [Located _ (GrammarV1ExpressionStatement source)] ->
      case locatedValue source of
        GrammarV1OfferExpression endpointSource arms -> Just $ do
          (maybeParameters, scope) <- mapLeft
            GrammarV1ComponentOfferBinderError
            (grammarV1ComponentParameterScope root component)
          endpointOccurrence <- maybe
            (Left GrammarV1ComponentOfferOperandNotLocal)
            Right
            (grammarV1CheckedLocalValueOccurrenceInScope scope endpointSource)
          let endpoint = grammarV1CheckedLocalValueBinder endpointOccurrence
              parameters = maybe [] id maybeParameters
              isParameter candidate =
                grammarV1ResolvedBinderKey candidate == grammarV1ResolvedBinderKey endpoint
          if grammarV1ResolvedBinderKind endpoint == GrammarV1ComponentParameterBinder
              && any isParameter parameters
            then Right ()
            else Left (GrammarV1ComponentOfferEndpointNotParameter endpoint)
          expected <- case checkedLocalSession of
            Offer branches -> Right (map branchLabel branches)
            other -> Left (GrammarV1ComponentOfferWrongSessionHead other)
          actual <- traverse sourceArmLabel arms
          case firstDuplicate actual of
            Just repeated -> Left (GrammarV1ComponentOfferDuplicateArm repeated)
            Nothing -> Right ()
          case firstMissing expected actual of
            Just missing -> Left (GrammarV1ComponentOfferMissingArm missing)
            Nothing -> Right ()
          case firstMissing actual expected of
            Just extra -> Left (GrammarV1ComponentOfferUnexpectedArm extra)
            Nothing -> Right ()
          Right GrammarV1CheckedComponentOfferCoverage
            { checkedComponentOfferEndpoint = endpoint
            , checkedComponentOfferLabels = actual
            }
        _ -> Nothing
    _ -> Nothing

sourceArmLabel
  :: Located GrammarV1MatchArm
  -> Either GrammarV1ComponentOfferCoverageError Text
sourceArmLabel (Located _ arm) = do
  let patternValue = locatedValue (grammarV1MatchArmPattern arm)
  label <- case grammarV1QualifiedNameParts
      (locatedValue (grammarV1CasePatternName patternValue)) of
    [simple] -> Right simple
    _ -> Left GrammarV1ComponentOfferNonSimpleLabel
  case grammarV1CasePatternBinders patternValue of
    Nothing -> Right ()
    Just _ -> Left GrammarV1ComponentOfferArmBindersUnsupported
  case grammarV1MatchArmBody arm of
    GrammarV1MatchArmBlock block ->
      case grammarV1BlockStatements (locatedValue block) of
        [Located _ (GrammarV1ReturnStatement expression)]
          | locatedValue expression == GrammarV1UnitExpression -> Right label
        _ -> Left GrammarV1ComponentOfferArmBodyUnsupported
    _ -> Left GrammarV1ComponentOfferArmBodyUnsupported

firstDuplicate :: Eq a => [a] -> Maybe a
firstDuplicate [] = Nothing
firstDuplicate (item : rest)
  | item `elem` rest = Just item
  | otherwise = firstDuplicate rest

firstMissing :: Eq a => [a] -> [a] -> Maybe a
firstMissing [] _ = Nothing
firstMissing (item : rest) available
  | item `elem` available = firstMissing rest available
  | otherwise = Just item

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
