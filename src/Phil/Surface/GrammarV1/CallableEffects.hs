module Phil.Surface.GrammarV1.CallableEffects
  ( GrammarV1CallableEffectBoundTemplate (..)
  , GrammarV1ResolvedCallableEffectsParameter (..)
  , GrammarV1ResolvedCallableEffectUse (..)
  , GrammarV1CallableEffectReferenceError (..)
  , GrammarV1CheckedSubjectIndexedEffect (..)
  , GrammarV1SubjectIndexedEffectError (..)
  , grammarV1SemanticEffect
  , grammarV1EffectSet
  , grammarV1CallableEffectBounds
  , grammarV1ResolvedCallableEffectBounds
  , grammarV1CheckedSubjectIndexedSemanticEffect
  , grammarV1CheckedSubjectIndexedEffectSet
  , grammarV1CheckedSubjectIndexedCallableEffectBounds
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.Generic (GenericStaticParameterKey)
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Core.Syntax (Name (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedExpressionReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1EffectExpression (..)
  , GrammarV1EffectSetExpression (..)
  , GrammarV1Expression (..)
  , GrammarV1GenericKind (..)
  , GrammarV1GenericParam (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | A callable effect bound after SURF-008 has preserved whether the source
-- selected a concrete finite effect set or an abstract static Effects parameter.
-- Parameter identity is supplied by the competent generic binder resolver; the
-- display spelling of the source parameter is never itself semantic identity.
data GrammarV1CallableEffectBoundTemplate
  = GrammarV1ConcreteCallableEffectBound (Set.Set SemanticEffect)
  | GrammarV1CallableEffectsParameterBound GenericStaticParameterKey
  deriving (Eq, Ord, Show)

-- | Exact generic-binder evidence for one source parameter of kind Effects.
data GrammarV1ResolvedCallableEffectsParameter =
  GrammarV1ResolvedCallableEffectsParameter
    { resolvedCallableEffectsSourceParameter :: Located GrammarV1GenericParam
    , resolvedCallableEffectsParameter :: GenericStaticParameter
    }
  deriving (Eq, Show)

-- | Exact use-site evidence for one source `effects E` occurrence. Matching is
-- by the complete Located effect-set occurrence rather than textual spelling.
data GrammarV1ResolvedCallableEffectUse = GrammarV1ResolvedCallableEffectUse
  { resolvedCallableEffectSourceUse :: Located GrammarV1EffectSetExpression
  , resolvedCallableEffectUseParameterKey :: GenericStaticParameterKey
  }
  deriving (Eq, Show)

data GrammarV1CallableEffectReferenceError
  = GrammarV1CallableEffectsParameterEvidenceCountMismatch Int Int
  | GrammarV1CallableEffectsParameterSourceMismatch
      Int
      (Located GrammarV1GenericParam)
      (Located GrammarV1GenericParam)
  | GrammarV1CallableEffectsParameterKindMismatch
      GenericStaticParameterKey
      GenericStaticKind
  | GrammarV1DuplicateCallableEffectsParameterKey GenericStaticParameterKey
  | GrammarV1MissingCallableEffectUseEvidence
      (Located GrammarV1EffectSetExpression)
  | GrammarV1DuplicateCallableEffectUseEvidence
      (Located GrammarV1EffectSetExpression)
  | GrammarV1CallableEffectUseUndeclaredParameter GenericStaticParameterKey
  | GrammarV1UnexpectedCallableEffectUseEvidence
      (Located GrammarV1EffectSetExpression)
  deriving (Eq, Show)

-- | One effect whose argument-bearing source form has been resolved through the
-- exact SURF-009 lexical authority. The Core carrier remains the established
-- Text-backed SemanticEffect used by the certified callable-effect checker;
-- subject identity is supplied by resolver-issued Core Names, never source text.
data GrammarV1CheckedSubjectIndexedEffect = GrammarV1CheckedSubjectIndexedEffect
  { checkedSubjectIndexedEffectCore :: SemanticEffect
  , checkedSubjectIndexedEffectReferences :: [GrammarV1CheckedLexicalReference]
  }
  deriving (Eq, Show)

data GrammarV1SubjectIndexedEffectError
  = GrammarV1EffectSubjectReferenceError GrammarV1LexicalReferenceError
  | GrammarV1EffectSubjectNotLocal (Located GrammarV1Expression)
  deriving (Eq, Show)

-- | Preserve the first exact Grammar-v1 effect identity fragment as Core's
-- Text-backed SemanticEffect. Only argument-free, unspecialized static
-- references are competent here; term arguments and static specialization carry
-- additional semantics and therefore remain unresolved rather than being
-- flattened into a string.
grammarV1SemanticEffect
  :: GrammarV1EffectExpression
  -> Maybe SemanticEffect
grammarV1SemanticEffect effect
  | not (null (grammarV1EffectArguments effect)) = Nothing
  | not (null (grammarV1StaticReferenceArguments reference)) = Nothing
  | otherwise = case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
      [] -> Nothing
      parts -> Just (SemanticEffect (Text.intercalate (Text.singleton '.') parts))
  where
    reference = locatedValue (grammarV1EffectReference effect)

-- | Route a literal Grammar-v1 effect set into Core's finite SemanticEffect set.
-- Literal ordering and duplicate spelling are intentionally normalized by the
-- semantic Set carrier. Effect-set references remain unresolved until the
-- expected static Effects parameter is competently resolved.
grammarV1EffectSet
  :: GrammarV1EffectSetExpression
  -> Maybe (Set.Set SemanticEffect)
grammarV1EffectSet source = case source of
  GrammarV1EffectSetLiteral effects ->
    Set.fromList <$> mapM
      (grammarV1SemanticEffect . locatedValue)
      effects
  GrammarV1EffectSetReference _ -> Nothing

-- | Preserve each callable effects clause as a separate Core effect bound in
-- source order. This projection does not invent a declaration-level cardinality
-- rule or silently union multiple clauses; callers retain that distinction.
-- Exact absence is Just []. One unresolved effect set rejects the projection in
-- full rather than dropping or partially accepting it.
grammarV1CallableEffectBounds
  :: GrammarV1CallableContractDecl
  -> Maybe [Set.Set SemanticEffect]
grammarV1CallableEffectBounds source =
  mapM elaborate
    [ effectSet
    | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses source
    ]
  where
    elaborate (Located _ effectSet) = grammarV1EffectSet effectSet

-- | Preserve both literal callable effect bounds and bare references to declared
-- Effects parameters. The caller supplies exact binder evidence for every source
-- Effects parameter and exact use evidence for every `effects E` occurrence.
-- SURF-008 consumes those stable keys but does not derive them from source names.
-- Specialized effect-set references and argument-bearing literal effects remain
-- outside this bounded route.
grammarV1ResolvedCallableEffectBounds
  :: [GrammarV1ResolvedCallableEffectsParameter]
  -> [GrammarV1ResolvedCallableEffectUse]
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1CallableEffectReferenceError
        [GrammarV1CallableEffectBoundTemplate])
grammarV1ResolvedCallableEffectBounds parameterEvidence useEvidence source =
  case validateEffectsParameterEvidence sourceParameters parameterEvidence of
    Left err -> Just (Left err)
    Right parameterKeys -> do
      projected <- projectEffectClauses parameterKeys useEvidence effectClauses
      pure $ case projected of
        Left err -> Left err
        Right (bounds, used) ->
          case firstUnexpectedEffectUseEvidence used useEvidence of
            Just extra -> Left
              (GrammarV1UnexpectedCallableEffectUseEvidence
                (resolvedCallableEffectSourceUse extra))
            Nothing -> Right bounds
  where
    sourceParameters =
      [ parameter
      | parameter@(Located _ genericParameter) <- grammarV1CallableGenericParams source
      , locatedValue (grammarV1GenericParamKind genericParameter) == GrammarV1EffectsKind
      ]
    effectClauses =
      [ effectSet
      | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses source
      ]

-- | Resolve one argument-bearing effect only when every effect argument is one
-- simple active lexical subject. Argument-free effects preserve their established
-- Core identity byte-for-byte. Subject-bearing effects use a versioned canonical
-- SemanticForm containing the checked effect label and resolver-issued Core Name
-- of each exact subject, so alpha-renaming cannot change effect identity and two
-- equal-typed local subjects cannot collapse merely because their representation
-- or source spelling happens to coincide.
grammarV1CheckedSubjectIndexedSemanticEffect
  :: GrammarV1LexicalScope
  -> Located GrammarV1EffectExpression
  -> Maybe
      (Either
        GrammarV1SubjectIndexedEffectError
        GrammarV1CheckedSubjectIndexedEffect)
grammarV1CheckedSubjectIndexedSemanticEffect scope (Located _ effect)
  | null arguments = do
      core <- grammarV1SemanticEffect effect
      pure (Right (GrammarV1CheckedSubjectIndexedEffect core []))
  | not (null (grammarV1StaticReferenceArguments reference)) = Nothing
  | null labelParts = Nothing
  | otherwise = do
      checkedArguments <- mapM (checkedEffectSubject scope) arguments
      pure $ do
        references <- sequence checkedArguments
        let subjects = map
              (grammarV1ResolvedBinderCoreName . grammarV1CheckedLexicalReferenceBinder)
              references
        Right GrammarV1CheckedSubjectIndexedEffect
          { checkedSubjectIndexedEffectCore =
              canonicalSubjectIndexedEffect labelParts subjects
          , checkedSubjectIndexedEffectReferences = references
          }
  where
    arguments = grammarV1EffectArguments effect
    reference = locatedValue (grammarV1EffectReference effect)
    labelParts = grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference)

-- | Resolve one literal effect set under one exact lexical scope. Set
-- canonicalization remains the already-established concrete carrier; exact
-- lexical evidence is retained in source occurrence order separately.
grammarV1CheckedSubjectIndexedEffectSet
  :: GrammarV1LexicalScope
  -> GrammarV1EffectSetExpression
  -> Maybe
      (Either
        GrammarV1SubjectIndexedEffectError
        (Set.Set SemanticEffect, [GrammarV1CheckedLexicalReference]))
grammarV1CheckedSubjectIndexedEffectSet scope source = case source of
  GrammarV1EffectSetLiteral effects -> do
    checked <- mapM (grammarV1CheckedSubjectIndexedSemanticEffect scope) effects
    pure $ do
      resolved <- sequence checked
      Right
        ( Set.fromList (map checkedSubjectIndexedEffectCore resolved)
        , concatMap checkedSubjectIndexedEffectReferences resolved
        )
  GrammarV1EffectSetReference _ -> Nothing

-- | Compose the bounded subject-indexed literal route across callable `effects`
-- clauses. Generic Effects references remain owned by the separate stable-key
-- route and are intentionally outside this first EFF slice.
grammarV1CheckedSubjectIndexedCallableEffectBounds
  :: GrammarV1LexicalScope
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SubjectIndexedEffectError
        [(Set.Set SemanticEffect, [GrammarV1CheckedLexicalReference])])
grammarV1CheckedSubjectIndexedCallableEffectBounds scope source =
  sequence <$> mapM elaborate
    [ effectSet
    | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses source
    ]
  where
    elaborate (Located _ effectSet) =
      grammarV1CheckedSubjectIndexedEffectSet scope effectSet

checkedEffectSubject
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe
      (Either
        GrammarV1SubjectIndexedEffectError
        GrammarV1CheckedLexicalReference)
checkedEffectSubject scope source@(Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments
    | null arguments
    , null (grammarV1StaticReferenceArguments reference)
    , [_] <- grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) -> do
        checked <- grammarV1CheckedExpressionReferences Set.empty scope source
        pure $ case checked of
          Left referenceError -> Left
            (GrammarV1EffectSubjectReferenceError referenceError)
          Right [resolved] -> Right resolved
          Right _ -> Left (GrammarV1EffectSubjectNotLocal source)
  _ -> Nothing

canonicalSubjectIndexedEffect :: [Text.Text] -> [Name] -> SemanticEffect
canonicalSubjectIndexedEffect labelParts subjects =
  SemanticEffect
    ( "phil.effect.subject.v1:"
      <> canonicalSemanticForm
        (SemanticRecord (Map.fromList
          [ ("label", SemanticOrdered (map SemanticAtom labelParts))
          , ("subjects", SemanticOrdered (map subjectForm subjects))
          ]))
    )
  where
    subjectForm (Name name) = SemanticAtom name

validateEffectsParameterEvidence
  :: [Located GrammarV1GenericParam]
  -> [GrammarV1ResolvedCallableEffectsParameter]
  -> Either GrammarV1CallableEffectReferenceError (Set.Set GenericStaticParameterKey)
validateEffectsParameterEvidence sourceParameters evidence
  | length sourceParameters /= length evidence = Left
      (GrammarV1CallableEffectsParameterEvidenceCountMismatch
        (length sourceParameters)
        (length evidence))
  | otherwise = go 0 Set.empty sourceParameters evidence
  where
    go _ keys [] [] = Right keys
    go index keys (sourceParameter : sourceRest) (resolved : resolvedRest)
      | sourceParameter /= resolvedCallableEffectsSourceParameter resolved = Left
          (GrammarV1CallableEffectsParameterSourceMismatch
            index
            sourceParameter
            (resolvedCallableEffectsSourceParameter resolved))
      | genericStaticParameterKind parameter /= GenericEffectsKind = Left
          (GrammarV1CallableEffectsParameterKindMismatch
            key
            (genericStaticParameterKind parameter))
      | Set.member key keys = Left
          (GrammarV1DuplicateCallableEffectsParameterKey key)
      | otherwise = go
          (index + 1)
          (Set.insert key keys)
          sourceRest
          resolvedRest
      where
        parameter = resolvedCallableEffectsParameter resolved
        key = genericStaticParameterKey parameter
    go _ _ _ _ = Left
      (GrammarV1CallableEffectsParameterEvidenceCountMismatch
        (length sourceParameters)
        (length evidence))

projectEffectClauses
  :: Set.Set GenericStaticParameterKey
  -> [GrammarV1ResolvedCallableEffectUse]
  -> [Located GrammarV1EffectSetExpression]
  -> Maybe
      (Either
        GrammarV1CallableEffectReferenceError
        ([GrammarV1CallableEffectBoundTemplate], [Located GrammarV1EffectSetExpression]))
projectEffectClauses _ _ [] = Just (Right ([], []))
projectEffectClauses parameterKeys evidence (sourceUse : rest) = do
  first <- projectEffectClause parameterKeys evidence sourceUse
  case first of
    Left err -> Just (Left err)
    Right (bound, ownUses) -> do
      remaining <- projectEffectClauses parameterKeys evidence rest
      pure $ fmap
        (\(bounds, used) -> (bound : bounds, ownUses <> used))
        remaining

projectEffectClause
  :: Set.Set GenericStaticParameterKey
  -> [GrammarV1ResolvedCallableEffectUse]
  -> Located GrammarV1EffectSetExpression
  -> Maybe
      (Either
        GrammarV1CallableEffectReferenceError
        (GrammarV1CallableEffectBoundTemplate, [Located GrammarV1EffectSetExpression]))
projectEffectClause parameterKeys evidence sourceUse@(Located _ effectSet) =
  case effectSet of
    GrammarV1EffectSetLiteral _ -> do
      concrete <- grammarV1EffectSet effectSet
      Just (Right (GrammarV1ConcreteCallableEffectBound concrete, []))
    GrammarV1EffectSetReference reference
      | not (null (grammarV1StaticReferenceArguments (locatedValue reference))) -> Nothing
      | otherwise -> Just $ case matchingEffectUseEvidence sourceUse evidence of
          [] -> Left (GrammarV1MissingCallableEffectUseEvidence sourceUse)
          [resolved]
            | not (Set.member key parameterKeys) -> Left
                (GrammarV1CallableEffectUseUndeclaredParameter key)
            | otherwise -> Right
                (GrammarV1CallableEffectsParameterBound key, [sourceUse])
            where
              key = resolvedCallableEffectUseParameterKey resolved
          _ -> Left (GrammarV1DuplicateCallableEffectUseEvidence sourceUse)

matchingEffectUseEvidence
  :: Located GrammarV1EffectSetExpression
  -> [GrammarV1ResolvedCallableEffectUse]
  -> [GrammarV1ResolvedCallableEffectUse]
matchingEffectUseEvidence sourceUse = filter
  ((== sourceUse) . resolvedCallableEffectSourceUse)

firstUnexpectedEffectUseEvidence
  :: [Located GrammarV1EffectSetExpression]
  -> [GrammarV1ResolvedCallableEffectUse]
  -> Maybe GrammarV1ResolvedCallableEffectUse
firstUnexpectedEffectUseEvidence used = firstUnexpected
  where
    firstUnexpected [] = Nothing
    firstUnexpected (entry : rest)
      | resolvedCallableEffectSourceUse entry `elem` used = firstUnexpected rest
      | otherwise = Just entry
