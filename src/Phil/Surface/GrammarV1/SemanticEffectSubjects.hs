module Phil.Surface.GrammarV1.SemanticEffectSubjects
  ( GrammarV1ResolvedExternalEffectSubject (..)
  , GrammarV1CheckedResolvedSubjectEffect (..)
  , GrammarV1ResolvedEffectSubjectError (..)
  , grammarV1CheckedResolvedSubjectSemanticEffect
  , grammarV1CheckedResolvedSubjectEffectSet
  , grammarV1CheckedResolvedSubjectCallableEffectBounds
  ) where

import qualified Data.Set as Set
import Phil.Core.Callable (SemanticEffect)
import Phil.Core.Effect
  ( CheckedSemanticEffect (..)
  , SemanticEffectCheckError
  , SemanticEffectSubjectKey (..)
  , checkedSemanticEffect
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
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact semantic evidence for one nonlocal effect-subject occurrence. The
-- competent declaration/kind-specific resolver supplies the semantic key and
-- repeats the exact Located source occurrence so this consumer can verify the
-- handoff without deriving identity from source spelling.
data GrammarV1ResolvedExternalEffectSubject = GrammarV1ResolvedExternalEffectSubject
  { resolvedExternalEffectSubjectSource :: Located GrammarV1Expression
  , resolvedExternalEffectSubjectKey :: SemanticEffectSubjectKey
  }
  deriving (Eq, Show)

-- | One effect after every subject occurrence has been resolved either through
-- the active SURF-009 lexical scope or through exact external resolver evidence.
-- The two evidence classes remain separate for auditability.
data GrammarV1CheckedResolvedSubjectEffect = GrammarV1CheckedResolvedSubjectEffect
  { checkedResolvedSubjectEffectCore :: SemanticEffect
  , checkedResolvedSubjectEffectLexicalReferences :: [GrammarV1CheckedLexicalReference]
  , checkedResolvedSubjectEffectExternalEvidence :: [GrammarV1ResolvedExternalEffectSubject]
  }
  deriving (Eq, Show)

data GrammarV1ResolvedEffectSubjectError
  = GrammarV1ResolvedEffectSubjectReferenceError GrammarV1LexicalReferenceError
  | GrammarV1MissingExternalEffectSubjectEvidence (Located GrammarV1Expression)
  | GrammarV1DuplicateExternalEffectSubjectEvidence (Located GrammarV1Expression)
  | GrammarV1UnexpectedExternalEffectSubjectEvidence (Located GrammarV1Expression)
  | GrammarV1ResolvedEffectCoreError SemanticEffectCheckError
  deriving (Eq, Show)

-- | Resolve one effect. Active lexical identity always has priority: external
-- evidence cannot override a local binder with the same spelling. A nonlocal
-- name-shaped argument requires exactly one evidence item tied to that exact
-- source occurrence. Qualified or unqualified presentation spelling is never
-- converted into semantic subject identity here.
grammarV1CheckedResolvedSubjectSemanticEffect
  :: GrammarV1LexicalScope
  -> [GrammarV1ResolvedExternalEffectSubject]
  -> Located GrammarV1EffectExpression
  -> Maybe
      (Either
        GrammarV1ResolvedEffectSubjectError
        GrammarV1CheckedResolvedSubjectEffect)
grammarV1CheckedResolvedSubjectSemanticEffect scope evidence (Located _ effect)
  | not (null (grammarV1StaticReferenceArguments reference)) = Nothing
  | null labelParts = Nothing
  | otherwise = do
      checkedArguments <- mapM (checkedEffectSubject scope evidence) arguments
      pure $ do
        subjects <- sequence checkedArguments
        checkedCore <- mapLeft GrammarV1ResolvedEffectCoreError
          (checkedSemanticEffect labelParts (map resolvedSubjectKey subjects))
        Right GrammarV1CheckedResolvedSubjectEffect
          { checkedResolvedSubjectEffectCore = checkedSemanticEffectCore checkedCore
          , checkedResolvedSubjectEffectLexicalReferences =
              concatMap resolvedSubjectLexical subjects
          , checkedResolvedSubjectEffectExternalEvidence =
              concatMap resolvedSubjectExternal subjects
          }
  where
    arguments = grammarV1EffectArguments effect
    reference = locatedValue (grammarV1EffectReference effect)
    labelParts = grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference)

-- | Resolve one literal effect set and reject any external evidence that was not
-- consumed by an exact nonlocal subject occurrence in that set.
grammarV1CheckedResolvedSubjectEffectSet
  :: GrammarV1LexicalScope
  -> [GrammarV1ResolvedExternalEffectSubject]
  -> GrammarV1EffectSetExpression
  -> Maybe
      (Either
        GrammarV1ResolvedEffectSubjectError
        ( Set.Set SemanticEffect
        , [GrammarV1CheckedLexicalReference]
        , [GrammarV1ResolvedExternalEffectSubject]
        ))
grammarV1CheckedResolvedSubjectEffectSet scope evidence source = do
  checked <- checkedEffectSet scope evidence source
  pure $ do
    (effects, lexical, usedExternal) <- checked
    case firstUnexpectedExternal usedExternal evidence of
      Just extra -> Left
        (GrammarV1UnexpectedExternalEffectSubjectEvidence
          (resolvedExternalEffectSubjectSource extra))
      Nothing -> Right (effects, lexical, usedExternal)

-- | Compose exact local/nonlocal subject resolution across callable `effects`
-- clauses. Effect-set references remain owned by the EFF-003/004 polymorphism
-- path; this EFF-001/002 route handles concrete literal effects only.
grammarV1CheckedResolvedSubjectCallableEffectBounds
  :: GrammarV1LexicalScope
  -> [GrammarV1ResolvedExternalEffectSubject]
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1ResolvedEffectSubjectError
        [ ( Set.Set SemanticEffect
          , [GrammarV1CheckedLexicalReference]
          , [GrammarV1ResolvedExternalEffectSubject]
          )
        ])
grammarV1CheckedResolvedSubjectCallableEffectBounds scope evidence source = do
  checked <- mapM (checkedEffectSet scope evidence . locatedValue) effectClauses
  pure $ do
    resolved <- sequence checked
    let usedExternal = concatMap third resolved
    case firstUnexpectedExternal usedExternal evidence of
      Just extra -> Left
        (GrammarV1UnexpectedExternalEffectSubjectEvidence
          (resolvedExternalEffectSubjectSource extra))
      Nothing -> Right resolved
  where
    effectClauses =
      [ effectSet
      | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses source
      ]

checkedEffectSet
  :: GrammarV1LexicalScope
  -> [GrammarV1ResolvedExternalEffectSubject]
  -> GrammarV1EffectSetExpression
  -> Maybe
      (Either
        GrammarV1ResolvedEffectSubjectError
        ( Set.Set SemanticEffect
        , [GrammarV1CheckedLexicalReference]
        , [GrammarV1ResolvedExternalEffectSubject]
        ))
checkedEffectSet scope evidence source = case source of
  GrammarV1EffectSetLiteral effects -> do
    checked <- mapM
      (grammarV1CheckedResolvedSubjectSemanticEffect scope evidence)
      effects
    pure $ do
      resolved <- sequence checked
      Right
        ( Set.fromList (map checkedResolvedSubjectEffectCore resolved)
        , concatMap checkedResolvedSubjectEffectLexicalReferences resolved
        , concatMap checkedResolvedSubjectEffectExternalEvidence resolved
        )
  GrammarV1EffectSetReference _ -> Nothing

data ResolvedSubject = ResolvedSubject
  { resolvedSubjectKey :: SemanticEffectSubjectKey
  , resolvedSubjectLexical :: [GrammarV1CheckedLexicalReference]
  , resolvedSubjectExternal :: [GrammarV1ResolvedExternalEffectSubject]
  }

checkedEffectSubject
  :: GrammarV1LexicalScope
  -> [GrammarV1ResolvedExternalEffectSubject]
  -> Located GrammarV1Expression
  -> Maybe (Either GrammarV1ResolvedEffectSubjectError ResolvedSubject)
checkedEffectSubject scope evidence source@(Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments
    | null arguments
    , null (grammarV1StaticReferenceArguments reference) -> do
        checked <- grammarV1CheckedExpressionReferences Set.empty scope source
        pure $ case checked of
          Left referenceError -> Left
            (GrammarV1ResolvedEffectSubjectReferenceError referenceError)
          Right [resolved] -> Right ResolvedSubject
            { resolvedSubjectKey = lexicalSubjectKey resolved
            , resolvedSubjectLexical = [resolved]
            , resolvedSubjectExternal = []
            }
          Right [] -> case matchingExternal source evidence of
            [] -> Left (GrammarV1MissingExternalEffectSubjectEvidence source)
            [resolved] -> Right ResolvedSubject
              { resolvedSubjectKey = resolvedExternalEffectSubjectKey resolved
              , resolvedSubjectLexical = []
              , resolvedSubjectExternal = [resolved]
              }
            _ -> Left (GrammarV1DuplicateExternalEffectSubjectEvidence source)
          Right _ -> Left (GrammarV1MissingExternalEffectSubjectEvidence source)
  _ -> Nothing

lexicalSubjectKey :: GrammarV1CheckedLexicalReference -> SemanticEffectSubjectKey
lexicalSubjectKey =
  coreNameSubjectKey
    . grammarV1ResolvedBinderCoreName
    . grammarV1CheckedLexicalReferenceBinder

coreNameSubjectKey :: Name -> SemanticEffectSubjectKey
coreNameSubjectKey (Name name) = SemanticEffectSubjectKey name

matchingExternal
  :: Located GrammarV1Expression
  -> [GrammarV1ResolvedExternalEffectSubject]
  -> [GrammarV1ResolvedExternalEffectSubject]
matchingExternal source = filter ((== source) . resolvedExternalEffectSubjectSource)

firstUnexpectedExternal
  :: [GrammarV1ResolvedExternalEffectSubject]
  -> [GrammarV1ResolvedExternalEffectSubject]
  -> Maybe GrammarV1ResolvedExternalEffectSubject
firstUnexpectedExternal used = firstUnexpected
  where
    usedSources = map resolvedExternalEffectSubjectSource used
    firstUnexpected [] = Nothing
    firstUnexpected (entry : rest)
      | resolvedExternalEffectSubjectSource entry `elem` usedSources = firstUnexpected rest
      | otherwise = Just entry

third :: (a, b, c) -> c
third (_, _, value) = value

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
