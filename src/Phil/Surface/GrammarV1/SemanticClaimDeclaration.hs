module Phil.Surface.GrammarV1.SemanticClaimDeclaration
  ( GrammarV1CheckedSemanticClaimDeclaration (..)
  , GrammarV1SemanticClaimDeclarationError (..)
  , grammarV1CheckedSemanticClaimDeclaration
  , grammarV1RegisterSemanticClaimDeclaration
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.SortCheck (refSortOfTy)
import Phil.Core.Static
  ( ClaimDecl (..)
  , ClaimDefinition (..)
  , DeclarationKey
  , StaticContext
  , StaticError
  , declareOpaqueClaim
  , declareTransparentClaim
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name
  , RefSort
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1ClaimParameterScope
  )
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedPropositionReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ClaimDecl (..)
  , GrammarV1Proposition
  , GrammarV1TermParam (..)
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewritePropositionReferences
  )
import Phil.Surface.Syntax (Located (..))

-- | One checked claim declaration whose term parameters carry exact SURF-009
-- binder identity. The optional parameter carrier preserves omitted versus
-- explicit-empty source syntax for diagnostics/composition, while the Core
-- ClaimDecl uses generated semantic names throughout its parameter telescope and
-- transparent body.
data GrammarV1CheckedSemanticClaimDeclaration =
  GrammarV1CheckedSemanticClaimDeclaration
    { checkedSemanticClaimDeclarationKey :: DeclarationKey
    , checkedSemanticClaimDisplayName :: Text
    , checkedSemanticClaimParameters :: Maybe [(GrammarV1ResolvedBinder, RefSort)]
    , checkedSemanticClaimDefinition :: ClaimDefinition
    , checkedSemanticClaimBodyReferences :: Maybe [GrammarV1CheckedLexicalReference]
    , checkedSemanticClaimCoreDeclaration :: ClaimDecl
    , checkedSemanticClaimState :: SurfaceState
    }
  deriving (Eq, Show)

data GrammarV1SemanticClaimDeclarationError
  = GrammarV1SemanticClaimBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticClaimBindingInsertError SurfaceCheckError
  | GrammarV1SemanticClaimBodyReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticClaimBodyRewriteNonCompetent (Located GrammarV1Proposition)
  | GrammarV1SemanticClaimBodyCheckNonCompetent (Located GrammarV1Proposition)
  | GrammarV1SemanticClaimRegistrationError StaticError
  deriving (Eq, Show)

-- | Migrate the bounded primitive claim-declaration bridge onto resolver-issued
-- term identity without changing the older SURF-008 API. Generic parameters and
-- requirements remain outside this slice. Primitive Bool/U<n> parameters retain
-- the existing RefSort competence, but are inserted into a fresh SurfaceState
-- under generated Core names rather than display spelling.
--
-- Transparent bodies are lexical-reference checked against that exact claim
-- scope, rewritten only at certified local occurrences, and then delegated to the
-- existing binding-aware proposition bridge. Opaque claims use the same generated
-- parameter telescope but have no body or body-reference evidence.
grammarV1CheckedSemanticClaimDeclaration
  :: DeclarationKey
  -> GrammarV1ClaimDecl
  -> Maybe
      (Either
        GrammarV1SemanticClaimDeclarationError
        GrammarV1CheckedSemanticClaimDeclaration)
grammarV1CheckedSemanticClaimDeclaration declarationKey source
  | not (null (grammarV1ClaimGenericParams source)) = Nothing
  | not (null (grammarV1ClaimRequirements source)) = Nothing
  | otherwise =
      case grammarV1ClaimParameterScope declarationKey source of
        Left scopeError ->
          Just (Left (GrammarV1SemanticClaimBinderScopeError scopeError))
        Right (maybeBinders, lexicalScope) -> do
          built <- buildSemanticParameters
            maybeBinders
            (grammarV1ClaimTermParams source)
          case built of
            Left buildError -> Just (Left buildError)
            Right (parameters, coreParameters, semanticState) ->
              case grammarV1ClaimProposition source of
                Nothing -> Just
                  (Right
                    (buildChecked
                      parameters
                      OpaqueClaim
                      Nothing
                      coreParameters
                      semanticState))
                Just bodySource ->
                  case grammarV1CheckedPropositionReferences
                      Set.empty
                      lexicalScope
                      bodySource of
                    Nothing ->
                      Just
                        (Left
                          (GrammarV1SemanticClaimBodyCheckNonCompetent bodySource))
                    Just (Left referenceError) ->
                      Just
                        (Left
                          (GrammarV1SemanticClaimBodyReferenceError referenceError))
                    Just (Right references) ->
                      case grammarV1RewritePropositionReferences references bodySource of
                        Nothing ->
                          Just
                            (Left
                              (GrammarV1SemanticClaimBodyRewriteNonCompetent
                                bodySource))
                        Just rewrittenBody ->
                          case grammarV1BoundProposition
                              semanticState
                              (locatedValue rewrittenBody) of
                            Nothing ->
                              Just
                                (Left
                                  (GrammarV1SemanticClaimBodyCheckNonCompetent
                                    bodySource))
                            Just proposition ->
                              Just
                                (Right
                                  (buildChecked
                                    parameters
                                    (TransparentClaim proposition)
                                    (Just references)
                                    coreParameters
                                    semanticState))
  where
    buildChecked parameters definition references coreParameters semanticState =
      GrammarV1CheckedSemanticClaimDeclaration
        { checkedSemanticClaimDeclarationKey = declarationKey
        , checkedSemanticClaimDisplayName = locatedValue (grammarV1ClaimName source)
        , checkedSemanticClaimParameters = parameters
        , checkedSemanticClaimDefinition = definition
        , checkedSemanticClaimBodyReferences = references
        , checkedSemanticClaimCoreDeclaration = ClaimDecl
            { claimParameters = coreParameters
            , claimDefinition = definition
            }
        , checkedSemanticClaimState = semanticState
        }

-- | Register the exact semantic ClaimDecl only through Core's established static
-- authority. Surface non-competence remains Nothing; resolver/elaboration errors
-- and Core registration errors remain explicit and disjoint constructors.
grammarV1RegisterSemanticClaimDeclaration
  :: DeclarationKey
  -> GrammarV1ClaimDecl
  -> StaticContext
  -> Maybe
      (Either
        GrammarV1SemanticClaimDeclarationError
        StaticContext)
grammarV1RegisterSemanticClaimDeclaration declarationKey source context = do
  checked <- grammarV1CheckedSemanticClaimDeclaration declarationKey source
  pure $ do
    declaration <- checked
    let claimName = checkedSemanticClaimDisplayName declaration
        coreDeclaration = checkedSemanticClaimCoreDeclaration declaration
    mapLeft GrammarV1SemanticClaimRegistrationError $
      case claimDefinition coreDeclaration of
        OpaqueClaim ->
          declareOpaqueClaim claimName (claimParameters coreDeclaration) context
        TransparentClaim proposition ->
          declareTransparentClaim
            claimName
            (claimParameters coreDeclaration)
            proposition
            context

buildSemanticParameters
  :: Maybe [GrammarV1ResolvedBinder]
  -> Maybe [Located GrammarV1TermParam]
  -> Maybe
      (Either
        GrammarV1SemanticClaimDeclarationError
        ( Maybe [(GrammarV1ResolvedBinder, RefSort)]
        , [(Name, RefSort)]
        , SurfaceState
        ))
buildSemanticParameters maybeBinders maybeParameters =
  case (maybeBinders, maybeParameters) of
    (Nothing, Nothing) ->
      Just (Right (Nothing, [], emptySurfaceState))
    (Just binders, Just parameters) -> do
      built <- buildPresentParameters binders parameters
      pure $ fmap
        (\(checked, coreParameters, state) ->
          (Just checked, coreParameters, state))
        built
    _ -> Nothing

buildPresentParameters
  :: [GrammarV1ResolvedBinder]
  -> [Located GrammarV1TermParam]
  -> Maybe
      (Either
        GrammarV1SemanticClaimDeclarationError
        ( [(GrammarV1ResolvedBinder, RefSort)]
        , [(Name, RefSort)]
        , SurfaceState
        ))
buildPresentParameters = go [] [] emptySurfaceState
  where
    go reversedChecked reversedCore state [] [] =
      Just
        (Right
          ( reverse reversedChecked
          , reverse reversedCore
          , state
          ))
    go reversedChecked reversedCore state
        (binder : binders)
        (Located _ parameter : parameters) = do
      ty <- grammarV1PrimitiveType
        (locatedValue (grammarV1TermParamType parameter))
      sort <- refSortOfTy ty
      case grammarV1InsertSemanticBinding
          binder
          (BindingMeta Unrestricted ty PlainShape)
          state of
        Left insertError ->
          Just (Left (GrammarV1SemanticClaimBindingInsertError insertError))
        Right nextState ->
          go
            ((binder, sort) : reversedChecked)
            ((grammarV1ResolvedBinderCoreName binder, sort) : reversedCore)
            nextState
            binders
            parameters
    go _ _ _ _ _ = Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
