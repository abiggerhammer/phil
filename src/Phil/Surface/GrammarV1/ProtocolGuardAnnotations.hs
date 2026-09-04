module Phil.Surface.GrammarV1.ProtocolGuardAnnotations
  ( GrammarV1ProtocolGuardSite (..)
  , GrammarV1CheckedProtocolGuardAnnotation (..)
  , GrammarV1ClosedProtocolGuardSurface (..)
  , GrammarV1ProtocolGuardError (..)
  , grammarV1CheckedClosedProtocolGuardSurface
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family (ProtocolSessionTemplate)
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1Proposition
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError
  , grammarV1CheckedClosedProtocolRoleTemplates
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact structural site of one source protocol guard. The site records only
-- author-visible placement; it is not an obligation/revision identity and does
-- not claim assurance authority to exercise the transition.
data GrammarV1ProtocolGuardSite
  = GrammarV1SendGuard
  | GrammarV1ReceiveGuard
  | GrammarV1SelectBranchGuard Text
  | GrammarV1OfferBranchGuard Text
  deriving (Eq, Show)

-- | One context-free source guard after ordinary Grammar-v1 proposition checking
-- and Core focusing. The exact source proposition remains attached so later
-- obligation/assurance handling cannot silently substitute a different guard.
data GrammarV1CheckedProtocolGuardAnnotation =
  GrammarV1CheckedProtocolGuardAnnotation
    { checkedProtocolGuardRole :: ProtocolRoleKey
    , checkedProtocolGuardSite :: GrammarV1ProtocolGuardSite
    , checkedProtocolGuardSource :: Located GrammarV1Proposition
    , checkedProtocolGuardProposition :: Proposition
    , checkedProtocolGuardFocusTrace :: [FocusStep]
    }
  deriving (Eq, Show)

-- | Checked closed role templates plus exact source-ordered context-free guard
-- propositions removed before the established closed protocol checker ran.
data GrammarV1ClosedProtocolGuardSurface = GrammarV1ClosedProtocolGuardSurface
  { checkedProtocolGuardRoleTemplates
      :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
         , (ProtocolRoleKey, ProtocolSessionTemplate)
         )
  , checkedProtocolGuardAnnotations
      :: [GrammarV1CheckedProtocolGuardAnnotation]
  }
  deriving (Eq, Show)

data GrammarV1ProtocolGuardError
  = GrammarV1ProtocolGuardRoleError GrammarV1ProtocolRoleError
  | GrammarV1ProtocolGuardFocusingError
      Int
      ProtocolRoleKey
      GrammarV1ProtocolGuardSite
      FocusingError
  deriving (Eq, Show)

-- | Check the first protocol-guard fragment whose propositions do not depend on
-- live message or branch-payload binders.
--
-- Guards are collected in exact source preorder and removed from a structural
-- copy before delegating to 'grammarV1CheckedClosedProtocolRoleTemplates'. Thus
-- primitive payload typing, recursion validity, duplicate-role rejection and
-- alpha-aware duality remain authoritative; a guard cannot make an otherwise
-- invalid protocol acceptable.
--
-- Each guard proposition is checked under the caller-supplied StaticContext but
-- an empty top-level term scope. This intentionally admits binder-free guards
-- such as `when true` and closed claim applications while leaving any proposition
-- that needs a send/receive or branch-payload binder outside this SURF-008 slice.
-- SURF-009 remains authoritative for those binder identities/scopes.
--
-- Protocol boundary annotations remain a separate exact semantic dimension and
-- therefore keep this route outside competence rather than being erased. Generic
-- and requirement-bearing protocols, static session references, richer payloads,
-- and all other unsupported closed-session forms continue to fail through the
-- delegated checker. This slice preserves checked propositions only: it does not
-- derive ProtocolTransitionGuard revision identity, discharge guard obligations,
-- supply assurance evidence, or assert peer-guard equivalence.
grammarV1CheckedClosedProtocolGuardSurface
  :: StaticContext
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolGuardError
        GrammarV1ClosedProtocolGuardSurface)
grammarV1CheckedClosedProtocolGuardSurface staticContext source = do
  (strippedRoles, guards) <- stripRoles (grammarV1ProtocolRoles source)
  if null guards
    then Nothing
    else do
      let stripped = source { grammarV1ProtocolRoles = strippedRoles }
      checkedTemplates <- grammarV1CheckedClosedProtocolRoleTemplates stripped
      case checkedTemplates of
        Left err -> pure (Left (GrammarV1ProtocolGuardRoleError err))
        Right templates -> do
          checked <- mapM
            (\(index, guard) -> checkGuard staticContext index guard)
            (zip [0 ..] guards)
          pure $ do
            annotations <- sequence checked
            Right GrammarV1ClosedProtocolGuardSurface
              { checkedProtocolGuardRoleTemplates = templates
              , checkedProtocolGuardAnnotations = annotations
              }

data GrammarV1ProtocolGuardOccurrence = GrammarV1ProtocolGuardOccurrence
  { protocolGuardOccurrenceRole :: ProtocolRoleKey
  , protocolGuardOccurrenceSite :: GrammarV1ProtocolGuardSite
  , protocolGuardOccurrenceSource :: Located GrammarV1Proposition
  }

stripRoles
  :: [Located GrammarV1RoleSessionDecl]
  -> Maybe
      ( [Located GrammarV1RoleSessionDecl]
      , [GrammarV1ProtocolGuardOccurrence]
      )
stripRoles [] = Just ([], [])
stripRoles (Located roleSpan role : rest) = do
  let roleKey = ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
      Located sessionSpan session = grammarV1RoleSessionExpression role
  (strippedSession, ownGuards) <- stripSession roleKey session
  (strippedRest, restGuards) <- stripRoles rest
  let strippedRole = role
        { grammarV1RoleSessionExpression = Located sessionSpan strippedSession }
  pure
    ( Located roleSpan strippedRole : strippedRest
    , ownGuards <> restGuards
    )

stripSession
  :: ProtocolRoleKey
  -> GrammarV1SessionExpression
  -> Maybe
      ( GrammarV1SessionExpression
      , [GrammarV1ProtocolGuardOccurrence]
      )
stripSession roleKey source = case source of
  GrammarV1SessionReference _ -> Just (source, [])
  GrammarV1SessionSend parameter Nothing guard continuation -> do
    own <- guardOccurrence roleKey GrammarV1SendGuard guard
    (strippedContinuation, continuationGuards) <-
      stripLocatedSession roleKey continuation
    pure
      ( GrammarV1SessionSend parameter Nothing Nothing strippedContinuation
      , own <> continuationGuards
      )
  GrammarV1SessionSend _ (Just _) _ _ -> Nothing
  GrammarV1SessionReceive parameter Nothing guard continuation -> do
    own <- guardOccurrence roleKey GrammarV1ReceiveGuard guard
    (strippedContinuation, continuationGuards) <-
      stripLocatedSession roleKey continuation
    pure
      ( GrammarV1SessionReceive parameter Nothing Nothing strippedContinuation
      , own <> continuationGuards
      )
  GrammarV1SessionReceive _ (Just _) _ _ -> Nothing
  GrammarV1SessionSelect branches -> do
    (strippedBranches, guards) <- stripBranches True roleKey branches
    pure (GrammarV1SessionSelect strippedBranches, guards)
  GrammarV1SessionOffer branches -> do
    (strippedBranches, guards) <- stripBranches False roleKey branches
    pure (GrammarV1SessionOffer strippedBranches, guards)
  GrammarV1SessionEnd _ -> Just (source, [])
  GrammarV1SessionRecursive recursionName body -> do
    (strippedBody, guards) <- stripLocatedSession roleKey body
    pure (GrammarV1SessionRecursive recursionName strippedBody, guards)
  GrammarV1SessionContinue _ -> Just (source, [])

stripLocatedSession
  :: ProtocolRoleKey
  -> Located GrammarV1SessionExpression
  -> Maybe
      ( Located GrammarV1SessionExpression
      , [GrammarV1ProtocolGuardOccurrence]
      )
stripLocatedSession roleKey (Located spanValue source) = do
  (stripped, guards) <- stripSession roleKey source
  pure (Located spanValue stripped, guards)

stripBranches
  :: Bool
  -> ProtocolRoleKey
  -> [Located GrammarV1SessionBranch]
  -> Maybe
      ( [Located GrammarV1SessionBranch]
      , [GrammarV1ProtocolGuardOccurrence]
      )
stripBranches _ _ [] = Just ([], [])
stripBranches selecting roleKey (Located branchSpan branch : rest)
  | grammarV1SessionBranchBoundary branch /= Nothing = Nothing
  | otherwise = do
      let label = locatedValue (grammarV1SessionBranchLabel branch)
          site
            | selecting = GrammarV1SelectBranchGuard label
            | otherwise = GrammarV1OfferBranchGuard label
      own <- guardOccurrence roleKey site (grammarV1SessionBranchGuard branch)
      (continuation, continuationGuards) <-
        stripLocatedSession
          roleKey
          (grammarV1SessionBranchContinuation branch)
      (strippedRest, restGuards) <- stripBranches selecting roleKey rest
      let strippedBranch = branch
            { grammarV1SessionBranchGuard = Nothing
            , grammarV1SessionBranchContinuation = continuation
            }
      pure
        ( Located branchSpan strippedBranch : strippedRest
        , own <> continuationGuards <> restGuards
        )

guardOccurrence
  :: ProtocolRoleKey
  -> GrammarV1ProtocolGuardSite
  -> Maybe (Located GrammarV1Proposition)
  -> Maybe [GrammarV1ProtocolGuardOccurrence]
guardOccurrence _ _ Nothing = Just []
guardOccurrence roleKey site (Just proposition) = Just
  [ GrammarV1ProtocolGuardOccurrence
      { protocolGuardOccurrenceRole = roleKey
      , protocolGuardOccurrenceSite = site
      , protocolGuardOccurrenceSource = proposition
      }
  ]

checkGuard
  :: StaticContext
  -> Int
  -> GrammarV1ProtocolGuardOccurrence
  -> Maybe
      (Either
        GrammarV1ProtocolGuardError
        GrammarV1CheckedProtocolGuardAnnotation)
checkGuard staticContext index occurrence = do
  checked <- grammarV1CheckedProposition
    staticContext
    emptySurfaceState
    (locatedValue (protocolGuardOccurrenceSource occurrence))
  pure $ case checked of
    Left err -> Left
      (GrammarV1ProtocolGuardFocusingError
        index
        (protocolGuardOccurrenceRole occurrence)
        (protocolGuardOccurrenceSite occurrence)
        err)
    Right (proposition, steps) -> Right GrammarV1CheckedProtocolGuardAnnotation
      { checkedProtocolGuardRole = protocolGuardOccurrenceRole occurrence
      , checkedProtocolGuardSite = protocolGuardOccurrenceSite occurrence
      , checkedProtocolGuardSource = protocolGuardOccurrenceSource occurrence
      , checkedProtocolGuardProposition = proposition
      , checkedProtocolGuardFocusTrace = steps
      }
