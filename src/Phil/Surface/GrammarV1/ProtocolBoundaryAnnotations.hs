module Phil.Surface.GrammarV1.ProtocolBoundaryAnnotations
  ( GrammarV1ProtocolBoundarySite (..)
  , GrammarV1ProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedProtocolBoundarySurface (..)
  , grammarV1CheckedClosedProtocolBoundarySurface
  ) where

import Data.Text (Text)
import Phil.Core.Generic.StaticActual (GenericStaticActual)
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family (ProtocolSessionTemplate)
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError
  , grammarV1CheckedClosedProtocolRoleTemplates
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact structural site of one source protocol boundary annotation. This site
-- records only the author-visible placement needed to keep distinct annotations
-- distinct; it is not a runtime boundary identity or transport choice.
data GrammarV1ProtocolBoundarySite
  = GrammarV1SendBoundary
  | GrammarV1ReceiveBoundary
  | GrammarV1SelectBranchBoundary Text
  | GrammarV1OfferBranchBoundary Text
  deriving (Eq, Show)

-- | One bare/qualified, unspecialized boundary annotation preserved beside the
-- checked protocol template. The source occurrence is retained exactly and the
-- static reference remains unresolved as GenericStaticActual: this bridge does
-- not claim boundary-contract existence, qualification, representation, codec,
-- transport, authority, or peer compatibility.
data GrammarV1ProtocolBoundaryAnnotation = GrammarV1ProtocolBoundaryAnnotation
  { protocolBoundaryRole :: ProtocolRoleKey
  , protocolBoundarySite :: GrammarV1ProtocolBoundarySite
  , protocolBoundarySourceReference :: Located GrammarV1StaticReference
  , protocolBoundaryStaticReference :: GenericStaticActual
  }
  deriving (Eq, Show)

-- | Checked closed role templates plus the exact ordered protocol-boundary
-- annotations that were deliberately removed before delegating session semantics
-- to the existing closed protocol checker.
data GrammarV1ClosedProtocolBoundarySurface = GrammarV1ClosedProtocolBoundarySurface
  { checkedProtocolBoundaryRoleTemplates
      :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
         , (ProtocolRoleKey, ProtocolSessionTemplate)
         )
  , checkedProtocolBoundaryAnnotations
      :: [GrammarV1ProtocolBoundaryAnnotation]
  }
  deriving (Eq, Show)

-- | Preserve the first closed Grammar-v1 protocol fragment containing explicit
-- boundary annotations without pretending Core BinaryProtocolFamily stores those
-- annotations today.
--
-- Bare/qualified unspecialized `using` references are collected in exact source
-- preorder and removed from a structural copy of the protocol. That copy is then
-- handed unchanged to grammarV1CheckedClosedProtocolRoleTemplates, so primitive
-- payload typing, recursion validity, duplicate-role rejection and alpha-aware
-- duality remain owned by the already-established semantic route. A boundary
-- annotation therefore cannot make an otherwise invalid protocol acceptable.
--
-- Guards remain non-competence because their propositions may depend on the live
-- message binder. Specialized boundary references also remain non-competence so
-- their static arguments cannot be erased. Generic/requirement-bearing protocols,
-- static session references, richer payloads and all other unsupported session
-- forms continue to fail through the delegated closed checker. This bridge does
-- not assert peer boundary compatibility or construct runtime boundary evidence.
grammarV1CheckedClosedProtocolBoundarySurface
  :: GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolRoleError
        GrammarV1ClosedProtocolBoundarySurface)
grammarV1CheckedClosedProtocolBoundarySurface source = do
  (strippedRoles, annotations) <- stripRoles (grammarV1ProtocolRoles source)
  let stripped = source { grammarV1ProtocolRoles = strippedRoles }
  checked <- grammarV1CheckedClosedProtocolRoleTemplates stripped
  pure $ fmap
    (\templates -> GrammarV1ClosedProtocolBoundarySurface
      { checkedProtocolBoundaryRoleTemplates = templates
      , checkedProtocolBoundaryAnnotations = annotations
      })
    checked

stripRoles
  :: [Located GrammarV1RoleSessionDecl]
  -> Maybe
      ( [Located GrammarV1RoleSessionDecl]
      , [GrammarV1ProtocolBoundaryAnnotation]
      )
stripRoles [] = Just ([], [])
stripRoles (Located roleSpan role : rest) = do
  let roleKey = ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
      Located sessionSpan session = grammarV1RoleSessionExpression role
  (strippedSession, ownAnnotations) <- stripSession roleKey session
  (strippedRest, restAnnotations) <- stripRoles rest
  let strippedRole = role
        { grammarV1RoleSessionExpression = Located sessionSpan strippedSession }
  pure
    ( Located roleSpan strippedRole : strippedRest
    , ownAnnotations <> restAnnotations
    )

stripSession
  :: ProtocolRoleKey
  -> GrammarV1SessionExpression
  -> Maybe
      ( GrammarV1SessionExpression
      , [GrammarV1ProtocolBoundaryAnnotation]
      )
stripSession roleKey source = case source of
  GrammarV1SessionReference _ -> Just (source, [])
  GrammarV1SessionSend parameter boundary Nothing continuation -> do
    own <- boundaryAnnotation roleKey GrammarV1SendBoundary boundary
    strippedContinuation <- stripLocatedSession roleKey continuation
    pure
      ( GrammarV1SessionSend parameter Nothing Nothing (fst strippedContinuation)
      , own <> snd strippedContinuation
      )
  GrammarV1SessionSend _ _ (Just _) _ -> Nothing
  GrammarV1SessionReceive parameter boundary Nothing continuation -> do
    own <- boundaryAnnotation roleKey GrammarV1ReceiveBoundary boundary
    strippedContinuation <- stripLocatedSession roleKey continuation
    pure
      ( GrammarV1SessionReceive parameter Nothing Nothing (fst strippedContinuation)
      , own <> snd strippedContinuation
      )
  GrammarV1SessionReceive _ _ (Just _) _ -> Nothing
  GrammarV1SessionSelect branches -> do
    (stripped, annotations) <- stripBranches True roleKey branches
    pure (GrammarV1SessionSelect stripped, annotations)
  GrammarV1SessionOffer branches -> do
    (stripped, annotations) <- stripBranches False roleKey branches
    pure (GrammarV1SessionOffer stripped, annotations)
  GrammarV1SessionEnd _ -> Just (source, [])
  GrammarV1SessionRecursive recursionName body -> do
    (strippedBody, annotations) <- stripLocatedSession roleKey body
    pure (GrammarV1SessionRecursive recursionName strippedBody, annotations)
  GrammarV1SessionContinue _ -> Just (source, [])

stripLocatedSession
  :: ProtocolRoleKey
  -> Located GrammarV1SessionExpression
  -> Maybe
      ( Located GrammarV1SessionExpression
      , [GrammarV1ProtocolBoundaryAnnotation]
      )
stripLocatedSession roleKey (Located spanValue source) = do
  (stripped, annotations) <- stripSession roleKey source
  pure (Located spanValue stripped, annotations)

stripBranches
  :: Bool
  -> ProtocolRoleKey
  -> [Located GrammarV1SessionBranch]
  -> Maybe
      ( [Located GrammarV1SessionBranch]
      , [GrammarV1ProtocolBoundaryAnnotation]
      )
stripBranches _ _ [] = Just ([], [])
stripBranches selecting roleKey (Located branchSpan branch : rest)
  | grammarV1SessionBranchGuard branch /= Nothing = Nothing
  | otherwise = do
      let label = locatedValue (grammarV1SessionBranchLabel branch)
          site
            | selecting = GrammarV1SelectBranchBoundary label
            | otherwise = GrammarV1OfferBranchBoundary label
      own <- boundaryAnnotation roleKey site (grammarV1SessionBranchBoundary branch)
      (continuation, continuationAnnotations) <- stripLocatedSession
        roleKey
        (grammarV1SessionBranchContinuation branch)
      (strippedRest, restAnnotations) <- stripBranches selecting roleKey rest
      let strippedBranch = branch
            { grammarV1SessionBranchBoundary = Nothing
            , grammarV1SessionBranchGuard = Nothing
            , grammarV1SessionBranchContinuation = continuation
            }
      pure
        ( Located branchSpan strippedBranch : strippedRest
        , own <> continuationAnnotations <> restAnnotations
        )

boundaryAnnotation
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBoundarySite
  -> Maybe (Located GrammarV1StaticReference)
  -> Maybe [GrammarV1ProtocolBoundaryAnnotation]
boundaryAnnotation _ _ Nothing = Just []
boundaryAnnotation roleKey site (Just sourceReference@(Located _ reference)) = do
  actual <- grammarV1BareStaticReferenceActual
    (GrammarV1StaticReferenceArgument reference)
  pure
    [ GrammarV1ProtocolBoundaryAnnotation
        { protocolBoundaryRole = roleKey
        , protocolBoundarySite = site
        , protocolBoundarySourceReference = sourceReference
        , protocolBoundaryStaticReference = actual
        }
    ]
