module Phil.Surface.GrammarV1.ProtocolBoundaryComposition
  ( GrammarV1CheckedMixedProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedMixedProtocolBoundarySurface (..)
  , GrammarV1MixedProtocolBoundaryError (..)
  , grammarV1CheckedMixedProtocolBoundarySurface
  ) where

import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family (ProtocolSessionTemplate)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.GrammarV1.ProtocolBoundaryAnnotations
  ( GrammarV1CheckedResolvedProtocolBoundaryAnnotation (..)
  , GrammarV1CheckedSpecializedProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedResolvedProtocolBoundarySurface (..)
  , GrammarV1ClosedSpecializedProtocolBoundarySurface (..)
  , GrammarV1ProtocolBoundaryResolutionError
  , GrammarV1ProtocolBoundarySite (..)
  , GrammarV1ProtocolSpecializedBoundaryError
  , GrammarV1ResolvedProtocolBoundaryReference
  , GrammarV1ResolvedSpecializedProtocolBoundary
  , grammarV1CheckedResolvedProtocolBoundarySurface
  , grammarV1CheckedSpecializedProtocolBoundarySurface
  )
import Phil.Surface.Syntax (Located (..))

-- | One checked boundary occurrence from a protocol that deliberately mixes the
-- two Grammar-v1 static-reference shapes already supported independently by the
-- boundary elaborator. The constructor records which competent resolver checked
-- the occurrence; neither form is reinterpreted as the other.
data GrammarV1CheckedMixedProtocolBoundaryAnnotation
  = GrammarV1CheckedMixedBareProtocolBoundary
      GrammarV1CheckedResolvedProtocolBoundaryAnnotation
  | GrammarV1CheckedMixedSpecializedProtocolBoundary
      GrammarV1CheckedSpecializedProtocolBoundaryAnnotation
  deriving (Eq, Show)

-- | One checked closed protocol plus all mixed bare/specialized boundary
-- annotations reassembled in exact source preorder.
data GrammarV1ClosedMixedProtocolBoundarySurface =
  GrammarV1ClosedMixedProtocolBoundarySurface
    { checkedMixedProtocolBoundaryRoleTemplates
        :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
           , (ProtocolRoleKey, ProtocolSessionTemplate)
           )
    , checkedMixedProtocolBoundaryAnnotations
        :: [GrammarV1CheckedMixedProtocolBoundaryAnnotation]
    }
  deriving (Eq, Show)

data GrammarV1MixedProtocolBoundaryError
  = GrammarV1MixedProtocolBoundaryBareError
      GrammarV1ProtocolBoundaryResolutionError
  | GrammarV1MixedProtocolBoundarySpecializedError
      GrammarV1ProtocolSpecializedBoundaryError
  | GrammarV1MixedProtocolBoundaryTemplateMismatch
  | GrammarV1MixedProtocolBoundaryReassemblyMismatch
  deriving (Eq, Show)

-- | Compose the established bare-reference and specialized-reference boundary
-- routes for the first protocol fragment that contains both forms.
--
-- Each source boundary occurrence is copied into exactly one category-specific
-- protocol view. The other category is removed only from that structural copy.
-- The two existing checked routes then run unchanged, including their exact
-- resolver evidence checks and the underlying closed role/duality checker. The
-- resulting role templates must agree exactly before annotations are reassembled
-- in the original source preorder.
--
-- This function is deliberately competent only when at least one bare and at
-- least one specialized boundary annotation are present. Homogeneous protocols
-- remain owned by the existing sibling routes. Guards, generic/requirement-bearing
-- protocols, richer unsupported payloads, and other existing competence walls are
-- preserved because both category-specific copies retain every non-boundary
-- source construct unchanged. No boundary qualification, representation,
-- codec/transport semantics, authority, peer compatibility, runtime evidence, or
-- binder identity is inferred here.
grammarV1CheckedMixedProtocolBoundarySurface
  :: [GrammarV1ResolvedProtocolBoundaryReference]
  -> [GrammarV1ResolvedSpecializedProtocolBoundary]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1MixedProtocolBoundaryError
        GrammarV1ClosedMixedProtocolBoundarySurface)
grammarV1CheckedMixedProtocolBoundarySurface bareEvidence specializedEvidence source = do
  let (bareRoles, specializedRoles, order) =
        partitionRoles (grammarV1ProtocolRoles source)
  if not (hasBare order && hasSpecialized order)
    then Nothing
    else do
      bareResult <- grammarV1CheckedResolvedProtocolBoundarySurface
        bareEvidence
        source { grammarV1ProtocolRoles = bareRoles }
      specializedResult <- grammarV1CheckedSpecializedProtocolBoundarySurface
        specializedEvidence
        source { grammarV1ProtocolRoles = specializedRoles }
      pure $ do
        bareSurface <- mapLeft GrammarV1MixedProtocolBoundaryBareError bareResult
        specializedSurface <- mapLeft
          GrammarV1MixedProtocolBoundarySpecializedError
          specializedResult
        let bareTemplates = checkedResolvedProtocolBoundaryRoleTemplates bareSurface
            specializedTemplates =
              checkedSpecializedProtocolBoundaryRoleTemplates specializedSurface
        if bareTemplates /= specializedTemplates
          then Left GrammarV1MixedProtocolBoundaryTemplateMismatch
          else do
            annotations <- reassemble
              order
              (checkedResolvedProtocolBoundaryAnnotations bareSurface)
              (checkedSpecializedProtocolBoundaryAnnotations specializedSurface)
            Right GrammarV1ClosedMixedProtocolBoundarySurface
              { checkedMixedProtocolBoundaryRoleTemplates = bareTemplates
              , checkedMixedProtocolBoundaryAnnotations = annotations
              }

data GrammarV1MixedProtocolBoundaryOccurrence
  = GrammarV1MixedBareBoundaryOccurrence
      ProtocolRoleKey
      GrammarV1ProtocolBoundarySite
      (Located GrammarV1StaticReference)
  | GrammarV1MixedSpecializedBoundaryOccurrence
      ProtocolRoleKey
      GrammarV1ProtocolBoundarySite
      (Located GrammarV1StaticReference)
  deriving (Eq, Show)

hasBare :: [GrammarV1MixedProtocolBoundaryOccurrence] -> Bool
hasBare = any isBare
  where
    isBare occurrence = case occurrence of
      GrammarV1MixedBareBoundaryOccurrence _ _ _ -> True
      GrammarV1MixedSpecializedBoundaryOccurrence _ _ _ -> False

hasSpecialized :: [GrammarV1MixedProtocolBoundaryOccurrence] -> Bool
hasSpecialized = any isSpecialized
  where
    isSpecialized occurrence = case occurrence of
      GrammarV1MixedBareBoundaryOccurrence _ _ _ -> False
      GrammarV1MixedSpecializedBoundaryOccurrence _ _ _ -> True

partitionRoles
  :: [Located GrammarV1RoleSessionDecl]
  -> ( [Located GrammarV1RoleSessionDecl]
     , [Located GrammarV1RoleSessionDecl]
     , [GrammarV1MixedProtocolBoundaryOccurrence]
     )
partitionRoles [] = ([], [], [])
partitionRoles (Located roleSpan role : rest) =
  let roleKey = ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
      Located sessionSpan session = grammarV1RoleSessionExpression role
      (bareSession, specializedSession, ownOrder) = partitionSession roleKey session
      (bareRest, specializedRest, restOrder) = partitionRoles rest
      bareRole = role
        { grammarV1RoleSessionExpression = Located sessionSpan bareSession }
      specializedRole = role
        { grammarV1RoleSessionExpression = Located sessionSpan specializedSession }
  in ( Located roleSpan bareRole : bareRest
     , Located roleSpan specializedRole : specializedRest
     , ownOrder <> restOrder
     )

partitionSession
  :: ProtocolRoleKey
  -> GrammarV1SessionExpression
  -> ( GrammarV1SessionExpression
     , GrammarV1SessionExpression
     , [GrammarV1MixedProtocolBoundaryOccurrence]
     )
partitionSession roleKey source = case source of
  GrammarV1SessionReference _ -> (source, source, [])
  GrammarV1SessionSend parameter boundary guard continuation ->
    let (bareBoundary, specializedBoundary, ownOrder) =
          partitionBoundary roleKey GrammarV1SendBoundary boundary
        (bareContinuation, specializedContinuation, continuationOrder) =
          partitionLocatedSession roleKey continuation
    in ( GrammarV1SessionSend parameter bareBoundary guard bareContinuation
       , GrammarV1SessionSend parameter specializedBoundary guard specializedContinuation
       , ownOrder <> continuationOrder
       )
  GrammarV1SessionReceive parameter boundary guard continuation ->
    let (bareBoundary, specializedBoundary, ownOrder) =
          partitionBoundary roleKey GrammarV1ReceiveBoundary boundary
        (bareContinuation, specializedContinuation, continuationOrder) =
          partitionLocatedSession roleKey continuation
    in ( GrammarV1SessionReceive parameter bareBoundary guard bareContinuation
       , GrammarV1SessionReceive parameter specializedBoundary guard specializedContinuation
       , ownOrder <> continuationOrder
       )
  GrammarV1SessionSelect branches ->
    let (bareBranches, specializedBranches, order) =
          partitionBranches True roleKey branches
    in ( GrammarV1SessionSelect bareBranches
       , GrammarV1SessionSelect specializedBranches
       , order
       )
  GrammarV1SessionOffer branches ->
    let (bareBranches, specializedBranches, order) =
          partitionBranches False roleKey branches
    in ( GrammarV1SessionOffer bareBranches
       , GrammarV1SessionOffer specializedBranches
       , order
       )
  GrammarV1SessionEnd _ -> (source, source, [])
  GrammarV1SessionRecursive recursionName body ->
    let (bareBody, specializedBody, order) = partitionLocatedSession roleKey body
    in ( GrammarV1SessionRecursive recursionName bareBody
       , GrammarV1SessionRecursive recursionName specializedBody
       , order
       )
  GrammarV1SessionContinue _ -> (source, source, [])

partitionLocatedSession
  :: ProtocolRoleKey
  -> Located GrammarV1SessionExpression
  -> ( Located GrammarV1SessionExpression
     , Located GrammarV1SessionExpression
     , [GrammarV1MixedProtocolBoundaryOccurrence]
     )
partitionLocatedSession roleKey (Located spanValue source) =
  let (bare, specialized, order) = partitionSession roleKey source
  in (Located spanValue bare, Located spanValue specialized, order)

partitionBranches
  :: Bool
  -> ProtocolRoleKey
  -> [Located GrammarV1SessionBranch]
  -> ( [Located GrammarV1SessionBranch]
     , [Located GrammarV1SessionBranch]
     , [GrammarV1MixedProtocolBoundaryOccurrence]
     )
partitionBranches _ _ [] = ([], [], [])
partitionBranches selecting roleKey (Located branchSpan branch : rest) =
  let label = locatedValue (grammarV1SessionBranchLabel branch)
      site
        | selecting = GrammarV1SelectBranchBoundary label
        | otherwise = GrammarV1OfferBranchBoundary label
      (bareBoundary, specializedBoundary, ownOrder) =
        partitionBoundary roleKey site (grammarV1SessionBranchBoundary branch)
      (bareContinuation, specializedContinuation, continuationOrder) =
        partitionLocatedSession roleKey (grammarV1SessionBranchContinuation branch)
      (bareRest, specializedRest, restOrder) =
        partitionBranches selecting roleKey rest
      bareBranch = branch
        { grammarV1SessionBranchBoundary = bareBoundary
        , grammarV1SessionBranchContinuation = bareContinuation
        }
      specializedBranch = branch
        { grammarV1SessionBranchBoundary = specializedBoundary
        , grammarV1SessionBranchContinuation = specializedContinuation
        }
  in ( Located branchSpan bareBranch : bareRest
     , Located branchSpan specializedBranch : specializedRest
     , ownOrder <> continuationOrder <> restOrder
     )

partitionBoundary
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBoundarySite
  -> Maybe (Located GrammarV1StaticReference)
  -> ( Maybe (Located GrammarV1StaticReference)
     , Maybe (Located GrammarV1StaticReference)
     , [GrammarV1MixedProtocolBoundaryOccurrence]
     )
partitionBoundary _ _ Nothing = (Nothing, Nothing, [])
partitionBoundary roleKey site (Just sourceReference@(Located _ reference))
  | null (grammarV1StaticReferenceArguments reference) =
      ( Just sourceReference
      , Nothing
      , [GrammarV1MixedBareBoundaryOccurrence roleKey site sourceReference]
      )
  | otherwise =
      ( Nothing
      , Just sourceReference
      , [GrammarV1MixedSpecializedBoundaryOccurrence roleKey site sourceReference]
      )

reassemble
  :: [GrammarV1MixedProtocolBoundaryOccurrence]
  -> [GrammarV1CheckedResolvedProtocolBoundaryAnnotation]
  -> [GrammarV1CheckedSpecializedProtocolBoundaryAnnotation]
  -> Either
      GrammarV1MixedProtocolBoundaryError
      [GrammarV1CheckedMixedProtocolBoundaryAnnotation]
reassemble [] [] [] = Right []
reassemble [] _ _ = Left GrammarV1MixedProtocolBoundaryReassemblyMismatch
reassemble (occurrence : rest) bare specialized = case occurrence of
  GrammarV1MixedBareBoundaryOccurrence roleKey site sourceReference ->
    case bare of
      annotation : bareRest
        | checkedResolvedProtocolBoundaryRole annotation == roleKey
        , checkedResolvedProtocolBoundarySite annotation == site
        , checkedResolvedProtocolBoundarySourceReference annotation == sourceReference ->
            (GrammarV1CheckedMixedBareProtocolBoundary annotation :)
              <$> reassemble rest bareRest specialized
      _ -> Left GrammarV1MixedProtocolBoundaryReassemblyMismatch
  GrammarV1MixedSpecializedBoundaryOccurrence roleKey site sourceReference ->
    case specialized of
      annotation : specializedRest
        | checkedSpecializedProtocolBoundaryRole annotation == roleKey
        , checkedSpecializedProtocolBoundarySite annotation == site
        , checkedSpecializedProtocolBoundarySourceReference annotation == sourceReference ->
            (GrammarV1CheckedMixedSpecializedProtocolBoundary annotation :)
              <$> reassemble rest bare specializedRest
      _ -> Left GrammarV1MixedProtocolBoundaryReassemblyMismatch

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
