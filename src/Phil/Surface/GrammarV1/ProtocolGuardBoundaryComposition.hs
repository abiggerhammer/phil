module Phil.Surface.GrammarV1.ProtocolGuardBoundaryComposition
  ( GrammarV1CheckedGuardedProtocolBoundaries (..)
  , GrammarV1ClosedGuardBoundarySurface (..)
  , GrammarV1GuardBoundaryError (..)
  , grammarV1CheckedGuardBoundarySurface
  ) where

import Phil.Core.Protocol (ProtocolRoleKey)
import Phil.Core.Protocol.Family (ProtocolSessionTemplate)
import Phil.Core.Static (StaticContext)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.GrammarV1.ProtocolBoundaryAnnotations
  ( GrammarV1CheckedResolvedProtocolBoundaryAnnotation
  , GrammarV1CheckedSpecializedProtocolBoundaryAnnotation
  , GrammarV1ClosedResolvedProtocolBoundarySurface (..)
  , GrammarV1ClosedSpecializedProtocolBoundarySurface (..)
  , GrammarV1ProtocolBoundaryResolutionError
  , GrammarV1ProtocolSpecializedBoundaryError
  , GrammarV1ResolvedProtocolBoundaryReference
  , GrammarV1ResolvedSpecializedProtocolBoundary
  , grammarV1CheckedResolvedProtocolBoundarySurface
  , grammarV1CheckedSpecializedProtocolBoundarySurface
  )
import Phil.Surface.GrammarV1.ProtocolBoundaryComposition
  ( GrammarV1CheckedMixedProtocolBoundaryAnnotation
  , GrammarV1ClosedMixedProtocolBoundarySurface (..)
  , GrammarV1MixedProtocolBoundaryError
  , grammarV1CheckedMixedProtocolBoundarySurface
  )
import Phil.Surface.GrammarV1.ProtocolGuardAnnotations
  ( GrammarV1CheckedProtocolGuardAnnotation
  , GrammarV1ClosedProtocolGuardSurface (..)
  , GrammarV1ProtocolGuardError
  , grammarV1CheckedClosedProtocolGuardSurface
  )
import Phil.Surface.Syntax (Located (..))

-- | The exact already-checked boundary dimension of a guarded protocol. The
-- constructors preserve which existing boundary authority checked the source;
-- this composition layer never reinterprets one static-reference shape as
-- another or invents a new boundary-resolution relation.
data GrammarV1CheckedGuardedProtocolBoundaries
  = GrammarV1CheckedGuardedBareProtocolBoundaries
      [GrammarV1CheckedResolvedProtocolBoundaryAnnotation]
  | GrammarV1CheckedGuardedSpecializedProtocolBoundaries
      [GrammarV1CheckedSpecializedProtocolBoundaryAnnotation]
  | GrammarV1CheckedGuardedMixedProtocolBoundaries
      [GrammarV1CheckedMixedProtocolBoundaryAnnotation]
  deriving (Eq, Show)

-- | One closed protocol whose binder-free guard propositions and boundary
-- references have both reached their existing competent semantic routes.
data GrammarV1ClosedGuardBoundarySurface = GrammarV1ClosedGuardBoundarySurface
  { checkedGuardBoundaryRoleTemplates
      :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
         , (ProtocolRoleKey, ProtocolSessionTemplate)
         )
  , checkedGuardBoundaryGuards :: [GrammarV1CheckedProtocolGuardAnnotation]
  , checkedGuardBoundaryBoundaries :: GrammarV1CheckedGuardedProtocolBoundaries
  }
  deriving (Eq, Show)

data GrammarV1GuardBoundaryError
  = GrammarV1GuardBoundaryGuardError GrammarV1ProtocolGuardError
  | GrammarV1GuardBoundaryBareError GrammarV1ProtocolBoundaryResolutionError
  | GrammarV1GuardBoundarySpecializedError GrammarV1ProtocolSpecializedBoundaryError
  | GrammarV1GuardBoundaryMixedError GrammarV1MixedProtocolBoundaryError
  | GrammarV1GuardBoundaryUnexpectedBareEvidence Int
  | GrammarV1GuardBoundaryUnexpectedSpecializedEvidence Int
  | GrammarV1GuardBoundaryTemplateMismatch
  deriving (Eq, Show)

-- | Compose context-free protocol guards with every already-supported protocol
-- boundary-reference shape without weakening either checker.
--
-- The source is projected into two structural views. The guard view removes only
-- boundary annotations and retains every guard unchanged. The boundary view
-- removes only guards and retains every boundary reference unchanged. Existing
-- guard focusing and bare/specialized/mixed boundary checkers then run on those
-- views. Their checked role templates must agree exactly before the annotation
-- dimensions are recombined.
--
-- This route is competent only when the source contains at least one guard and at
-- least one boundary annotation. A protocol with guards only or boundaries only
-- remains owned by the existing sibling route. Guard propositions are still
-- checked under the empty term scope used by the existing context-free guard
-- checker, so any guard that requires a live message or branch-payload binder
-- remains outside competence for SURF-009. Generic/requirement-bearing protocols,
-- richer payload competence, boundary qualification, representation,
-- codec/transport semantics, peer compatibility, assurance evidence, authority,
-- runtime boundary evidence, and source-binder identity are not introduced here.
grammarV1CheckedGuardBoundarySurface
  :: StaticContext
  -> [GrammarV1ResolvedProtocolBoundaryReference]
  -> [GrammarV1ResolvedSpecializedProtocolBoundary]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1GuardBoundaryError
        GrammarV1ClosedGuardBoundarySurface)
grammarV1CheckedGuardBoundarySurface
    staticContext bareEvidence specializedEvidence source = do
  let (guardRoles, boundaryRoles, summary) =
        partitionRoles (grammarV1ProtocolRoles source)
  if not (summaryHasGuard summary) || boundaryShape summary == NoBoundaries
    then Nothing
    else do
      guardResult <- grammarV1CheckedClosedProtocolGuardSurface
        staticContext
        source { grammarV1ProtocolRoles = guardRoles }
      boundaryResult <- checkBoundaries
        (boundaryShape summary)
        bareEvidence
        specializedEvidence
        source { grammarV1ProtocolRoles = boundaryRoles }
      pure $ do
        guardSurface <- mapLeft GrammarV1GuardBoundaryGuardError guardResult
        boundaryChecked <- boundaryResult
        let guardTemplates = checkedProtocolGuardRoleTemplates guardSurface
            boundaryTemplates = boundaryCheckTemplates boundaryChecked
        if guardTemplates /= boundaryTemplates
          then Left GrammarV1GuardBoundaryTemplateMismatch
          else Right GrammarV1ClosedGuardBoundarySurface
            { checkedGuardBoundaryRoleTemplates = guardTemplates
            , checkedGuardBoundaryGuards =
                checkedProtocolGuardAnnotations guardSurface
            , checkedGuardBoundaryBoundaries =
                boundaryCheckAnnotations boundaryChecked
            }

data BoundaryShape
  = NoBoundaries
  | BareBoundariesOnly
  | SpecializedBoundariesOnly
  | MixedBoundaries
  deriving (Eq, Show)

data ViewSummary = ViewSummary
  { summaryHasGuard :: Bool
  , summaryHasBareBoundary :: Bool
  , summaryHasSpecializedBoundary :: Bool
  }
  deriving (Eq, Show)

emptySummary :: ViewSummary
emptySummary = ViewSummary False False False

combineSummary :: ViewSummary -> ViewSummary -> ViewSummary
combineSummary left right = ViewSummary
  { summaryHasGuard = summaryHasGuard left || summaryHasGuard right
  , summaryHasBareBoundary =
      summaryHasBareBoundary left || summaryHasBareBoundary right
  , summaryHasSpecializedBoundary =
      summaryHasSpecializedBoundary left || summaryHasSpecializedBoundary right
  }

boundaryShape :: ViewSummary -> BoundaryShape
boundaryShape summary = case
    (summaryHasBareBoundary summary, summaryHasSpecializedBoundary summary) of
  (False, False) -> NoBoundaries
  (True, False) -> BareBoundariesOnly
  (False, True) -> SpecializedBoundariesOnly
  (True, True) -> MixedBoundaries

data BoundaryCheck = BoundaryCheck
  { boundaryCheckTemplates
      :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
         , (ProtocolRoleKey, ProtocolSessionTemplate)
         )
  , boundaryCheckAnnotations :: GrammarV1CheckedGuardedProtocolBoundaries
  }

checkBoundaries
  :: BoundaryShape
  -> [GrammarV1ResolvedProtocolBoundaryReference]
  -> [GrammarV1ResolvedSpecializedProtocolBoundary]
  -> GrammarV1ProtocolDecl
  -> Maybe (Either GrammarV1GuardBoundaryError BoundaryCheck)
checkBoundaries shape bareEvidence specializedEvidence source = case shape of
  NoBoundaries -> Nothing
  BareBoundariesOnly
    | not (null specializedEvidence) -> Just
        (Left
          (GrammarV1GuardBoundaryUnexpectedSpecializedEvidence
            (length specializedEvidence)))
    | otherwise -> do
        checked <- grammarV1CheckedResolvedProtocolBoundarySurface bareEvidence source
        pure $ do
          surface <- mapLeft GrammarV1GuardBoundaryBareError checked
          Right BoundaryCheck
            { boundaryCheckTemplates =
                checkedResolvedProtocolBoundaryRoleTemplates surface
            , boundaryCheckAnnotations =
                GrammarV1CheckedGuardedBareProtocolBoundaries
                  (checkedResolvedProtocolBoundaryAnnotations surface)
            }
  SpecializedBoundariesOnly
    | not (null bareEvidence) -> Just
        (Left
          (GrammarV1GuardBoundaryUnexpectedBareEvidence (length bareEvidence)))
    | otherwise -> do
        checked <- grammarV1CheckedSpecializedProtocolBoundarySurface
          specializedEvidence
          source
        pure $ do
          surface <- mapLeft GrammarV1GuardBoundarySpecializedError checked
          Right BoundaryCheck
            { boundaryCheckTemplates =
                checkedSpecializedProtocolBoundaryRoleTemplates surface
            , boundaryCheckAnnotations =
                GrammarV1CheckedGuardedSpecializedProtocolBoundaries
                  (checkedSpecializedProtocolBoundaryAnnotations surface)
            }
  MixedBoundaries -> do
    checked <- grammarV1CheckedMixedProtocolBoundarySurface
      bareEvidence
      specializedEvidence
      source
    pure $ do
      surface <- mapLeft GrammarV1GuardBoundaryMixedError checked
      Right BoundaryCheck
        { boundaryCheckTemplates = checkedMixedProtocolBoundaryRoleTemplates surface
        , boundaryCheckAnnotations =
            GrammarV1CheckedGuardedMixedProtocolBoundaries
              (checkedMixedProtocolBoundaryAnnotations surface)
        }

partitionRoles
  :: [Located GrammarV1RoleSessionDecl]
  -> ( [Located GrammarV1RoleSessionDecl]
     , [Located GrammarV1RoleSessionDecl]
     , ViewSummary
     )
partitionRoles [] = ([], [], emptySummary)
partitionRoles (Located roleSpan role : rest) =
  let Located sessionSpan session = grammarV1RoleSessionExpression role
      (guardSession, boundarySession, ownSummary) = partitionSession session
      (guardRest, boundaryRest, restSummary) = partitionRoles rest
      guardRole = role
        { grammarV1RoleSessionExpression = Located sessionSpan guardSession }
      boundaryRole = role
        { grammarV1RoleSessionExpression = Located sessionSpan boundarySession }
  in ( Located roleSpan guardRole : guardRest
     , Located roleSpan boundaryRole : boundaryRest
     , combineSummary ownSummary restSummary
     )

partitionSession
  :: GrammarV1SessionExpression
  -> (GrammarV1SessionExpression, GrammarV1SessionExpression, ViewSummary)
partitionSession source = case source of
  GrammarV1SessionReference _ -> (source, source, emptySummary)
  GrammarV1SessionSend parameter boundary guard continuation ->
    let (guardContinuation, boundaryContinuation, continuationSummary) =
          partitionLocatedSession continuation
        ownSummary = summaryFor boundary guard
    in ( GrammarV1SessionSend parameter Nothing guard guardContinuation
       , GrammarV1SessionSend parameter boundary Nothing boundaryContinuation
       , combineSummary ownSummary continuationSummary
       )
  GrammarV1SessionReceive parameter boundary guard continuation ->
    let (guardContinuation, boundaryContinuation, continuationSummary) =
          partitionLocatedSession continuation
        ownSummary = summaryFor boundary guard
    in ( GrammarV1SessionReceive parameter Nothing guard guardContinuation
       , GrammarV1SessionReceive parameter boundary Nothing boundaryContinuation
       , combineSummary ownSummary continuationSummary
       )
  GrammarV1SessionSelect branches ->
    let (guardBranches, boundaryBranches, summary) = partitionBranches branches
    in ( GrammarV1SessionSelect guardBranches
       , GrammarV1SessionSelect boundaryBranches
       , summary
       )
  GrammarV1SessionOffer branches ->
    let (guardBranches, boundaryBranches, summary) = partitionBranches branches
    in ( GrammarV1SessionOffer guardBranches
       , GrammarV1SessionOffer boundaryBranches
       , summary
       )
  GrammarV1SessionEnd _ -> (source, source, emptySummary)
  GrammarV1SessionRecursive recursionName body ->
    let (guardBody, boundaryBody, summary) = partitionLocatedSession body
    in ( GrammarV1SessionRecursive recursionName guardBody
       , GrammarV1SessionRecursive recursionName boundaryBody
       , summary
       )
  GrammarV1SessionContinue _ -> (source, source, emptySummary)

partitionLocatedSession
  :: Located GrammarV1SessionExpression
  -> ( Located GrammarV1SessionExpression
     , Located GrammarV1SessionExpression
     , ViewSummary
     )
partitionLocatedSession (Located spanValue source) =
  let (guardView, boundaryView, summary) = partitionSession source
  in ( Located spanValue guardView
     , Located spanValue boundaryView
     , summary
     )

partitionBranches
  :: [Located GrammarV1SessionBranch]
  -> ( [Located GrammarV1SessionBranch]
     , [Located GrammarV1SessionBranch]
     , ViewSummary
     )
partitionBranches [] = ([], [], emptySummary)
partitionBranches (Located branchSpan branch : rest) =
  let (guardContinuation, boundaryContinuation, continuationSummary) =
        partitionLocatedSession (grammarV1SessionBranchContinuation branch)
      ownSummary = summaryFor
        (grammarV1SessionBranchBoundary branch)
        (grammarV1SessionBranchGuard branch)
      (guardRest, boundaryRest, restSummary) = partitionBranches rest
      guardBranch = branch
        { grammarV1SessionBranchBoundary = Nothing
        , grammarV1SessionBranchContinuation = guardContinuation
        }
      boundaryBranch = branch
        { grammarV1SessionBranchGuard = Nothing
        , grammarV1SessionBranchContinuation = boundaryContinuation
        }
  in ( Located branchSpan guardBranch : guardRest
     , Located branchSpan boundaryBranch : boundaryRest
     , combineSummary ownSummary
         (combineSummary continuationSummary restSummary)
     )

summaryFor
  :: Maybe (Located GrammarV1StaticReference)
  -> Maybe a
  -> ViewSummary
summaryFor boundary guard =
  let guardPresent = case guard of
        Nothing -> False
        Just _ -> True
      (barePresent, specializedPresent) = case boundary of
        Nothing -> (False, False)
        Just (Located _ reference)
          | null (grammarV1StaticReferenceArguments reference) -> (True, False)
          | otherwise -> (False, True)
  in ViewSummary guardPresent barePresent specializedPresent

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
