module Phil.Surface.GrammarV1.ProtocolBoundaryAnnotations
  ( GrammarV1ProtocolBoundarySite (..)
  , GrammarV1ProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedProtocolBoundarySurface (..)
  , grammarV1CheckedClosedProtocolBoundarySurface
  , GrammarV1ResolvedSpecializedProtocolBoundary (..)
  , GrammarV1CheckedSpecializedProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedSpecializedProtocolBoundarySurface (..)
  , GrammarV1ProtocolSpecializedBoundaryError (..)
  , grammarV1CheckedSpecializedProtocolBoundarySurface
  , GrammarV1ResolvedProtocolBoundaryReference (..)
  , GrammarV1CheckedResolvedProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedResolvedProtocolBoundarySurface (..)
  , GrammarV1ProtocolBoundaryResolutionError (..)
  , grammarV1CheckedResolvedProtocolBoundarySurface
  ) where

import qualified Data.Text as Text
import Data.Text (Text)
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  , GenericStaticParameter
  , GenericStaticReferenceCandidate (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family (ProtocolSessionTemplate)
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  , SemanticForm
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError
  , grammarV1CheckedClosedProtocolRoleTemplates
  )
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1CheckedSpecializedStaticReference
  , GrammarV1ResolvedDirectStaticArgument
  , GrammarV1SpecializedStaticReferenceError
  , grammarV1CheckedSpecializedStaticReference
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

-- | Resolver evidence for one specialized protocol-boundary occurrence. The
-- source role/site/reference triple is repeated deliberately so positional
-- semantic evidence cannot drift onto another syntactically similar occurrence.
-- Target category, stable declaration/interface identity, generic parameter
-- schema, and static-argument evidence all come from competent resolution layers.
data GrammarV1ResolvedSpecializedProtocolBoundary =
  GrammarV1ResolvedSpecializedProtocolBoundary
    { resolvedSpecializedProtocolBoundaryRole :: ProtocolRoleKey
    , resolvedSpecializedProtocolBoundarySite :: GrammarV1ProtocolBoundarySite
    , resolvedSpecializedProtocolBoundarySourceReference
        :: Located GrammarV1StaticReference
    , resolvedSpecializedProtocolBoundaryTargetCandidate
        :: GenericStaticReferenceCandidate
    , resolvedSpecializedProtocolBoundaryDeclarationKey :: DeclarationKey
    , resolvedSpecializedProtocolBoundaryInterfaceRevision :: InterfaceRevision
    , resolvedSpecializedProtocolBoundaryParameters :: [GenericStaticParameter]
    , resolvedSpecializedProtocolBoundaryDirectArguments
        :: [GrammarV1ResolvedDirectStaticArgument]
    , resolvedSpecializedProtocolBoundaryArgumentReferences
        :: [GenericStaticReferenceCandidate]
    }
  deriving (Eq, Show)

-- | One specialized `using` occurrence after the generic static-application
-- checker has established exact target-parameter/argument correspondence. The
-- target semantic form is retained separately for the later competent boundary
-- resolver; it is not interpreted here as representation or runtime evidence.
data GrammarV1CheckedSpecializedProtocolBoundaryAnnotation =
  GrammarV1CheckedSpecializedProtocolBoundaryAnnotation
    { checkedSpecializedProtocolBoundaryRole :: ProtocolRoleKey
    , checkedSpecializedProtocolBoundarySite :: GrammarV1ProtocolBoundarySite
    , checkedSpecializedProtocolBoundarySourceReference
        :: Located GrammarV1StaticReference
    , checkedSpecializedProtocolBoundaryTargetSemanticForm :: SemanticForm
    , checkedSpecializedProtocolBoundaryReference
        :: GrammarV1CheckedSpecializedStaticReference
    }
  deriving (Eq, Show)

-- | Checked closed role templates plus exact source-ordered checked specialized
-- boundary applications removed before the established protocol-role checker ran.
data GrammarV1ClosedSpecializedProtocolBoundarySurface =
  GrammarV1ClosedSpecializedProtocolBoundarySurface
    { checkedSpecializedProtocolBoundaryRoleTemplates
        :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
           , (ProtocolRoleKey, ProtocolSessionTemplate)
           )
    , checkedSpecializedProtocolBoundaryAnnotations
        :: [GrammarV1CheckedSpecializedProtocolBoundaryAnnotation]
    }
  deriving (Eq, Show)

data GrammarV1ProtocolSpecializedBoundaryError
  = GrammarV1SpecializedProtocolBoundaryRoleError GrammarV1ProtocolRoleError
  | GrammarV1SpecializedProtocolBoundaryEvidenceCountMismatch Int Int
  | GrammarV1SpecializedProtocolBoundaryRoleMismatch
      Int ProtocolRoleKey ProtocolRoleKey
  | GrammarV1SpecializedProtocolBoundarySiteMismatch
      Int GrammarV1ProtocolBoundarySite GrammarV1ProtocolBoundarySite
  | GrammarV1SpecializedProtocolBoundarySourceReferenceMismatch
      Int
      (Located GrammarV1StaticReference)
      (Located GrammarV1StaticReference)
  | GrammarV1SpecializedProtocolBoundaryTargetNameMismatch Int Text Text
  | GrammarV1SpecializedProtocolBoundaryTargetKindMismatch
      Int Text GenericStaticKind
  | GrammarV1SpecializedProtocolBoundaryStaticReferenceError
      Int GrammarV1SpecializedStaticReferenceError
  deriving (Eq, Show)

-- | Check specialized Grammar-v1 protocol-boundary annotations without treating
-- source spelling as boundary-contract resolution authority.
--
-- This is the specialized sibling of
-- 'grammarV1CheckedClosedProtocolBoundarySurface'. A protocol must contain at
-- least one specialized boundary reference, and every explicit boundary reference
-- in the admitted fragment must be specialized. Each source occurrence is removed
-- only from a structural copy that is delegated unchanged to the existing closed
-- protocol-role checker. Thus payload typing, recursion validity, duplicate-role
-- rejection and alpha-aware duality remain authoritative and cannot be bypassed by
-- boundary specialization.
--
-- Evidence is consumed in exact source preorder and must match the exact role,
-- structural site and Located source reference. The supplied target candidate must
-- match source target spelling and carry GenericBoundaryContractKind. Static
-- argument kind checking and GenericApplicationIdentity construction delegate
-- unchanged to 'grammarV1CheckedSpecializedStaticReference'.
--
-- Guards remain non-competence because their propositions may depend on live
-- message/payload binders. Bare boundary references remain owned by the sibling
-- unresolved route. Generic/requirement-bearing protocols and other unsupported
-- session forms still fail through the delegated closed checker. This bridge does
-- not establish boundary-contract qualification, representation, codec/transport
-- semantics, peer compatibility, authority, or runtime boundary evidence, and it
-- does not resolve source binders.
grammarV1CheckedSpecializedProtocolBoundarySurface
  :: [GrammarV1ResolvedSpecializedProtocolBoundary]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolSpecializedBoundaryError
        GrammarV1ClosedSpecializedProtocolBoundarySurface)
grammarV1CheckedSpecializedProtocolBoundarySurface evidence source = do
  (strippedRoles, occurrences) <-
    stripSpecializedRoles (grammarV1ProtocolRoles source)
  if null occurrences
    then Nothing
    else do
      let stripped = source { grammarV1ProtocolRoles = strippedRoles }
      checkedTemplates <- grammarV1CheckedClosedProtocolRoleTemplates stripped
      case checkedTemplates of
        Left err -> pure
          (Left (GrammarV1SpecializedProtocolBoundaryRoleError err))
        Right templates ->
          if length evidence /= length occurrences
            then pure
              (Left
                (GrammarV1SpecializedProtocolBoundaryEvidenceCountMismatch
                  (length occurrences)
                  (length evidence)))
            else do
              checked <- mapM
                (\(index, occurrence, resolved) ->
                  checkSpecializedBoundary index occurrence resolved)
                (zip3 [0 ..] occurrences evidence)
              pure $ do
                annotations <- sequence checked
                Right GrammarV1ClosedSpecializedProtocolBoundarySurface
                  { checkedSpecializedProtocolBoundaryRoleTemplates = templates
                  , checkedSpecializedProtocolBoundaryAnnotations = annotations
                  }

data GrammarV1SpecializedProtocolBoundaryOccurrence =
  GrammarV1SpecializedProtocolBoundaryOccurrence
    { specializedProtocolBoundaryOccurrenceRole :: ProtocolRoleKey
    , specializedProtocolBoundaryOccurrenceSite :: GrammarV1ProtocolBoundarySite
    , specializedProtocolBoundaryOccurrenceSourceReference
        :: Located GrammarV1StaticReference
    }
  deriving (Eq, Show)

stripSpecializedRoles
  :: [Located GrammarV1RoleSessionDecl]
  -> Maybe
      ( [Located GrammarV1RoleSessionDecl]
      , [GrammarV1SpecializedProtocolBoundaryOccurrence]
      )
stripSpecializedRoles [] = Just ([], [])
stripSpecializedRoles (Located roleSpan role : rest) = do
  let roleKey = ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
      Located sessionSpan session = grammarV1RoleSessionExpression role
  (strippedSession, ownOccurrences) <-
    stripSpecializedSession roleKey session
  (strippedRest, restOccurrences) <- stripSpecializedRoles rest
  let strippedRole = role
        { grammarV1RoleSessionExpression = Located sessionSpan strippedSession }
  pure
    ( Located roleSpan strippedRole : strippedRest
    , ownOccurrences <> restOccurrences
    )

stripSpecializedSession
  :: ProtocolRoleKey
  -> GrammarV1SessionExpression
  -> Maybe
      ( GrammarV1SessionExpression
      , [GrammarV1SpecializedProtocolBoundaryOccurrence]
      )
stripSpecializedSession roleKey source = case source of
  GrammarV1SessionReference _ -> Just (source, [])
  GrammarV1SessionSend parameter boundary Nothing continuation -> do
    own <- specializedBoundaryOccurrence roleKey GrammarV1SendBoundary boundary
    strippedContinuation <- stripSpecializedLocatedSession roleKey continuation
    pure
      ( GrammarV1SessionSend parameter Nothing Nothing (fst strippedContinuation)
      , own <> snd strippedContinuation
      )
  GrammarV1SessionSend _ _ (Just _) _ -> Nothing
  GrammarV1SessionReceive parameter boundary Nothing continuation -> do
    own <- specializedBoundaryOccurrence roleKey GrammarV1ReceiveBoundary boundary
    strippedContinuation <- stripSpecializedLocatedSession roleKey continuation
    pure
      ( GrammarV1SessionReceive parameter Nothing Nothing (fst strippedContinuation)
      , own <> snd strippedContinuation
      )
  GrammarV1SessionReceive _ _ (Just _) _ -> Nothing
  GrammarV1SessionSelect branches -> do
    (stripped, occurrences) <-
      stripSpecializedBranches True roleKey branches
    pure (GrammarV1SessionSelect stripped, occurrences)
  GrammarV1SessionOffer branches -> do
    (stripped, occurrences) <-
      stripSpecializedBranches False roleKey branches
    pure (GrammarV1SessionOffer stripped, occurrences)
  GrammarV1SessionEnd _ -> Just (source, [])
  GrammarV1SessionRecursive recursionName body -> do
    (strippedBody, occurrences) <-
      stripSpecializedLocatedSession roleKey body
    pure (GrammarV1SessionRecursive recursionName strippedBody, occurrences)
  GrammarV1SessionContinue _ -> Just (source, [])

stripSpecializedLocatedSession
  :: ProtocolRoleKey
  -> Located GrammarV1SessionExpression
  -> Maybe
      ( Located GrammarV1SessionExpression
      , [GrammarV1SpecializedProtocolBoundaryOccurrence]
      )
stripSpecializedLocatedSession roleKey (Located spanValue source) = do
  (stripped, occurrences) <- stripSpecializedSession roleKey source
  pure (Located spanValue stripped, occurrences)

stripSpecializedBranches
  :: Bool
  -> ProtocolRoleKey
  -> [Located GrammarV1SessionBranch]
  -> Maybe
      ( [Located GrammarV1SessionBranch]
      , [GrammarV1SpecializedProtocolBoundaryOccurrence]
      )
stripSpecializedBranches _ _ [] = Just ([], [])
stripSpecializedBranches selecting roleKey (Located branchSpan branch : rest)
  | grammarV1SessionBranchGuard branch /= Nothing = Nothing
  | otherwise = do
      let label = locatedValue (grammarV1SessionBranchLabel branch)
          site
            | selecting = GrammarV1SelectBranchBoundary label
            | otherwise = GrammarV1OfferBranchBoundary label
      own <- specializedBoundaryOccurrence
        roleKey site (grammarV1SessionBranchBoundary branch)
      (continuation, continuationOccurrences) <-
        stripSpecializedLocatedSession
          roleKey
          (grammarV1SessionBranchContinuation branch)
      (strippedRest, restOccurrences) <-
        stripSpecializedBranches selecting roleKey rest
      let strippedBranch = branch
            { grammarV1SessionBranchBoundary = Nothing
            , grammarV1SessionBranchGuard = Nothing
            , grammarV1SessionBranchContinuation = continuation
            }
      pure
        ( Located branchSpan strippedBranch : strippedRest
        , own <> continuationOccurrences <> restOccurrences
        )

specializedBoundaryOccurrence
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBoundarySite
  -> Maybe (Located GrammarV1StaticReference)
  -> Maybe [GrammarV1SpecializedProtocolBoundaryOccurrence]
specializedBoundaryOccurrence _ _ Nothing = Just []
specializedBoundaryOccurrence roleKey site (Just sourceReference@(Located _ reference))
  | null (grammarV1StaticReferenceArguments reference) = Nothing
  | otherwise = Just
      [ GrammarV1SpecializedProtocolBoundaryOccurrence
          { specializedProtocolBoundaryOccurrenceRole = roleKey
          , specializedProtocolBoundaryOccurrenceSite = site
          , specializedProtocolBoundaryOccurrenceSourceReference = sourceReference
          }
      ]

checkSpecializedBoundary
  :: Int
  -> GrammarV1SpecializedProtocolBoundaryOccurrence
  -> GrammarV1ResolvedSpecializedProtocolBoundary
  -> Maybe
      (Either
        GrammarV1ProtocolSpecializedBoundaryError
        GrammarV1CheckedSpecializedProtocolBoundaryAnnotation)
checkSpecializedBoundary index occurrence resolved
  | resolvedSpecializedProtocolBoundaryRole resolved /= sourceRole =
      pure
        (Left
          (GrammarV1SpecializedProtocolBoundaryRoleMismatch
            index
            sourceRole
            (resolvedSpecializedProtocolBoundaryRole resolved)))
  | resolvedSpecializedProtocolBoundarySite resolved /= sourceSite =
      pure
        (Left
          (GrammarV1SpecializedProtocolBoundarySiteMismatch
            index
            sourceSite
            (resolvedSpecializedProtocolBoundarySite resolved)))
  | resolvedSpecializedProtocolBoundarySourceReference resolved /= sourceReference =
      pure
        (Left
          (GrammarV1SpecializedProtocolBoundarySourceReferenceMismatch
            index
            sourceReference
            (resolvedSpecializedProtocolBoundarySourceReference resolved)))
  | genericStaticReferenceName target /= sourceName =
      pure
        (Left
          (GrammarV1SpecializedProtocolBoundaryTargetNameMismatch
            index
            sourceName
            (genericStaticReferenceName target)))
  | genericStaticReferenceKind target /= GenericBoundaryContractKind =
      pure
        (Left
          (GrammarV1SpecializedProtocolBoundaryTargetKindMismatch
            index
            sourceName
            (genericStaticReferenceKind target)))
  | otherwise = do
      checked <- grammarV1CheckedSpecializedStaticReference
        (resolvedSpecializedProtocolBoundaryDeclarationKey resolved)
        (resolvedSpecializedProtocolBoundaryInterfaceRevision resolved)
        (resolvedSpecializedProtocolBoundaryParameters resolved)
        (resolvedSpecializedProtocolBoundaryDirectArguments resolved)
        (resolvedSpecializedProtocolBoundaryArgumentReferences resolved)
        (locatedValue sourceReference)
      pure $ case checked of
        Left err -> Left
          (GrammarV1SpecializedProtocolBoundaryStaticReferenceError index err)
        Right result -> Right GrammarV1CheckedSpecializedProtocolBoundaryAnnotation
          { checkedSpecializedProtocolBoundaryRole = sourceRole
          , checkedSpecializedProtocolBoundarySite = sourceSite
          , checkedSpecializedProtocolBoundarySourceReference = sourceReference
          , checkedSpecializedProtocolBoundaryTargetSemanticForm =
              genericStaticReferenceSemanticForm target
          , checkedSpecializedProtocolBoundaryReference = result
          }
  where
    sourceRole = specializedProtocolBoundaryOccurrenceRole occurrence
    sourceSite = specializedProtocolBoundaryOccurrenceSite occurrence
    sourceReference = specializedProtocolBoundaryOccurrenceSourceReference occurrence
    sourceName = qualifiedNameText
      (grammarV1StaticReferenceName (locatedValue sourceReference))
    target = resolvedSpecializedProtocolBoundaryTargetCandidate resolved

qualifiedNameText :: GrammarV1QualifiedName -> Text
qualifiedNameText source =
  Text.intercalate (Text.singleton '.') (grammarV1QualifiedNameParts source)

-- | Exact declaration-resolution evidence for one bare/qualified unspecialized
-- protocol boundary annotation. The complete source annotation is repeated so
-- resolution cannot drift between equal-spelled occurrences at different roles or
-- structural sites. Stable declaration/interface identity and the target
-- candidate come from the competent static resolver rather than source spelling.
data GrammarV1ResolvedProtocolBoundaryReference =
  GrammarV1ResolvedProtocolBoundaryReference
    { resolvedProtocolBoundarySourceAnnotation :: GrammarV1ProtocolBoundaryAnnotation
    , resolvedProtocolBoundaryTargetCandidate :: GenericStaticReferenceCandidate
    , resolvedProtocolBoundaryDeclarationKey :: DeclarationKey
    , resolvedProtocolBoundaryInterfaceRevision :: InterfaceRevision
    }
  deriving (Eq, Show)

-- | A bare protocol boundary after exact static category resolution. Source
-- occurrence identity and the unresolved reference remain visible beside stable
-- declaration/interface identity and the resolver-supplied semantic form.
data GrammarV1CheckedResolvedProtocolBoundaryAnnotation =
  GrammarV1CheckedResolvedProtocolBoundaryAnnotation
    { checkedResolvedProtocolBoundaryRole :: ProtocolRoleKey
    , checkedResolvedProtocolBoundarySite :: GrammarV1ProtocolBoundarySite
    , checkedResolvedProtocolBoundarySourceReference :: Located GrammarV1StaticReference
    , checkedResolvedProtocolBoundaryStaticReference :: GenericStaticActual
    , checkedResolvedProtocolBoundaryDeclarationKey :: DeclarationKey
    , checkedResolvedProtocolBoundaryInterfaceRevision :: InterfaceRevision
    , checkedResolvedProtocolBoundarySemanticForm :: SemanticForm
    }
  deriving (Eq, Show)

data GrammarV1ClosedResolvedProtocolBoundarySurface =
  GrammarV1ClosedResolvedProtocolBoundarySurface
    { checkedResolvedProtocolBoundaryRoleTemplates
        :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
           , (ProtocolRoleKey, ProtocolSessionTemplate)
           )
    , checkedResolvedProtocolBoundaryAnnotations
        :: [GrammarV1CheckedResolvedProtocolBoundaryAnnotation]
    }
  deriving (Eq, Show)

data GrammarV1ProtocolBoundaryResolutionError
  = GrammarV1ResolvedProtocolBoundaryRoleError GrammarV1ProtocolRoleError
  | GrammarV1ResolvedProtocolBoundaryEvidenceCountMismatch Int Int
  | GrammarV1ResolvedProtocolBoundarySourceMismatch
      Int GrammarV1ProtocolBoundaryAnnotation GrammarV1ProtocolBoundaryAnnotation
  | GrammarV1ResolvedProtocolBoundaryUnexpectedStaticActual
      Int GenericStaticActual
  | GrammarV1ResolvedProtocolBoundaryTargetNameMismatch Int Text Text
  | GrammarV1ResolvedProtocolBoundaryTargetKindMismatch
      Int Text GenericStaticKind
  deriving (Eq, Show)

-- | Consume exact resolver evidence for the bare boundary annotations preserved by
-- 'grammarV1CheckedClosedProtocolBoundarySurface'. This bridge does not perform a
-- second parse or rebuild protocol structure: the #648 checked surface remains the
-- source-occurrence and closed-protocol authority, including payload typing,
-- recursion, duplicate-role rejection and alpha-aware duality.
--
-- Every annotation must receive one evidence entry in exact source preorder. The
-- evidence repeats the complete source annotation, the target candidate must keep
-- the same textual reference and carry GenericBoundaryContractKind, and stable
-- DeclarationKey/InterfaceRevision are preserved unchanged. The target semantic
-- form is consumed from the competent resolver rather than synthesized from source
-- spelling.
--
-- This slice does not establish boundary qualification, representation,
-- codec/transport semantics, peer compatibility, authority, runtime evidence, or
-- source-binder scope. Specialized references remain owned by the sibling checked
-- static-application route, while guards and generic/requirement-bearing protocols
-- retain the existing fail-closed competence boundary.
grammarV1CheckedResolvedProtocolBoundarySurface
  :: [GrammarV1ResolvedProtocolBoundaryReference]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolBoundaryResolutionError
        GrammarV1ClosedResolvedProtocolBoundarySurface)
grammarV1CheckedResolvedProtocolBoundarySurface evidence source = do
  checked <- grammarV1CheckedClosedProtocolBoundarySurface source
  case checked of
    Left err -> pure (Left (GrammarV1ResolvedProtocolBoundaryRoleError err))
    Right surface ->
      let annotations = checkedProtocolBoundaryAnnotations surface
      in if null annotations
          then Nothing
          else if length evidence /= length annotations
            then pure
              (Left
                (GrammarV1ResolvedProtocolBoundaryEvidenceCountMismatch
                  (length annotations)
                  (length evidence)))
            else pure $ do
              resolved <- sequence
                [ checkResolvedProtocolBoundary index annotation supplied
                | (index, annotation, supplied) <- zip3 [0 ..] annotations evidence
                ]
              Right GrammarV1ClosedResolvedProtocolBoundarySurface
                { checkedResolvedProtocolBoundaryRoleTemplates =
                    checkedProtocolBoundaryRoleTemplates surface
                , checkedResolvedProtocolBoundaryAnnotations = resolved
                }

checkResolvedProtocolBoundary
  :: Int
  -> GrammarV1ProtocolBoundaryAnnotation
  -> GrammarV1ResolvedProtocolBoundaryReference
  -> Either
      GrammarV1ProtocolBoundaryResolutionError
      GrammarV1CheckedResolvedProtocolBoundaryAnnotation
checkResolvedProtocolBoundary index annotation supplied
  | resolvedProtocolBoundarySourceAnnotation supplied /= annotation =
      Left
        (GrammarV1ResolvedProtocolBoundarySourceMismatch
          index
          annotation
          (resolvedProtocolBoundarySourceAnnotation supplied))
  | otherwise = case protocolBoundaryStaticReference annotation of
      ReferencedGenericStaticActual sourceName
        | genericStaticReferenceName target /= sourceName ->
            Left
              (GrammarV1ResolvedProtocolBoundaryTargetNameMismatch
                index
                sourceName
                (genericStaticReferenceName target))
        | genericStaticReferenceKind target /= GenericBoundaryContractKind ->
            Left
              (GrammarV1ResolvedProtocolBoundaryTargetKindMismatch
                index
                sourceName
                (genericStaticReferenceKind target))
        | otherwise -> Right GrammarV1CheckedResolvedProtocolBoundaryAnnotation
            { checkedResolvedProtocolBoundaryRole = protocolBoundaryRole annotation
            , checkedResolvedProtocolBoundarySite = protocolBoundarySite annotation
            , checkedResolvedProtocolBoundarySourceReference =
                protocolBoundarySourceReference annotation
            , checkedResolvedProtocolBoundaryStaticReference =
                protocolBoundaryStaticReference annotation
            , checkedResolvedProtocolBoundaryDeclarationKey =
                resolvedProtocolBoundaryDeclarationKey supplied
            , checkedResolvedProtocolBoundaryInterfaceRevision =
                resolvedProtocolBoundaryInterfaceRevision supplied
            , checkedResolvedProtocolBoundarySemanticForm =
                genericStaticReferenceSemanticForm target
            }
      other -> Left
        (GrammarV1ResolvedProtocolBoundaryUnexpectedStaticActual index other)
  where
    target = resolvedProtocolBoundaryTargetCandidate supplied
