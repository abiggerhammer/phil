{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification
  ( AssurancePolicyRevision (..)
  , VerificationDisposition (..)
  , ApplicationAssurancePolicy (..)
  , IntrinsicRejection (..)
  , ApplicationVerificationResult (..)
  , VerificationObligationInput (..)
  , VerificationObligationGraph (..)
  , VerificationGraphError (..)
  , buildVerificationObligationGraph
  , verifySurfaceApplication
  ) where

import Control.Monad (foldM)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( AcceptanceRule (..)
  , Digest
  , ObligationRevision (..)
  , RevisionId (..)
  , digestText
  , revisionFromCoreObligation
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId
  )
import Phil.Surface.Check
  ( SurfaceCheckError
  , SurfaceCheckResult
  , SurfaceEnvironment
  , checkSurfaceComponent
  )
import Phil.Surface.Parser
  ( ParseDiagnostic
  , parseSurfaceFile
  )
import Phil.Surface.Syntax (SurfaceFile (..))

-- | Identity-bearing assurance policy input for obligation closure.  VER-001
-- deliberately does not let this policy participate in intrinsic validity.
newtype AssurancePolicyRevision = AssurancePolicyRevision
  { unAssurancePolicyRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Phase-1 closure dispositions from the application-verification contract.
-- Their presence here does not make them available to intrinsically invalid
-- programs: only an intrinsically accepted program can reach the closure stage.
data VerificationDisposition
  = StaticallyDischarged
  | RuntimeBound
  | ExternallyDischarged
  | AssumptionDependent
  | Exported
  | DeploymentExported
  | Unresolved
  deriving (Eq, Ord, Show)

data ApplicationAssurancePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision :: AssurancePolicyRevision
  , applicationAssurancePolicyPermittedDispositions :: Set VerificationDisposition
  }
  deriving (Eq, Show)

-- | Competent intrinsic rejection.  No constructor carries an assurance
-- disposition, residual obligation, or VerificationBundle: rejection is a
-- terminal result of intrinsic checking, not an obligation-closure input.
data IntrinsicRejection
  = IntrinsicParseRejected ParseDiagnostic
  | IntrinsicComponentCardinalityRejected Int
  | IntrinsicSurfaceRejected SurfaceCheckError
  deriving (Eq, Show)

-- | VER-001's application-verification boundary.  VER-002 and later slices
-- enrich the successful side with a canonical obligation graph and then the
-- remaining VerificationBundle fields.  Rejection remains terminal.
data ApplicationVerificationResult
  = IntrinsicRejected IntrinsicRejection
  | ReadyForObligationClosure
      { readyCheckedSurface :: SurfaceCheckResult
      , readyAssurancePolicy :: ApplicationAssurancePolicy
      }
  deriving (Eq, Show)

-- | Exact semantic input supplied by the competent obligation-generating
-- layer.  Presentation details, diagnostics, container traversal, proof-search
-- producer identity, and runtime object identity are deliberately absent.
-- Dependencies name semantic obligations, not mutable positions in a list.
data VerificationObligationInput = VerificationObligationInput
  { verificationInputObligation :: Obligation
  , verificationInputKind :: Text
  , verificationInputRepresentation :: Text
  , verificationInputSubjectIds :: [Text]
  , verificationInputContextIds :: [Text]
  , verificationInputAcceptanceRule :: AcceptanceRule
  , verificationInputDependencies :: Set ObligationId
  }
  deriving (Eq, Ord, Show)

-- | Canonical exact graph used by VER-002.  Nodes are keyed by immutable
-- ObligationRevision identity.  An edge (A,B) means A depends on B.  Sets and
-- maps make container/traversal order nonsemantic; graphRevision content-binds
-- the complete normalized node/edge/scope triple.
data VerificationObligationGraph = VerificationObligationGraph
  { verificationGraphRevision :: Digest
  , verificationGraphNodes :: Map RevisionId ObligationRevision
  , verificationGraphDependencies :: Set (RevisionId, RevisionId)
  , verificationGraphCertificationScope :: Set RevisionId
  }
  deriving (Eq, Show)

data VerificationGraphError
  = ConflictingObligationInputs ObligationId
  | UnknownObligationDependency ObligationId ObligationId
  | UnknownCertificationScopeObligation ObligationId
  | CyclicObligationDependencies (Set ObligationId)
  deriving (Eq, Show)

-- | Build the canonical residual-obligation/dependency graph before proof
-- search.  Exact duplicate inputs collapse; a reused stable ObligationId with
-- different semantics rejects.  Subject/context order and AcceptAll/AcceptAny
-- branch order are normalized because those are set-like semantic dimensions.
-- Changing proposition, subject, context, acceptance content, dependency, or
-- certification scope changes the resulting graph or rejects invalid input.
buildVerificationObligationGraph
  :: [VerificationObligationInput]
  -> Set ObligationId
  -> Either VerificationGraphError VerificationObligationGraph
buildVerificationObligationGraph rawInputs requestedScope = do
  inputs <- foldM insertCanonicalInput Map.empty rawInputs
  validateScope inputs requestedScope
  validateDependencies inputs
  case cyclicRegion inputs of
    Nothing -> pure ()
    Just region -> Left (CyclicObligationDependencies region)
  let byObligation = Map.map inputRevision inputs
      revisionLookup = Map.map revisionId byObligation
      nodes = Map.fromList
        [ (revisionId revision, revision)
        | revision <- Map.elems byObligation
        ]
      edges = Set.fromList
        [ (revisionLookup Map.! obligationId, revisionLookup Map.! dependencyId)
        | (obligationId, input) <- Map.toAscList inputs
        , dependencyId <- Set.toAscList (verificationInputDependencies input)
        ]
      scope = Set.map (revisionLookup Map.!) requestedScope
      graphDigest = digestText (renderGraphIdentity nodes edges scope)
  Right VerificationObligationGraph
    { verificationGraphRevision = graphDigest
    , verificationGraphNodes = nodes
    , verificationGraphDependencies = edges
    , verificationGraphCertificationScope = scope
    }

insertCanonicalInput
  :: Map ObligationId VerificationObligationInput
  -> VerificationObligationInput
  -> Either VerificationGraphError (Map ObligationId VerificationObligationInput)
insertCanonicalInput inputs rawInput =
  let input = canonicalizeInput rawInput
      obligationId = obligationIdOf input
  in case Map.lookup obligationId inputs of
      Nothing -> Right (Map.insert obligationId input inputs)
      Just existing
        | existing == input -> Right inputs
        | otherwise -> Left (ConflictingObligationInputs obligationId)

canonicalizeInput :: VerificationObligationInput -> VerificationObligationInput
canonicalizeInput input = input
  { verificationInputSubjectIds = sort (verificationInputSubjectIds input)
  , verificationInputContextIds = sort (verificationInputContextIds input)
  , verificationInputAcceptanceRule =
      canonicalizeAcceptanceRule (verificationInputAcceptanceRule input)
  }

canonicalizeAcceptanceRule :: AcceptanceRule -> AcceptanceRule
canonicalizeAcceptanceRule rule = case rule of
  AcceptEntry kind role -> AcceptEntry kind role
  AcceptAll rules -> AcceptAll (sort (map canonicalizeAcceptanceRule rules))
  AcceptAny rules -> AcceptAny (sort (map canonicalizeAcceptanceRule rules))

obligationIdOf :: VerificationObligationInput -> ObligationId
obligationIdOf = obligationId . verificationInputObligation

inputRevision :: VerificationObligationInput -> ObligationRevision
inputRevision input = revisionFromCoreObligation
  (verificationInputObligation input)
  (verificationInputKind input)
  (verificationInputRepresentation input)
  (verificationInputSubjectIds input)
  (verificationInputContextIds input)
  (verificationInputAcceptanceRule input)
  []

validateScope
  :: Map ObligationId VerificationObligationInput
  -> Set ObligationId
  -> Either VerificationGraphError ()
validateScope inputs requestedScope =
  case Set.lookupMin (requestedScope `Set.difference` Map.keysSet inputs) of
    Nothing -> Right ()
    Just missing -> Left (UnknownCertificationScopeObligation missing)

validateDependencies
  :: Map ObligationId VerificationObligationInput
  -> Either VerificationGraphError ()
validateDependencies inputs = go (Map.toAscList inputs)
  where
    known = Map.keysSet inputs

    go [] = Right ()
    go ((obligationId, input) : rest) =
      case Set.lookupMin (verificationInputDependencies input `Set.difference` known) of
        Nothing -> go rest
        Just missing -> Left (UnknownObligationDependency obligationId missing)

cyclicRegion
  :: Map ObligationId VerificationObligationInput
  -> Maybe (Set ObligationId)
cyclicRegion inputs = go dependencyMap
  where
    dependencyMap = Map.map verificationInputDependencies inputs

    go remaining
      | Map.null remaining = Nothing
      | null roots = Just (Map.keysSet remaining)
      | otherwise = go $ Map.map (`Set.difference` rootSet) withoutRoots
      where
        roots =
          [ obligationId
          | (obligationId, dependencies) <- Map.toAscList remaining
          , Set.null dependencies
          ]
        rootSet = Set.fromList roots
        withoutRoots = foldr Map.delete remaining roots

renderGraphIdentity
  :: Map RevisionId ObligationRevision
  -> Set (RevisionId, RevisionId)
  -> Set RevisionId
  -> Text
renderGraphIdentity nodes edges scope = Text.intercalate "\n"
  [ "verification-obligation-graph-v1"
  , "nodes=" <> Text.intercalate "," (map unRevisionId (Map.keys nodes))
  , "edges=" <> Text.intercalate "," (map renderEdge (Set.toAscList edges))
  , "scope=" <> Text.intercalate "," (map unRevisionId (Set.toAscList scope))
  ]
  where
    renderEdge (fromRevision, toRevision) =
      unRevisionId fromRevision <> "->" <> unRevisionId toRevision

-- | Run competent intrinsic checking before assurance disposition.  In
-- particular, even a policy that permits every Phase-1 disposition cannot turn
-- parsing, component-shape, structural, protocol, authority, borrow, or other
-- surface semantic rejection into a residual obligation.
verifySurfaceApplication
  :: SurfaceEnvironment
  -> ApplicationAssurancePolicy
  -> Text
  -> Text
  -> ApplicationVerificationResult
verifySurfaceApplication environment policy sourceName source =
  case parseSurfaceFile sourceName source of
    Left diagnostic -> IntrinsicRejected (IntrinsicParseRejected diagnostic)
    Right (SurfaceFile [component]) ->
      case checkSurfaceComponent environment component of
        Left errorValue -> IntrinsicRejected (IntrinsicSurfaceRejected errorValue)
        Right checked -> ReadyForObligationClosure
          { readyCheckedSurface = checked
          , readyAssurancePolicy = policy
          }
    Right (SurfaceFile components) ->
      IntrinsicRejected (IntrinsicComponentCardinalityRejected (length components))
