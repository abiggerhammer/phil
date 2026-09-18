{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1VerificationBundle
  ( HandoffVerificationNode (..)
  , HandoffVerificationEdge (..)
  , HandoffAcceptedEvidence (..)
  , Phase1VerificationBundleSummary (..)
  , Phase1VerificationBundleSummaryError (..)
  , phase1VerificationBundleFormatV1
  , derivePhase1VerificationBundleSummary
  , renderPhase1VerificationBundleSummary
  , decodePhase1VerificationBundleSummary
  ) where

import Data.Char (isDigit)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( Digest (..)
  , EvidenceEntryId (..)
  , ObligationRevision (..)
  , RevisionId (..)
  )
import Phil.Verification
  ( AssurancePolicyRevision (..)
  , VerificationObligationGraph (..)
  )
import Phil.Verification.Bundle
  ( AcceptedEvidenceReference (..)
  , VerificationBundle (..)
  , verificationBundleArchitectureDigest
  )

data HandoffVerificationNode = HandoffVerificationNode
  { handoffVerificationNodeRevision :: RevisionId
  , handoffVerificationNodeStatementSha256 :: Text
  }
  deriving (Eq, Ord, Show)

data HandoffVerificationEdge = HandoffVerificationEdge
  { handoffVerificationEdgeFrom :: RevisionId
  , handoffVerificationEdgeTo :: RevisionId
  }
  deriving (Eq, Ord, Show)

data HandoffAcceptedEvidence = HandoffAcceptedEvidence
  { handoffAcceptedEvidenceId :: EvidenceEntryId
  , handoffAcceptedEvidenceSha256 :: Text
  , handoffAcceptedEvidenceObligationRevision :: RevisionId
  }
  deriving (Eq, Ord, Show)

data Phase1VerificationBundleSummary = Phase1VerificationBundleSummary
  { handoffVerificationBundleRevisionSha256 :: Text
  , handoffVerificationSourceRevisionSha256 :: Text
  , handoffVerificationArchitectureSha256 :: Text
  , handoffVerificationGraphRevisionSha256 :: Text
  , handoffVerificationPolicyRevision :: AssurancePolicyRevision
  , handoffVerificationNodes :: [HandoffVerificationNode]
  , handoffVerificationEdges :: [HandoffVerificationEdge]
  , handoffVerificationScope :: [RevisionId]
  , handoffVerificationEvidence :: [HandoffAcceptedEvidence]
  }
  deriving (Eq, Show)

data Phase1VerificationBundleSummaryError
  = VerificationSummaryEmpty
  | VerificationSummaryHeaderMismatch Text
  | VerificationSummaryMalformedRecord Int Text
  | VerificationSummaryMalformedDigest Int Text
  | VerificationSummaryDuplicateBundle
  | VerificationSummaryMissingBundle
  | VerificationSummaryDuplicateNode RevisionId
  | VerificationSummaryDuplicateEdge HandoffVerificationEdge
  | VerificationSummaryDuplicateScope RevisionId
  | VerificationSummaryDuplicateEvidence EvidenceEntryId
  | VerificationSummaryUnknownEdgeEndpoint RevisionId
  | VerificationSummaryUnknownScopeRevision RevisionId
  | VerificationSummaryUnknownEvidenceRevision RevisionId
  deriving (Eq, Show)

phase1VerificationBundleFormatV1 :: Text
phase1VerificationBundleFormatV1 = "PHIL-PHASE1-VERIFICATION-BUNDLE-V1"

derivePhase1VerificationBundleSummary
  :: VerificationBundle
  -> Phase1VerificationBundleSummary
derivePhase1VerificationBundleSummary bundle =
  Phase1VerificationBundleSummary
    { handoffVerificationBundleRevisionSha256 =
        digestSha256 (verificationBundleRevision bundle)
    , handoffVerificationSourceRevisionSha256 =
        digestSha256 (verificationBundleSourceRevision bundle)
    , handoffVerificationArchitectureSha256 =
        digestSha256 (verificationBundleArchitectureDigest bundle)
    , handoffVerificationGraphRevisionSha256 =
        digestSha256 (verificationGraphRevision graph)
    , handoffVerificationPolicyRevision = verificationBundlePolicyRevision bundle
    , handoffVerificationNodes = sort
        [ HandoffVerificationNode revisionIdValue
            (digestSha256 (revisionStatementDigest revision))
        | (revisionIdValue, revision) <- Map.toAscList (verificationGraphNodes graph)
        ]
    , handoffVerificationEdges = sort
        [ HandoffVerificationEdge fromRevision toRevision
        | (fromRevision, toRevision) <-
            Set.toAscList (verificationGraphDependencies graph)
        ]
    , handoffVerificationScope =
        Set.toAscList (verificationGraphCertificationScope graph)
    , handoffVerificationEvidence = sort
        [ HandoffAcceptedEvidence entryId
            (digestSha256 (acceptedEvidenceDigest reference))
            (acceptedEvidenceObligationRevision reference)
        | (entryId, reference) <-
            Map.toAscList (verificationBundleAcceptedEvidence bundle)
        ]
    }
  where
    graph = verificationBundleObligationGraph bundle

digestSha256 :: Digest -> Text
digestSha256 = ("sha256:" <>) . unDigest

renderPhase1VerificationBundleSummary
  :: Phase1VerificationBundleSummary
  -> Text
renderPhase1VerificationBundleSummary summary = Text.unlines $
  [ phase1VerificationBundleFormatV1
  , Text.intercalate "\t"
      [ "bundle"
      , handoffVerificationBundleRevisionSha256 summary
      , handoffVerificationSourceRevisionSha256 summary
      , handoffVerificationArchitectureSha256 summary
      , handoffVerificationGraphRevisionSha256 summary
      , unAssurancePolicyRevision (handoffVerificationPolicyRevision summary)
      , "accepted"
      ]
  ]
  <> map renderNode (sort (handoffVerificationNodes summary))
  <> map renderEdge (sort (handoffVerificationEdges summary))
  <> map renderScope (sort (handoffVerificationScope summary))
  <> map renderEvidence (sort (handoffVerificationEvidence summary))
  where
    renderNode node = Text.intercalate "\t"
      [ "node"
      , unRevisionId (handoffVerificationNodeRevision node)
      , handoffVerificationNodeStatementSha256 node
      ]
    renderEdge edge = Text.intercalate "\t"
      [ "edge"
      , unRevisionId (handoffVerificationEdgeFrom edge)
      , unRevisionId (handoffVerificationEdgeTo edge)
      ]
    renderScope revision =
      Text.intercalate "\t" ["scope", unRevisionId revision]
    renderEvidence evidence = Text.intercalate "\t"
      [ "evidence"
      , unEvidenceEntryId (handoffAcceptedEvidenceId evidence)
      , handoffAcceptedEvidenceSha256 evidence
      , unRevisionId (handoffAcceptedEvidenceObligationRevision evidence)
      ]

data DecodeState = DecodeState
  { decodeBundle :: Maybe (Text, Text, Text, Text, AssurancePolicyRevision)
  , decodeNodes :: [HandoffVerificationNode]
  , decodeEdges :: [HandoffVerificationEdge]
  , decodeScope :: [RevisionId]
  , decodeEvidence :: [HandoffAcceptedEvidence]
  }

emptyDecodeState :: DecodeState
emptyDecodeState = DecodeState Nothing [] [] [] []

decodePhase1VerificationBundleSummary
  :: Text
  -> Either Phase1VerificationBundleSummaryError Phase1VerificationBundleSummary
decodePhase1VerificationBundleSummary input =
  case Text.lines input of
    [] -> Left VerificationSummaryEmpty
    header : rows
      | Text.strip header /= phase1VerificationBundleFormatV1 ->
          Left (VerificationSummaryHeaderMismatch (Text.strip header))
      | otherwise -> do
          state <- foldl step (Right emptyDecodeState) (zip [2 ..] rows)
          (bundleRevision, sourceRevision, architectureDigest, graphRevision, policy) <-
            maybe (Left VerificationSummaryMissingBundle) Right
              (decodeBundle state)
          let nodes = sort (decodeNodes state)
              edges = sort (decodeEdges state)
              scope = sort (decodeScope state)
              evidence = sort (decodeEvidence state)
              nodeDomain = Set.fromList (map handoffVerificationNodeRevision nodes)
          mapM_ (validateEdge nodeDomain) edges
          mapM_ (validateScope nodeDomain) scope
          mapM_ (validateEvidence nodeDomain) evidence
          Right Phase1VerificationBundleSummary
            { handoffVerificationBundleRevisionSha256 = bundleRevision
            , handoffVerificationSourceRevisionSha256 = sourceRevision
            , handoffVerificationArchitectureSha256 = architectureDigest
            , handoffVerificationGraphRevisionSha256 = graphRevision
            , handoffVerificationPolicyRevision = policy
            , handoffVerificationNodes = nodes
            , handoffVerificationEdges = edges
            , handoffVerificationScope = scope
            , handoffVerificationEvidence = evidence
            }
  where
    step accumulated row = accumulated >>= \state -> decodeRow state row

decodeRow
  :: DecodeState
  -> (Int, Text)
  -> Either Phase1VerificationBundleSummaryError DecodeState
decodeRow state (lineNumber, rawLine)
  | Text.null stripped = Right state
  | "#" `Text.isPrefixOf` stripped = Right state
  | otherwise =
      case Text.splitOn "\t" rawLine of
        [ "bundle"
          , bundleRevision
          , sourceRevision
          , architectureDigest
          , graphRevision
          , policyRevision
          , "accepted"
          ] -> do
            mapM_ (validateDigest lineNumber)
              [bundleRevision, sourceRevision, architectureDigest, graphRevision]
            case decodeBundle state of
              Nothing -> Right state
                { decodeBundle = Just
                    ( bundleRevision
                    , sourceRevision
                    , architectureDigest
                    , graphRevision
                    , AssurancePolicyRevision policyRevision
                    )
                }
              Just _ -> Left VerificationSummaryDuplicateBundle
        ["node", rawRevision, statementDigest]
          | not (Text.null rawRevision) -> do
              validateDigest lineNumber statementDigest
              let node = HandoffVerificationNode
                    (RevisionId rawRevision) statementDigest
              if any ((== RevisionId rawRevision) . handoffVerificationNodeRevision)
                  (decodeNodes state)
                then Left (VerificationSummaryDuplicateNode (RevisionId rawRevision))
                else Right state { decodeNodes = node : decodeNodes state }
          | otherwise -> malformed
        ["edge", rawFrom, rawTo]
          | all (not . Text.null) [rawFrom, rawTo] ->
              let edge = HandoffVerificationEdge
                    (RevisionId rawFrom) (RevisionId rawTo)
              in if edge `elem` decodeEdges state
                  then Left (VerificationSummaryDuplicateEdge edge)
                  else Right state { decodeEdges = edge : decodeEdges state }
          | otherwise -> malformed
        ["scope", rawRevision]
          | not (Text.null rawRevision) ->
              let revision = RevisionId rawRevision
              in if revision `elem` decodeScope state
                  then Left (VerificationSummaryDuplicateScope revision)
                  else Right state { decodeScope = revision : decodeScope state }
          | otherwise -> malformed
        ["evidence", rawId, evidenceDigest, rawRevision]
          | all (not . Text.null) [rawId, rawRevision] -> do
              validateDigest lineNumber evidenceDigest
              let evidence = HandoffAcceptedEvidence
                    (EvidenceEntryId rawId)
                    evidenceDigest
                    (RevisionId rawRevision)
              if any ((== EvidenceEntryId rawId) . handoffAcceptedEvidenceId)
                  (decodeEvidence state)
                then Left
                  (VerificationSummaryDuplicateEvidence (EvidenceEntryId rawId))
                else Right state
                  { decodeEvidence = evidence : decodeEvidence state }
          | otherwise -> malformed
        _ -> malformed
  where
    stripped = Text.strip rawLine
    malformed = Left (VerificationSummaryMalformedRecord lineNumber rawLine)

validateDigest
  :: Int
  -> Text
  -> Either Phase1VerificationBundleSummaryError ()
validateDigest lineNumber raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest
      | Text.length digest == 64
      , Text.all lowerHex digest -> Right ()
    _ -> Left (VerificationSummaryMalformedDigest lineNumber raw)
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

validateEdge
  :: Set.Set RevisionId
  -> HandoffVerificationEdge
  -> Either Phase1VerificationBundleSummaryError ()
validateEdge domain edge
  | not (Set.member (handoffVerificationEdgeFrom edge) domain) =
      Left (VerificationSummaryUnknownEdgeEndpoint
        (handoffVerificationEdgeFrom edge))
  | not (Set.member (handoffVerificationEdgeTo edge) domain) =
      Left (VerificationSummaryUnknownEdgeEndpoint
        (handoffVerificationEdgeTo edge))
  | otherwise = Right ()

validateScope
  :: Set.Set RevisionId
  -> RevisionId
  -> Either Phase1VerificationBundleSummaryError ()
validateScope domain revision
  | Set.member revision domain = Right ()
  | otherwise = Left (VerificationSummaryUnknownScopeRevision revision)

validateEvidence
  :: Set.Set RevisionId
  -> HandoffAcceptedEvidence
  -> Either Phase1VerificationBundleSummaryError ()
validateEvidence domain evidence
  | Set.member (handoffAcceptedEvidenceObligationRevision evidence) domain =
      Right ()
  | otherwise = Left
      (VerificationSummaryUnknownEvidenceRevision
        (handoffAcceptedEvidenceObligationRevision evidence))
