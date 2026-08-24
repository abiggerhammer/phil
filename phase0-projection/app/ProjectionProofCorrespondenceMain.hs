{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance
import Phil.LLVM
  ( LLVMVerificationContext (..)
  , llvmArtifactModule
  , llvmRuntimeABIProfile
  , lowerSystemsControlCodec
  , phase0ControlCodecLLVMTarget
  , phase0ControlCodecLLVMVerificationContext
  , verifyLLVMEmissionWith
  )
import Phil.Phase0UploadProjection
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  clientSource <- TextIO.readFile "examples/upload/client.phil"
  serverSource <- TextIO.readFile "examples/upload/server.phil"
  results <- sequence
    [ test "landed Phase 0 upload projection verifies" $
        projectionVerifies clientSource serverSource
    , test "projection preserves canonical base and final Systems programs" $
        programsPreserved clientSource serverSource
    , test "projection binds exact source digest in stage contracts and all lowering decisions" $
        sourceBindingExact clientSource serverSource
    , test "projection rederives decision digests, lowering roots, manifests and verification contexts" $
        identityMetadataRederived clientSource serverSource
    , test "source-bound final Systems artifact translation-validates through control-codec-v1" $
        downstreamControlCodecVerifies clientSource serverSource
    , test "client/server file-boundary ambiguity from delimiter concatenation is eliminated" $
        sourcePairBoundaryBinding
    , test "whitespace-only source change changes source authority without changing projected program" $
        contentBindingPreservesSemantics clientSource serverSource
    , test "semantic trace drift cannot silently reuse the frozen upload projection" $
        semanticDriftRejects clientSource serverSource
    , test "projection source-digest identity drift is rejected" $
        sourceDigestDriftRejects clientSource serverSource
    , test "rebound stage source identity drift is rejected" $
        stageSourceDriftRejects clientSource serverSource
    , test "canonical Systems program substitution is rejected" $
        programDriftRejects clientSource serverSource
    ]
  if and results then pure () else exitFailure

projectionVerifies :: Text.Text -> Text.Text -> Bool
projectionVerifies clientSource serverSource =
  case projectPhase0UploadSources clientSource serverSource of
    Left _ -> False
    Right projection -> verifyPhase0UploadProjection projection == Right ()

programsPreserved :: Text.Text -> Text.Text -> Bool
programsPreserved clientSource serverSource = withProjection clientSource serverSource $ \projection ->
  case phase0StorageFailureBundle of
    Left _ -> False
    Right baseline ->
      systemsArtifactProgram (phase0ProjectionBaseArtifact projection)
        == systemsArtifactProgram phase0SystemsArtifact
      && systemsArtifactProgram (phase0ProjectionFinalArtifact projection)
        == systemsArtifactProgram (storageFailureArtifact baseline)

sourceBindingExact :: Text.Text -> Text.Text -> Bool
sourceBindingExact clientSource serverSource = withProjection clientSource serverSource $ \projection ->
  let sourceDigest = phase0ProjectionSourceDigest projection
      artifacts =
        [ phase0ProjectionBaseArtifact projection
        , phase0ProjectionFinalArtifact projection
        ]
      artifactBound artifact =
        stageSourceArtifactDigest (systemsArtifactStageContract artifact) == sourceDigest
        && all
          ((== sourceDigest) . loweringSourceArtifactDigest)
          (Map.elems (loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)))
  in all artifactBound artifacts

identityMetadataRederived :: Text.Text -> Text.Text -> Bool
identityMetadataRederived clientSource serverSource = withProjection clientSource serverSource $ \projection ->
  artifactContextExact
    (phase0ProjectionSourceDigest projection)
    (phase0ProjectionBaseArtifact projection)
    (phase0ProjectionBaseContext projection)
  && artifactContextExact
    (phase0ProjectionSourceDigest projection)
    (phase0ProjectionFinalArtifact projection)
    (phase0ProjectionFinalContext projection)

artifactContextExact :: Digest -> SystemsArtifact -> SystemsVerificationContext -> Bool
artifactContextExact sourceDigest artifact context =
  let ledger = systemsArtifactLoweringLedger artifact
      decisions = loweringLedgerDecisions ledger
      root = loweringLedgerRoot ledger
      manifest = systemsAssuranceManifest context
      verification = systemsAssuranceVerificationContext context
      decisionDigestExact decision =
        loweringDecisionDigest decision
          == deriveLoweringDecisionDigest
            (decision { loweringDecisionDigest = digestText "" })
  in all decisionDigestExact (Map.elems decisions)
      && root == deriveLoweringLedgerRoot decisions
      && manifestImplementationDigest manifest == systemsArtifactDigest artifact
      && manifestLoweringLedgerRoot manifest == root
      && verificationImplementationDigest verification == systemsArtifactDigest artifact
      && verificationLoweringLedgerRoot verification == root
      && systemsExpectedSourceArtifactDigest context == sourceDigest


downstreamControlCodecVerifies :: Text.Text -> Text.Text -> Bool
downstreamControlCodecVerifies clientSource serverSource = withProjection clientSource serverSource $ \projection ->
  case phase0StorageFailureBundle of
    Left _ -> False
    Right baseline ->
      let finalArtifact = phase0ProjectionFinalArtifact projection
          llvmArtifact = lowerSystemsControlCodec phase0ControlCodecLLVMTarget finalArtifact
          llvmContext =
            (phase0ControlCodecLLVMVerificationContext baseline)
              { llvmSystemsContext = phase0ProjectionFinalContext projection }
      in verifyLLVMEmissionWith
          lowerSystemsControlCodec llvmContext finalArtifact llvmArtifact == Right ()
          && llvmRuntimeABIProfile (llvmArtifactModule llvmArtifact)
            == "phil-runtime/phase0/control-codec-v1"

sourcePairBoundaryBinding :: Bool
sourcePairBoundaryBinding =
  let clientA = "x\nfile:server.phil\ny"
      serverA = "z"
      clientB = "x"
      serverB = "y\nfile:server.phil\nz"
      legacyDigest clientSource serverSource = digestText $ Text.intercalate "\n"
        [ "phil-source-pair/phase0-upload/v1"
        , "file:client.phil"
        , clientSource
        , "file:server.phil"
        , serverSource
        ]
  in legacyDigest clientA serverA == legacyDigest clientB serverB
      && phase0UploadSourceDigest clientA serverA
        /= phase0UploadSourceDigest clientB serverB

contentBindingPreservesSemantics :: Text.Text -> Text.Text -> Bool
contentBindingPreservesSemantics clientSource serverSource =
  case ( projectPhase0UploadSources clientSource serverSource
       , projectPhase0UploadSources clientSource (serverSource <> "\n")
       ) of
    (Right original, Right whitespaceVariant) ->
      phase0ProjectionSourceDigest original /= phase0ProjectionSourceDigest whitespaceVariant
      && systemsArtifactProgram (phase0ProjectionFinalArtifact original)
        == systemsArtifactProgram (phase0ProjectionFinalArtifact whitespaceVariant)
    _ -> False

semanticDriftRejects :: Text.Text -> Text.Text -> Bool
semanticDriftRejects clientSource serverSource =
  let drifted = Text.replace "record_upload_id(id)" "inspect(id)" clientSource
  in case projectPhase0UploadSources drifted serverSource of
      Left _ -> True
      Right _ -> False

sourceDigestDriftRejects :: Text.Text -> Text.Text -> Bool
sourceDigestDriftRejects clientSource serverSource = withProjection clientSource serverSource $ \projection ->
  isLeft (verifyPhase0UploadProjection
    (projection { phase0ProjectionSourceDigest = digestText "wrong-source-pair" }))

stageSourceDriftRejects :: Text.Text -> Text.Text -> Bool
stageSourceDriftRejects clientSource serverSource = withProjection clientSource serverSource $ \projection ->
  let artifact = phase0ProjectionBaseArtifact projection
      contract = systemsArtifactStageContract artifact
      mutatedArtifact = artifact
        { systemsArtifactStageContract = contract
            { stageSourceArtifactDigest = digestText "wrong-stage-source" }
        }
  in isLeft (verifyPhase0UploadProjection
      (projection { phase0ProjectionBaseArtifact = mutatedArtifact }))

programDriftRejects :: Text.Text -> Text.Text -> Bool
programDriftRejects clientSource serverSource = withProjection clientSource serverSource $ \projection ->
  isLeft (verifyPhase0UploadProjection
    (projection
      { phase0ProjectionBaseArtifact = phase0ProjectionFinalArtifact projection
      }))

withProjection
  :: Text.Text
  -> Text.Text
  -> (Phase0UploadProjection -> Bool)
  -> Bool
withProjection clientSource serverSource action =
  case projectPhase0UploadSources clientSource serverSource of
    Left _ -> False
    Right projection -> action projection

isLeft :: Either a b -> Bool
isLeft value = case value of
  Left _ -> True
  Right _ -> False

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
