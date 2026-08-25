{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.BranchResourceWitnesses
  ( uploadBranchResourceStageBundle
  , steveBranchResourceStageBundle
  , uploadReceiveSite
  , uploadDigestSite
  , steveDigestComputeSite
  , steveBlobInstallSite
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.AuthorityEffectWitnesses
  ( steveAuthorityEffectStageBundle
  , uploadAuthorityEffectStageBundle
  )
import Phil.Systems.BranchResourceFailure
import Phil.Systems.IR (BlockId (..), ValueId (..))
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))

uploadBranchResourceStageBundle :: Either String BranchResourceStageBundle
uploadBranchResourceStageBundle = do
  base <- uploadAuthorityEffectStageBundle
  pure (makeBranchResourceStageBundle base (Map.fromList
    [ (uploadReceiveSite, uploadReceiveContract)
    , (uploadDigestSite, uploadDigestContract)
    ]))

steveBranchResourceStageBundle :: Either String BranchResourceStageBundle
steveBranchResourceStageBundle = do
  base <- steveAuthorityEffectStageBundle
  pure (makeBranchResourceStageBundle base (Map.fromList
    [ (steveDigestComputeSite, steveDigestComputeContract)
    , (steveBlobInstallSite, steveBlobInstallContract)
    ]))

uploadReceiveSite, uploadDigestSite :: SystemsMechanismKey
uploadReceiveSite = SystemsMechanismKey
  "UploadServer:server.payload:term.receive-exact"
uploadDigestSite = SystemsMechanismKey
  "UploadServer:server.digest:term.runtime-check"

steveDigestComputeSite, steveBlobInstallSite :: SystemsMechanismKey
steveDigestComputeSite = SystemsMechanismKey
  "StevePut:put.entry:term.runtime-choice.DigestProvider.compute"
steveBlobInstallSite = SystemsMechanismKey
  "StevePut:put.install:term.runtime-choice.BlobProvider.install-if-absent"

uploadPayloadOwner, steveCandidateOwner :: ValueId
uploadPayloadOwner = ValueId "server.payload"
steveCandidateOwner = ValueId "put.candidate"

uploadReceiveContract :: BranchSiteContract
uploadReceiveContract = BranchSiteContract
  { branchSiteMechanism = uploadReceiveSite
  , branchSiteFunction = "UploadServer"
  , branchSiteBlock = BlockId "server.payload"
  , branchSiteTrackedOwners = Set.singleton uploadPayloadOwner
  , branchSiteOutcomes = Map.fromList
      [ ("success", outcome
          "upload.payload.exact_receive.success"
          uploadPayloadOwner OwnerContinues BranchContinues)
      , ("failure", outcome
          "upload.payload.exact_receive.early-eof"
          uploadPayloadOwner OwnerReleased (BranchFatal "EarlyEOF"))
      ]
  }

uploadDigestContract :: BranchSiteContract
uploadDigestContract = BranchSiteContract
  { branchSiteMechanism = uploadDigestSite
  , branchSiteFunction = "UploadServer"
  , branchSiteBlock = BlockId "server.digest"
  , branchSiteTrackedOwners = Set.singleton uploadPayloadOwner
  , branchSiteOutcomes = Map.fromList
      [ ("success", outcome
          "upload.digest.matches.success"
          uploadPayloadOwner OwnerContinues BranchContinues)
      , ("failure", outcome
          "upload.digest.matches.failure"
          uploadPayloadOwner OwnerReleased (BranchEnds "failure"))
      ]
  }

steveDigestComputeContract :: BranchSiteContract
steveDigestComputeContract = BranchSiteContract
  { branchSiteMechanism = steveDigestComputeSite
  , branchSiteFunction = "StevePut"
  , branchSiteBlock = BlockId "put.entry"
  , branchSiteTrackedOwners = Set.singleton steveCandidateOwner
  , branchSiteOutcomes = Map.singleton "computed"
      (outcome
        "steve.digest.compute.success"
        steveCandidateOwner OwnerContinues BranchContinues)
  }

steveBlobInstallContract :: BranchSiteContract
steveBlobInstallContract = BranchSiteContract
  { branchSiteMechanism = steveBlobInstallSite
  , branchSiteFunction = "StevePut"
  , branchSiteBlock = BlockId "put.install"
  , branchSiteTrackedOwners = Set.singleton steveCandidateOwner
  , branchSiteOutcomes = Map.fromList
      [ ("installed", outcome
          "steve.blob.install.installed"
          steveCandidateOwner OwnerReturnedAtTerminal (BranchEnds "success"))
      , ("already-exists", outcome
          "steve.blob.install.already-exists"
          steveCandidateOwner OwnerReturnedAtTerminal (BranchEnds "success"))
      , ("storage-failure", outcome
          "steve.blob.install.storage-failure"
          steveCandidateOwner OwnerReturnedAtTerminal (BranchEnds "storage-failure"))
      ]
  }

outcome
  :: String
  -> ValueId
  -> BranchOwnerFate
  -> BranchControlClass
  -> BranchOutcomeContract
outcome semanticRef owner fate control = BranchOutcomeContract
  { branchOutcomeSemanticRef = fromString semanticRef
  , branchOutcomeOwnerFates = Map.singleton owner fate
  , branchOutcomeControlClass = control
  }

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack
