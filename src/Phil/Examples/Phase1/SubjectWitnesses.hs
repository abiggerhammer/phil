{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.SubjectWitnesses
  ( uploadSubjectStageBundle
  , steveSubjectStageBundle
  , uploadPayloadSubject
  , steveCandidateSubject
  , steveReadSubject
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Examples.Phase1.SystemsWitnesses
  ( stevePhase1StageBundle
  , uploadPhase1StageBundle
  )
import Phil.Systems.IR (ValueId (..))
import Phil.Systems.SubjectCorrespondence

uploadPayloadSubject :: SourceSubjectKey
uploadPayloadSubject = SourceSubjectKey "upload.payload.server"

steveCandidateSubject, steveReadSubject :: SourceSubjectKey
steveCandidateSubject = SourceSubjectKey "steve.bytes.candidate"
steveReadSubject = SourceSubjectKey "steve.bytes.read-result"

uploadSubjectStageBundle :: SubjectStageBundle
uploadSubjectStageBundle = makeSubjectStageBundle
  uploadPhase1StageBundle
  (Map.singleton uploadPayloadSubject uploadPayloadCorrespondence)

steveSubjectStageBundle :: Either String SubjectStageBundle
steveSubjectStageBundle = do
  base <- stevePhase1StageBundle
  pure (makeSubjectStageBundle base (Map.fromList
    [ (steveCandidateSubject, steveCandidateCorrespondence)
    , (steveReadSubject, steveReadCorrespondence)
    ]))

uploadPayloadCorrespondence :: SubjectCorrespondence
uploadPayloadCorrespondence = SubjectCorrespondence
  { subjectCorrespondenceSource = uploadPayloadSubject
  , subjectCorrespondenceSystemsValues = Set.fromList
      [ SystemsValueRef "UploadServer" (ValueId "server.payload")
      , SystemsValueRef "UploadServer" (ValueId "server.payload_view")
      ]
  , subjectCorrespondenceBasis = CheckedSubjectRelation
      (SubjectRelationRevision "subject.upload.payload.owner-and-borrow.v1")
  , subjectCorrespondenceValidityScope = SubjectValidityScopeRevision
      "scope.upload.payload.owner-live.v1"
  , subjectCorrespondenceEvidenceRefs = Set.fromList
      [ "digest.shared_borrow"
      , "payload.exact_receive"
      ]
  }

steveCandidateCorrespondence :: SubjectCorrespondence
steveCandidateCorrespondence = SubjectCorrespondence
  { subjectCorrespondenceSource = steveCandidateSubject
  , subjectCorrespondenceSystemsValues = Set.fromList
      [ SystemsValueRef "StevePut" (ValueId "put.candidate")
      , SystemsValueRef "StevePut" (ValueId "put.digest-view")
      , SystemsValueRef "StevePut" (ValueId "put.install-view")
      ]
  , subjectCorrespondenceBasis = CheckedSubjectRelation
      (SubjectRelationRevision "subject.steve.candidate.owner-and-borrows.v1")
  , subjectCorrespondenceValidityScope = SubjectValidityScopeRevision
      "scope.steve.candidate.owner-live.v1"
  , subjectCorrespondenceEvidenceRefs = Set.fromList
      [ "steve.digest.stable-subject"
      , "steve.blob.borrow-preservation"
      ]
  }

steveReadCorrespondence :: SubjectCorrespondence
steveReadCorrespondence = SubjectCorrespondence
  { subjectCorrespondenceSource = steveReadSubject
  , subjectCorrespondenceSystemsValues = Set.fromList
      [ SystemsValueRef "SteveGet" (ValueId "get.bytes")
      , SystemsValueRef "SteveGet" (ValueId "get.bytes-view")
      ]
  , subjectCorrespondenceBasis = CheckedSubjectRelation
      (SubjectRelationRevision "subject.steve.read-result.owner-and-borrow.v1")
  , subjectCorrespondenceValidityScope = SubjectValidityScopeRevision
      "scope.steve.read-result.owner-live.v1"
  , subjectCorrespondenceEvidenceRefs = Set.fromList
      [ "steve.digest.stable-subject"
      , "steve.provider.admission-lineage"
      ]
  }
