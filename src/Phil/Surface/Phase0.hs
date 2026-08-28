{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Phase0
  ( FixtureExpectation (..)
  , phase0EnvironmentFor
  , phase0ExpectationFor
  , serverUploadSession
  , clientUploadSession
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Session (dualSession)
import Phil.Core.Static
  ( StaticContext
  , declareOpaqueClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Branch (..)
  , FrameId (..)
  , GrammarId (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( FieldInfo (..)
  , InitialBinding (..)
  , PrimitiveSemantics (..)
  , RejectionClass (..)
  , ReleaseResidue (..)
  , ReleaseSemanticAccount (..)
  , ReleaseTransitionContract (..)
  , ReleaseTransitionOutcome (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , emptySurfaceEnvironment
  )

data FixtureExpectation
  = FixtureAccept
  | FixtureReject RejectionClass
  deriving (Eq, Show)

phase0ExpectationFor :: FilePath -> Maybe FixtureExpectation
phase0ExpectationFor path =
  case fileName path of
    "client.phil" -> Just FixtureAccept
    "server.phil" -> Just FixtureAccept
    "01-reuse-consumed-endpoint.phil" -> reject StructuralUse
    "02-drop-live-endpoint.phil" -> reject LinearCompletion
    "03-wrong-protocol-order.phil" -> reject SessionAction
    "04-nonexhaustive-offer.phil" -> reject BranchExhaustiveness
    "05-raw-field-access.phil" -> reject IllegalProjection
    "06-parsed-used-as-validated.phil" -> reject MissingEvidence
    "07-unrelated-payload-length.phil" -> reject ExplicitTransport
    "08-incompatible-branch-join.phil" -> reject IncompatibleBranchResidue
    "09-continue-after-fatal-recognition-failure.phil" -> reject ControlAfterTerminal
    "10-accept-before-digest-check.phil" -> reject MissingEvidence
    "11-copy-authority-capability.phil" -> reject StructuralUse
    "12-ignore-cancellation-cleanup.phil" -> reject LinearCompletion
    "13-commit-unrelated-parsed.phil" -> reject RecognitionProvenance
    "14-copy-owned-payload.phil" -> reject StructuralUse
    "15-drop-pending-receive.phil" -> reject LinearCompletion
    "16-escape-shared-loan.phil" -> reject BorrowEscape
    "17-use-evidence-wrong-context.phil" -> reject MissingEvidence
    "18-prove-opaque-digest.phil" -> reject OpaqueProof
    "19-label-does-not-transfer-proof.phil" -> reject MissingEvidence
    "20-unchecked-wraparound-proof.phil" -> reject UncheckedArithmetic
    _ -> Nothing
  where
    reject = Just . FixtureReject

phase0EnvironmentFor :: FilePath -> Either Text SurfaceEnvironment
phase0EnvironmentFor path = do
  staticContext <- phase0StaticContext
  let base = commonEnvironment staticContext
  case fileName path of
    "client.phil" -> Right (clientEnvironment base)
    "server.phil" -> Right (serverEnvironment base)
    "01-reuse-consumed-endpoint.phil" -> Right (simpleReceiveEnvironment base)
    "02-drop-live-endpoint.phil" -> Right (simpleReceiveEnvironment base)
    "03-wrong-protocol-order.phil" -> Right (wrongOrderEnvironment base)
    "04-nonexhaustive-offer.phil" -> Right (nonexhaustiveOfferEnvironment base)
    "05-raw-field-access.phil" -> Right (legacyRawEnvironment base)
    "06-parsed-used-as-validated.phil" -> Right (parsedValidationBypassEnvironment base)
    "07-unrelated-payload-length.phil" -> Right (unrelatedLengthEnvironment base)
    "08-incompatible-branch-join.phil" -> Right (incompatibleJoinEnvironment base)
    "09-continue-after-fatal-recognition-failure.phil" -> Right (failureReuseEnvironment base)
    "10-accept-before-digest-check.phil" -> Right (prematureAcceptanceEnvironment base)
    "11-copy-authority-capability.phil" -> Right base
    "12-ignore-cancellation-cleanup.phil" -> Right base
    "13-commit-unrelated-parsed.phil" -> Right (pendingCommitEnvironment base)
    "14-copy-owned-payload.phil" -> Right base
    "15-drop-pending-receive.phil" -> Right (pendingDropEnvironment base)
    "16-escape-shared-loan.phil" -> Right base
    "17-use-evidence-wrong-context.phil" -> Right (stalePolicyEnvironment base)
    "18-prove-opaque-digest.phil" -> Right (opaqueProofEnvironment base)
    "19-label-does-not-transfer-proof.phil" -> Right (labelProofEnvironment base)
    "20-unchecked-wraparound-proof.phil" -> Right base
    _ -> Left ("no Phase 0 checking environment for " <> Text.pack path)

phase0StaticContext :: Either Text StaticContext
phase0StaticContext =
  case declareOpaqueClaim
    "DigestMatches"
    [ (Name "begin", SortOpaque "Frame")
    , (Name "payload_id", SortStableId "OwnedBytes")
    ]
    emptyStaticContext of
      Left errorValue -> Left (Text.pack (show errorValue))
      Right context -> Right context

commonEnvironment :: StaticContext -> SurfaceEnvironment
commonEnvironment staticContext = (emptySurfaceEnvironment staticContext)
  { surfacePrimitives = Map.fromList
      [ ("supported_versions", PrimitiveSupportedVersions)
      , ("sha256", PrimitiveSha256)
      , ("should_cancel_upload", PrimitiveShouldCancel)
      , ("choose_supported", PrimitiveChooseSupported)
      , ("store", PrimitiveStore)
      , ("fixture_bytes", PrimitiveFixtureBytes)
      , ("unchecked_u32_add", PrimitiveUncheckedU32Add)
      , ("new_cancellation_scope", PrimitiveNewCancellationScope)
      , ("allocate_linear_buffer", PrimitiveAllocateLinearBuffer)
      , ("record_upload_id", PrimitiveRecordUploadId)
      , ("consume_begin_policy_evidence", PrimitiveConsumeBeginPolicyEvidence)
      , ("use", PrimitiveUse)
      , ("inspect", PrimitiveInspect)
      , ("authorize_store", PrimitiveAuthorizeStore)
      , ("delegate", PrimitiveDelegate)
      , ("continue_with_common_state", PrimitiveContinueCommonState)
      , ("handle_payload", PrimitiveHandlePayload)
      ]
  , surfaceTypeAliases = Map.fromList
      [ ("Client[Upload]", TyEndpoint clientUploadSession)
      , ("Server[Upload]", TyEndpoint serverUploadSession)
      ]
  }

clientEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
clientEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("session0", endpoint clientUploadSession)
      , ("payload", ownedPayload "payload")
      , ("sha256", unrestricted (TyOpaque "DigestAlgorithm") PlainShape)
      ]
  , surfaceExpectedProvides = Just (TyEndpoint clientUploadSession)
  , surfaceReleaseTransitions = [payloadReleaseTransition]
  }

serverEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
serverEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("session0", endpoint serverUploadSession)
      , ("policyContext", unrestricted (TyOpaqueSorted "PolicyContext" (SortStableId "Policy")) PlainShape)
      , ("serverSupported", unrestricted (TyOpaqueSorted "SupportedVersions" versionSetSort) PlainShape)
      ]
  , surfaceExpectedProvides = Just (TyEndpoint serverUploadSession)
  , surfaceSelectRequirements = uploadSelectRequirements
  , surfaceReceiveExactRequirement = Just beginPolicyProposition
  }

simpleReceiveEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
simpleReceiveEnvironment base = base
  { surfaceInitialBindings = Map.singleton "s0"
      (endpoint (Receive (Name "hello") (TyOpaque "Hello") (End (Outcome "success"))))
  }

wrongOrderEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
wrongOrderEnvironment = simpleReceiveEnvironment

nonexhaustiveOfferEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
nonexhaustiveOfferEnvironment base = base
  { surfaceInitialBindings = Map.singleton "s0" (endpoint (Offer
      [ branch "payload" Nothing (End (Outcome "success"))
      , branch "cancel" Nothing (End (Outcome "cancelled"))
      ]))
  }

legacyRawEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
legacyRawEnvironment base = base
  { surfaceInitialBindings = Map.singleton "s0"
      (endpoint (Receive (Name "raw") (TyFrame (GrammarId "Begin")) (End (Outcome "success"))))
  , surfaceLegacyReceiveFrameRaw = True
  }

parsedValidationBypassEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
parsedValidationBypassEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("raw", unrestricted (TyOpaqueSorted "RawBytes" byteSequenceSort) (FixtureRawShape (FrameId "fixture")))
      , ("s0", endpoint (Receive (Name "body") (TyBytes beginLengthNat) (End (Outcome "success"))))
      ]
  , surfaceReceiveExactRequirement = Just beginPolicyProposition
  }

unrelatedLengthEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
unrelatedLengthEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("begin", unrestricted (TyFrame (GrammarId "Begin")) (recordBegin "begin"))
      , ("beginPolicy", unrestricted (TyValidated "BeginPolicy" (Name "policyContext") (Name "begin")) PlainShape)
      , ("s0", endpoint (Receive (Name "body") (TyBytes (RefNat 4096)) (End (Outcome "success"))))
      ]
  }

incompatibleJoinEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
incompatibleJoinEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("condition", unrestricted TyBool PlainShape)
      , ("s0", endpoint (Select
          [ branch "left" Nothing (End (Outcome "left"))
          , branch "right" Nothing (End (Outcome "right"))
          ]))
      ]
  }

failureReuseEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
failureReuseEnvironment base = base
  { surfaceInitialBindings = Map.singleton "s0"
      (endpoint (Receive (Name "begin") (TyFrame (GrammarId "Begin")) (End (Outcome "success"))))
  , surfaceLegacyReceiveFrameRaw = True
  }

prematureAcceptanceEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
prematureAcceptanceEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("begin", unrestricted (TyFrame (GrammarId "Begin")) (recordBegin "begin"))
      , ("beginPolicy", unrestricted (TyValidated "BeginPolicy" (Name "policyContext") (Name "begin")) PlainShape)
      , ("s0", endpoint (Receive (Name "body") (TyBytes beginLengthNat)
          (Select [branch "accepted" (Just (Name "id", TyOpaque "UploadId")) (End (Outcome "success"))])))
      ]
  , surfaceReceiveExactRequirement = Just beginPolicyProposition
  , surfaceSelectRequirements = Map.singleton "accepted" [digestMatchesProposition]
  }

pendingCommitEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
pendingCommitEnvironment base = base
  { surfaceInitialBindings = Map.singleton "s0" (endpoint serverUploadSession)
  }

pendingDropEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
pendingDropEnvironment = pendingCommitEnvironment

stalePolicyEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
stalePolicyEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("begin", unrestricted (TyFrame (GrammarId "Begin")) (recordBegin "begin"))
      , ("oldPolicy", unrestricted (TyValidated "BeginPolicy" (Name "kappa1") (Name "begin")) PlainShape)
      , ("session", endpoint (Select [branch "proceed" Nothing (End (Outcome "success"))]))
      ]
  , surfaceSelectRequirements = Map.singleton "proceed"
      [Atom "BeginPolicy" [RefVar (Name "kappa2"), RefVar (Name "begin")]]
  }

opaqueProofEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
opaqueProofEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("begin", unrestricted (TyFrame (GrammarId "Begin")) (recordBegin "begin"))
      , ("payload", InitialBinding Linear
          (TyOpaqueSorted "OwnedPayload" (SortOpaque "OwnedPayload"))
          (OwnedBytesShape (RefNat 0)))
      ]
  }

labelProofEnvironment :: SurfaceEnvironment -> SurfaceEnvironment
labelProofEnvironment base = base
  { surfaceInitialBindings = Map.fromList
      [ ("begin", unrestricted (TyFrame (GrammarId "Begin")) (recordBegin "begin"))
      , ("session", endpoint (Offer
          [ branch "proceed" Nothing (End (Outcome "success"))
          , branch "reject" (Just (Name "reason", TyOpaque "Reason")) (End (Outcome "failure"))
          ]))
      ]
  }

uploadSelectRequirements :: Map.Map Text [Proposition]
uploadSelectRequirements = Map.fromList
  [ ("unsupported", [helloPolicyProposition, Disjoint serverSupportedTerm helloVersionsTerm])
  , ("version", [helloPolicyProposition])
  , ("proceed", [beginPolicyProposition])
  , ("accepted", [digestMatchesProposition])
  ]

helloPolicyProposition :: Proposition
helloPolicyProposition = Atom "HelloPolicy"
  [RefVar (Name "policyContext"), RefVar (Name "hello")]

beginPolicyProposition :: Proposition
beginPolicyProposition = Atom "BeginPolicy"
  [RefVar (Name "policyContext"), RefVar (Name "begin")]

digestMatchesProposition :: Proposition
digestMatchesProposition = Atom "DigestMatches"
  [RefVar (Name "begin"), RefOpaque (SortStableId "OwnedBytes") "payload"]

serverSupportedTerm :: RefTerm
serverSupportedTerm = RefVar (Name "serverSupported")

helloVersionsTerm :: RefTerm
helloVersionsTerm = RefField (RefVar (Name "hello")) "versions" versionSetSort

beginLengthUInt :: RefTerm
beginLengthUInt = RefField (RefVar (Name "begin")) "length" (SortUInt 64)

beginLengthNat :: RefTerm
beginLengthNat = RefToNat beginLengthUInt

versionSetSort :: RefSort
versionSetSort = SortFiniteSet (SortUInt 16)

byteSequenceSort :: RefSort
byteSequenceSort = SortFiniteSeq (SortUInt 8)

serverUploadSession :: Session
serverUploadSession =
  Receive (Name "hello") (TyFrame (GrammarId "Hello")) $
    Select
      [ branch "unsupported" Nothing (End (Outcome "failure"))
      , branch "version" (Just (Name "selected", selectedVersionTy)) $
          Receive (Name "begin") (TyFrame (GrammarId "Begin")) $
            Select
              [ branch "reject" (Just (Name "reason", TyOpaque "ValidationFailure[BeginPolicy]"))
                  (End (Outcome "failure"))
              , branch "proceed" Nothing $
                  Offer
                    [ branch "cancel" Nothing (End (Outcome "cancelled"))
                    , branch "payload" Nothing $
                        Receive (Name "body") (TyBytes beginLengthNat) $
                          Select
                            [ branch "rejected" (Just (Name "reason", TyOpaque "DigestFailure"))
                                (End (Outcome "failure"))
                            , branch "accepted" (Just (Name "id", TyOpaque "UploadId"))
                                (End (Outcome "success"))
                            ]
                    ]
              ]
      ]

clientUploadSession :: Session
clientUploadSession = dualSession serverUploadSession

selectedVersionTy :: Ty
selectedVersionTy = TyRefined (Name "v") (TyUInt 16)
  (Member (RefVar (Name "v")) helloVersionsTerm)

branch :: Text -> Maybe (Name, Ty) -> Session -> Branch
branch = Branch

endpoint :: Session -> InitialBinding
endpoint session = InitialBinding Linear (TyEndpoint session) PlainShape

unrestricted :: Ty -> SurfaceShape -> InitialBinding
unrestricted = InitialBinding Unrestricted

ownedPayload :: Text -> InitialBinding
ownedPayload name =
  let lengthUInt = RefField (RefVar (Name name)) "length" (SortUInt 64)
      index = RefToNat lengthUInt
  in InitialBinding Linear (TyBytes index) (OwnedBytesShape index)

payloadReleaseTransition :: ReleaseTransitionContract
payloadReleaseTransition = ReleaseTransitionContract
  { releaseTransitionKey = "upload.payload.release.v1"
  , releaseTransitionOwnerType = initialType (ownedPayload "payload")
  , releaseTransitionRequirements = Set.empty
  , releaseTransitionSemanticAccount = ReleaseSemanticAccount
      { releaseAccountAuthorityRefs = Set.empty
      , releaseAccountEvidenceRefs = Set.empty
      , releaseAccountEffectRefs = Set.empty
      , releaseAccountAssumptionRefs = Set.empty
      , releaseAccountCostRefs = Set.empty
      , releaseAccountSubjectRef = "upload.payload"
      }
  , releaseTransitionOutcome = ReleaseContinuesUnit
  , releaseTransitionResidue = ReleaseConsumesOwner
  }

recordBegin :: Text -> SurfaceShape
recordBegin name = RecordShape "Begin" (Map.fromList
  [ ("length", FieldInfo
      (TyUInt 64)
      (SortUInt 64)
      (Just (RefField (RefVar (Name name)) "length" (SortUInt 64))))
  ])

fileName :: FilePath -> FilePath
fileName = reverse . takeWhile (/= '/') . reverse
