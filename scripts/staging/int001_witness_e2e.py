from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    file_path = Path(path)
    text = file_path.read_text()
    if new in text:
        return
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected one staging target, found {count}")
    file_path.write_text(text.replace(old, new, 1))


policy_path = "src/Phil/Compiler/SourceCorePolicy.hs"
replace_once(
    policy_path,
    '''data SourceBranchDisposition = SourceBranchDisposition
  { sourceBranchCoreBlock :: Text
  , sourceBranchTargets :: Map Text Text
  }
  deriving (Eq, Ord, Show)
''',
    '''data SourceBranchDisposition
  = SourceBranchDisposition Text (Map Text Text)
  -- | A source `primary or fail` branch whose fallback is absorbed by the
  -- selected framed-receive ABI: receive_frame either returns a complete frame
  -- or does not return normally.  The Core block must still contain the exact
  -- receive-frame operation, so this cannot erase an arbitrary source branch.
  | SourceBranchReceiveFrameNonreturningFallback Text
  deriving (Eq, Ord, Show)
''')

replace_once(
    policy_path,
    '''verifyBranch branchSites program (site, disposition) = do
  sourceLabels <- maybe (Left (SourceCoreBranchSiteMissing site)) Right
    (Map.lookup site branchSites)
  let expectedLabels = Map.keysSet (sourceBranchTargets disposition)
  if sourceLabels == expectedLabels
    then Right ()
    else Left (SourceCoreBranchLabelMismatch site sourceLabels expectedLabels)
  function <- coreFunction site program
  blockValue <- maybe
    (Left (SourceCoreBranchBlockMissing site (sourceBranchCoreBlock disposition)))
    Right
    (Map.lookup (sourceBranchCoreBlock disposition) (coreFunctionBlocks function))
  let expectedTargets = sourceBranchTargets disposition
  case coreBlockTerminator blockValue of
    CoreSystemsRuntimeChoice _ _ _ actualTargets
      | actualTargets == expectedTargets -> Right ()
      | otherwise -> Left (SourceCoreBranchTargetsMismatch site expectedTargets actualTargets)
    CoreSystemsBranch _ yesTarget noTarget ->
      compareUnlabeledTargets site expectedTargets [yesTarget, noTarget]
    CoreSystemsRuntimeCheck _ _ yesTarget noTarget ->
      compareUnlabeledTargets site expectedTargets [yesTarget, noTarget]
    _ -> Left (SourceCoreBranchNotNormalized site (sourceBranchCoreBlock disposition))
''',
    '''verifyBranch branchSites program (site, disposition) = do
  sourceLabels <- maybe (Left (SourceCoreBranchSiteMissing site)) Right
    (Map.lookup site branchSites)
  case disposition of
    SourceBranchDisposition blockName expectedTargets -> do
      let expectedLabels = Map.keysSet expectedTargets
      if sourceLabels == expectedLabels
        then Right ()
        else Left (SourceCoreBranchLabelMismatch site sourceLabels expectedLabels)
      function <- coreFunction site program
      blockValue <- maybe
        (Left (SourceCoreBranchBlockMissing site blockName))
        Right
        (Map.lookup blockName (coreFunctionBlocks function))
      case coreBlockTerminator blockValue of
        CoreSystemsRuntimeChoice _ _ _ actualTargets
          | actualTargets == expectedTargets -> Right ()
          | otherwise -> Left
              (SourceCoreBranchTargetsMismatch site expectedTargets actualTargets)
        CoreSystemsBranch _ yesTarget noTarget ->
          compareUnlabeledTargets site expectedTargets [yesTarget, noTarget]
        CoreSystemsRuntimeCheck _ _ yesTarget noTarget ->
          compareUnlabeledTargets site expectedTargets [yesTarget, noTarget]
        CoreSystemsRecognize _ _ _ successTarget failureTarget ->
          compareUnlabeledTargets site expectedTargets [successTarget, failureTarget]
        CoreSystemsReceiveExact _ _ _ _ successTarget failureTarget ->
          compareUnlabeledTargets site expectedTargets [successTarget, failureTarget]
        CoreSystemsStore _ _ _ successTarget failureTarget ->
          compareUnlabeledTargets site expectedTargets [successTarget, failureTarget]
        _ -> Left (SourceCoreBranchNotNormalized site blockName)
    SourceBranchReceiveFrameNonreturningFallback blockName -> do
      let expectedLabels = Set.fromList ["primary", "fallback"]
      if sourceLabels == expectedLabels
        then Right ()
        else Left (SourceCoreBranchLabelMismatch site sourceLabels expectedLabels)
      function <- coreFunction site program
      blockValue <- maybe
        (Left (SourceCoreBranchBlockMissing site blockName))
        Right
        (Map.lookup blockName (coreFunctionBlocks function))
      if any isReceiveFrame (coreBlockOperations blockValue)
        then Right ()
        else Left (SourceCoreBranchNotNormalized site blockName)
  where
    isReceiveFrame operation = case operation of
      CoreReceiveFrame {} -> True
      _ -> False
''')

witness_path = "src/Phil/Examples/Phase1/SystemsWitnesses.hs"
replace_once(
    witness_path,
    '''      [ value "client.transport" CoreTransportHandle (Just "transport.client")
      , value "client.payload" (CoreOwnedBuffer "Bytes[payload.length]")
          (Just "payload.client")
      , value "client.version_branch" (CoreRuntimeScalar "Bool") Nothing
      , value "client.begin_branch" (CoreRuntimeScalar "Bool") Nothing
      , value "client.should_cancel" (CoreRuntimeScalar "Bool") Nothing
      , value "client.result_branch" (CoreRuntimeScalar "Bool") Nothing
      ]
''',
    '''      [ value "client.transport" CoreTransportHandle (Just "transport.client")
      , value "client.payload" (CoreOwnedBuffer "Bytes[payload.length]")
          (Just "payload.client")
      , value "client.payload_view" (CoreBorrowedValue "client.payload") Nothing
      , value "client.supported_versions" (CoreRuntimeScalar "VersionSet") Nothing
      , value "client.declared_digest" (CoreRuntimeScalar "SHA256Digest") Nothing
      , value "client.upload_id" (CoreRuntimeScalar "UploadId") Nothing
      , value "client.version_branch" (CoreRuntimeScalar "Bool") Nothing
      , value "client.begin_branch" (CoreRuntimeScalar "Bool") Nothing
      , value "client.should_cancel" (CoreRuntimeScalar "Bool") Nothing
      , value "client.result_branch" (CoreRuntimeScalar "Bool") Nothing
      ]
''')

replace_once(
    witness_path,
    '''      [ block "client.entry"
          [ CoreRuntimeCall "semantic-call" "send Hello"
              ["client.transport"] [] Nothing
          , CoreRuntimeCall "semantic-call" "receive version/unsupported label"
              ["client.transport"] ["client.version_branch"] Nothing
          ]
''',
    '''      [ block "client.entry"
          [ CoreRuntimeCall "semantic-call" "supported_versions"
              [] ["client.supported_versions"] Nothing
          , CoreRuntimeCall "semantic-call" "send Hello"
              ["client.transport"] [] Nothing
          , CoreRuntimeCall "semantic-call" "receive version/unsupported label"
              ["client.transport"] ["client.version_branch"] Nothing
          ]
''')

replace_once(
    witness_path,
    '''      , block "client.version"
          [ CoreRuntimeCall "semantic-call" "send Begin"
              ["client.transport"] [] Nothing
          , CoreRuntimeCall "semantic-call" "receive proceed/reject label"
              ["client.transport"] ["client.begin_branch"] Nothing
          ]
''',
    '''      , block "client.version"
          [ CoreBorrowView "payload-borrow" "client.payload_view" "client.payload"
          , CoreRuntimeCall "semantic-call" "sha256"
              ["client.payload_view"] ["client.declared_digest"] Nothing
          , CoreRuntimeCall "semantic-call" "send Begin"
              ["client.transport"] [] Nothing
          , CoreRuntimeCall "semantic-call" "receive proceed/reject label"
              ["client.transport"] ["client.begin_branch"] Nothing
          ]
''')

replace_once(
    witness_path,
    '''      , block "client.accepted" [] (CoreSystemsEnd "success")
      , block "client.rejected" [] (CoreSystemsEnd "failure")
''',
    '''      , block "client.accepted"
          [ CoreRuntimeCall "semantic-call" "record_upload_id"
              ["client.upload_id"] [] Nothing
          ]
          (CoreSystemsEnd "success")
      , block "client.rejected" [] (CoreSystemsEnd "failure")
''')

replace_once(
    witness_path,
    '''      , block "get.ok" [CoreTrace "steve.get.commit"] (CoreSystemsEnd "success")
      , block "get.not-found" [] (CoreSystemsEnd "not-found")
      , block "get.integrity-failure" [] (CoreSystemsEnd "integrity-failure")
      , block "get.failure" [] (CoreSystemsEnd "storage-failure")
''',
    '''      , block "get.ok"
          [ CoreReleaseOwner "cleanup" "get.bytes"
          , CoreTrace "steve.get.commit"
          ]
          (CoreSystemsEnd "success")
      , block "get.not-found" [] (CoreSystemsEnd "not-found")
      , block "get.integrity-failure"
          [CoreReleaseOwner "cleanup" "get.bytes"]
          (CoreSystemsEnd "integrity-failure")
      , block "get.failure" [] (CoreSystemsEnd "storage-failure")
''')

replace_once(
    witness_path,
    '''  , genericContextDecisions = Map.singleton "host-abi"
      GenericDecisionSpec
        { genericDecisionId = steveHostAbiDecisionId
        , genericDecisionSourceRepresentation =
            "Steve BlobProvider semantic byte slice"
        , genericDecisionTargetRepresentation =
            "host pointer/length byte-slice ABI"
        , genericDecisionSemanticEntities = ["steve.blob.byte-slice"]
        , genericDecisionAction = ChooseLayout
        , genericDecisionCostClass = Just TargetRequired
        , genericDecisionCostShape =
            emptyCostShape { costFrequency = Just "per provider ABI realization" }
        , genericDecisionTargetPreconditions = [steveHostAbiTargetPrecondition]
        , genericDecisionAssumptions = []
        , genericDecisionDerivedObligations = [steveHostAbiObligationRevision]
        }
''',
    '''  , genericContextDecisions = Map.fromList
      [ ("host-abi", GenericDecisionSpec
          { genericDecisionId = steveHostAbiDecisionId
          , genericDecisionSourceRepresentation =
              "Steve BlobProvider semantic byte slice"
          , genericDecisionTargetRepresentation =
              "host pointer/length byte-slice ABI"
          , genericDecisionSemanticEntities = ["steve.blob.byte-slice"]
          , genericDecisionAction = ChooseLayout
          , genericDecisionCostClass = Just TargetRequired
          , genericDecisionCostShape =
              emptyCostShape { costFrequency = Just "per provider ABI realization" }
          , genericDecisionTargetPreconditions = [steveHostAbiTargetPrecondition]
          , genericDecisionAssumptions = []
          , genericDecisionDerivedObligations = [steveHostAbiObligationRevision]
          })
      , ordinaryDecision "cleanup" "lower.resource.cleanup" Cleanup
      ]
''')
