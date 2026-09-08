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


verification = "src/Phil/Verification.hs"
replace_once(
    verification,
    '''  , buildVerificationObligationGraph
  , RuntimeClosureProposal (..)
''',
    '''  , buildVerificationObligationGraph
  , buildVerificationRevisionGraph
  , RuntimeClosureProposal (..)
''')
replace_once(
    verification,
    '''  , digestText
  , revisionFromCoreObligation
''',
    '''  , deriveRevisionId
  , digestText
  , revisionFromCoreObligation
''')
replace_once(
    verification,
    '''data VerificationGraphError
  = ConflictingObligationInputs ObligationId
  | UnknownObligationDependency ObligationId ObligationId
  | UnknownCertificationScopeObligation ObligationId
  | CyclicObligationDependencies (Set ObligationId)
  deriving (Eq, Show)
''',
    '''data VerificationGraphError
  = ConflictingObligationInputs ObligationId
  | UnknownObligationDependency ObligationId ObligationId
  | UnknownCertificationScopeObligation ObligationId
  | CyclicObligationDependencies (Set ObligationId)
  | ConflictingObligationRevisions RevisionId
  | InvalidObligationRevisionIdentity RevisionId RevisionId
  | UnknownRevisionDependency RevisionId RevisionId
  | UnknownCertificationScopeRevision RevisionId
  | CyclicRevisionDependencies (Set RevisionId)
  deriving (Eq, Show)
''')
replace_once(
    verification,
    '''  Right VerificationObligationGraph
    { verificationGraphRevision = graphDigest
    , verificationGraphNodes = nodes
    , verificationGraphDependencies = edges
    , verificationGraphCertificationScope = scope
    }

insertCanonicalInput
''',
    '''  Right VerificationObligationGraph
    { verificationGraphRevision = graphDigest
    , verificationGraphNodes = nodes
    , verificationGraphDependencies = edges
    , verificationGraphCertificationScope = scope
    }

-- | Build the same canonical VerificationObligationGraph from already competent
-- exact ObligationRevision records.  This is the bridge used when an assurance
-- ledger is the authoritative carrier of obligation identity: revision identity,
-- provenance dependencies, scope, and graph revision are still checked and
-- canonicalized rather than reconstructed from presentation or Haskell object
-- identity.
buildVerificationRevisionGraph
  :: [ObligationRevision]
  -> Set RevisionId
  -> Either VerificationGraphError VerificationObligationGraph
buildVerificationRevisionGraph rawRevisions requestedScope = do
  revisions <- foldM insertExactRevision Map.empty rawRevisions
  validateRevisionScope revisions requestedScope
  validateRevisionDependencies revisions
  case cyclicRevisionRegion revisions of
    Nothing -> pure ()
    Just region -> Left (CyclicRevisionDependencies region)
  let edges = Set.fromList
        [ (revisionKey, dependency)
        | (revisionKey, revision) <- Map.toAscList revisions
        , dependency <- revisionGeneratedFrom revision
        ]
      graphDigest = digestText (renderGraphIdentity revisions edges requestedScope)
  Right VerificationObligationGraph
    { verificationGraphRevision = graphDigest
    , verificationGraphNodes = revisions
    , verificationGraphDependencies = edges
    , verificationGraphCertificationScope = requestedScope
    }

insertExactRevision
  :: Map RevisionId ObligationRevision
  -> ObligationRevision
  -> Either VerificationGraphError (Map RevisionId ObligationRevision)
insertExactRevision revisions revision = do
  let actual = revisionId revision
      expected = deriveRevisionId revision
  if actual == expected
    then Right ()
    else Left (InvalidObligationRevisionIdentity expected actual)
  case Map.lookup actual revisions of
    Nothing -> Right (Map.insert actual revision revisions)
    Just existing
      | existing == revision -> Right revisions
      | otherwise -> Left (ConflictingObligationRevisions actual)

validateRevisionScope
  :: Map RevisionId ObligationRevision
  -> Set RevisionId
  -> Either VerificationGraphError ()
validateRevisionScope revisions requestedScope =
  case Set.lookupMin (requestedScope `Set.difference` Map.keysSet revisions) of
    Nothing -> Right ()
    Just missing -> Left (UnknownCertificationScopeRevision missing)

validateRevisionDependencies
  :: Map RevisionId ObligationRevision
  -> Either VerificationGraphError ()
validateRevisionDependencies revisions = mapM_ verifyRevision
  (Map.toAscList revisions)
  where
    known = Map.keysSet revisions
    verifyRevision (revisionKey, revision) =
      case Set.lookupMin
          (Set.fromList (revisionGeneratedFrom revision) `Set.difference` known) of
        Nothing -> Right ()
        Just missing -> Left (UnknownRevisionDependency revisionKey missing)

cyclicRevisionRegion
  :: Map RevisionId ObligationRevision
  -> Maybe (Set RevisionId)
cyclicRevisionRegion revisions = go dependencyMap
  where
    dependencyMap = Map.map (Set.fromList . revisionGeneratedFrom) revisions

    go remaining
      | Map.null remaining = Nothing
      | null roots = Just (Map.keysSet remaining)
      | otherwise = go $ Map.map (`Set.difference` rootSet) withoutRoots
      where
        roots =
          [ revisionKey
          | (revisionKey, dependencies) <- Map.toAscList remaining
          , Set.null dependencies
          ]
        rootSet = Set.fromList roots
        withoutRoots = foldr Map.delete remaining roots

insertCanonicalInput
''')

bundle = "src/Phil/Verification/Bundle.hs"
replace_once(
    bundle,
    '''  , VerificationBundleError (..)
  , buildVerificationBundle
  ) where
''',
    '''  , VerificationBundleError (..)
  , buildVerificationBundle
  , verificationBundleArchitectureDigest
  ) where
''')
replace_once(
    bundle,
    '''validateSourceRevision :: Digest -> Either VerificationBundleError ()
''',
    '''-- | Canonical architecture identity carried by a VerificationBundle.
-- Manifest closure compares the caller's build context against this digest so
-- an unrelated Architecture cannot be substituted after source verification.
verificationBundleArchitectureDigest :: VerificationBundle -> Digest
verificationBundleArchitectureDigest bundle = digestText (Text.intercalate "\\n"
  [ "verification-bundle-architecture-v1"
  , "declarations=" <> Text.intercalate ","
      (map renderDeclaration
        (Set.toAscList (verificationBundleDeclarations bundle)))
  , "instances=" <> Text.intercalate ","
      (map renderInstance
        (Set.toAscList (verificationBundleArchitectureInstances bundle)))
  , "realizations=" <> Text.intercalate ","
      (map renderRealization
        (Set.toAscList (verificationBundleArchitectureRealizations bundle)))
  ])
  where
    renderDeclaration identity = Text.intercalate "@"
      [ unDeclarationKey (identityDeclarationKey identity)
      , unInterfaceRevision (identityInterfaceRevision identity)
      , unDefinitionRevision (identityDefinitionRevision identity)
      ]

    renderInstance identity = Text.intercalate "@"
      [ unInstanceKey (identityInstanceKey identity)
      , unInstanceRevision (identityInstanceRevision identity)
      ]

    renderRealization identity =
      unRealizationRevision (identityRealizationRevision identity)

validateSourceRevision :: Digest -> Either VerificationBundleError ()
''')

closure = "src/Phil/Verification/ManifestClosure.hs"
replace_once(
    closure,
    '''  ( AcceptedEvidenceReference (..)
  , VerificationBundle (..)
  )
''',
    '''  ( AcceptedEvidenceReference (..)
  , VerificationBundle (..)
  , verificationBundleArchitectureDigest
  )
''')
replace_once(
    closure,
    '''data ManifestClosureError
  = ManifestClosurePolicyRevisionMismatch AssurancePolicyRevision AssurancePolicyRevision
  | ManifestClosureExpectedObligationsMismatch (Set RevisionId) (Set RevisionId)
''',
    '''data ManifestClosureError
  = ManifestClosurePolicyRevisionMismatch AssurancePolicyRevision AssurancePolicyRevision
  | ManifestClosureArchitectureDigestMismatch Digest Digest
  | ManifestClosureExpectedObligationsMismatch (Set RevisionId) (Set RevisionId)
''')
replace_once(
    closure,
    '''closeVerificationBundle bundle policy context ledger selection = do
  verifyPolicyRevision
  verifyContextObligations
''',
    '''closeVerificationBundle bundle policy context ledger selection = do
  verifyPolicyRevision
  verifyArchitectureDigest
  verifyContextObligations
''')
replace_once(
    closure,
    '''    verifyPolicyRevision =
      let bundleRevision = verificationBundlePolicyRevision bundle
          selectedRevision = applicationAssurancePolicyRevision policy
      in if bundleRevision == selectedRevision
          then Right ()
          else Left
            (ManifestClosurePolicyRevisionMismatch bundleRevision selectedRevision)

    verifyContextObligations =
''',
    '''    verifyPolicyRevision =
      let bundleRevision = verificationBundlePolicyRevision bundle
          selectedRevision = applicationAssurancePolicyRevision policy
      in if bundleRevision == selectedRevision
          then Right ()
          else Left
            (ManifestClosurePolicyRevisionMismatch bundleRevision selectedRevision)

    verifyArchitectureDigest =
      let expected = verificationBundleArchitectureDigest bundle
          actual = verificationArchitectureDigest context
      in if actual == expected
          then Right ()
          else Left (ManifestClosureArchitectureDigestMismatch expected actual)

    verifyContextObligations =
''')
