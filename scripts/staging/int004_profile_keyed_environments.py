from pathlib import Path

phase0_path = Path('src/Phil/Surface/Phase0.hs')
phase0 = phase0_path.read_text()

old_export = '''  ( FixtureExpectation (..)
  , phase0EnvironmentFor
  , phase0ExpectationFor
'''
new_export = '''  ( FixtureExpectation (..)
  , phase0EnvironmentFor
  , phase0EnvironmentProfile
  , phase0ExpectationFor
'''
if new_export not in phase0:
    if old_export not in phase0:
        raise SystemExit('Phase0 export list does not match expected form')
    phase0 = phase0.replace(old_export, new_export, 1)

old_environment = '''phase0EnvironmentFor :: FilePath -> Either Text SurfaceEnvironment
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
'''
new_environment = '''phase0EnvironmentFor :: FilePath -> Either Text SurfaceEnvironment
phase0EnvironmentFor path = case fileName path of
  "client.phil" -> phase0EnvironmentProfile "phase0.client"
  "server.phil" -> phase0EnvironmentProfile "phase0.server"
  "01-reuse-consumed-endpoint.phil" -> phase0EnvironmentProfile "phase0.simple-receive"
  "02-drop-live-endpoint.phil" -> phase0EnvironmentProfile "phase0.simple-receive"
  "03-wrong-protocol-order.phil" -> phase0EnvironmentProfile "phase0.wrong-order"
  "04-nonexhaustive-offer.phil" -> phase0EnvironmentProfile "phase0.nonexhaustive-offer"
  "05-raw-field-access.phil" -> phase0EnvironmentProfile "phase0.legacy-raw"
  "06-parsed-used-as-validated.phil" -> phase0EnvironmentProfile "phase0.parsed-validation-bypass"
  "07-unrelated-payload-length.phil" -> phase0EnvironmentProfile "phase0.unrelated-length"
  "08-incompatible-branch-join.phil" -> phase0EnvironmentProfile "phase0.incompatible-join"
  "09-continue-after-fatal-recognition-failure.phil" -> phase0EnvironmentProfile "phase0.failure-reuse"
  "10-accept-before-digest-check.phil" -> phase0EnvironmentProfile "phase0.premature-acceptance"
  "11-copy-authority-capability.phil" -> phase0EnvironmentProfile "phase0.common"
  "12-ignore-cancellation-cleanup.phil" -> phase0EnvironmentProfile "phase0.common"
  "13-commit-unrelated-parsed.phil" -> phase0EnvironmentProfile "phase0.pending-commit"
  "14-copy-owned-payload.phil" -> phase0EnvironmentProfile "phase0.common"
  "15-drop-pending-receive.phil" -> phase0EnvironmentProfile "phase0.pending-drop"
  "16-escape-shared-loan.phil" -> phase0EnvironmentProfile "phase0.common"
  "17-use-evidence-wrong-context.phil" -> phase0EnvironmentProfile "phase0.stale-policy"
  "18-prove-opaque-digest.phil" -> phase0EnvironmentProfile "phase0.opaque-proof"
  "19-label-does-not-transfer-proof.phil" -> phase0EnvironmentProfile "phase0.label-proof"
  "20-unchecked-wraparound-proof.phil" -> phase0EnvironmentProfile "phase0.common"
  _ -> Left ("no Phase 0 checking environment for " <> Text.pack path)

-- | Stable semantic environment profiles for portable conformance fixtures.
-- Fixture paths are deliberately not inputs: a portable manifest selects a
-- profile by semantic name, and this resolver materializes the corresponding
-- checker boundary.  The legacy filename adapter above is retained only for
-- pre-INT-004 callers while they migrate.
phase0EnvironmentProfile :: Text -> Either Text SurfaceEnvironment
phase0EnvironmentProfile profile = do
  staticContext <- phase0StaticContext
  let base = commonEnvironment staticContext
  case profile of
    "phase0.common" -> Right base
    "phase0.client" -> Right (clientEnvironment base)
    "phase0.server" -> Right (serverEnvironment base)
    "phase0.simple-receive" -> Right (simpleReceiveEnvironment base)
    "phase0.wrong-order" -> Right (wrongOrderEnvironment base)
    "phase0.nonexhaustive-offer" -> Right (nonexhaustiveOfferEnvironment base)
    "phase0.legacy-raw" -> Right (legacyRawEnvironment base)
    "phase0.parsed-validation-bypass" -> Right (parsedValidationBypassEnvironment base)
    "phase0.unrelated-length" -> Right (unrelatedLengthEnvironment base)
    "phase0.incompatible-join" -> Right (incompatibleJoinEnvironment base)
    "phase0.failure-reuse" -> Right (failureReuseEnvironment base)
    "phase0.premature-acceptance" -> Right (prematureAcceptanceEnvironment base)
    "phase0.pending-commit" -> Right (pendingCommitEnvironment base)
    "phase0.pending-drop" -> Right (pendingDropEnvironment base)
    "phase0.stale-policy" -> Right (stalePolicyEnvironment base)
    "phase0.opaque-proof" -> Right (opaqueProofEnvironment base)
    "phase0.label-proof" -> Right (labelProofEnvironment base)
    _ -> Left ("unknown Phase 0 environment profile " <> profile)
'''
if new_environment not in phase0:
    if old_environment not in phase0:
        raise SystemExit('Phase0 environment resolver does not match expected form')
    phase0 = phase0.replace(old_environment, new_environment, 1)

phase0_path.write_text(phase0)

test_path = Path('test/Phase1INT004PortableNegativeManifestMain.hs')
test = test_path.read_text()
old_import = '''import Phil.Surface.Phase0
  ( FixtureExpectation (..)
  , phase0EnvironmentFor
  , phase0ExpectationFor
  )
'''
new_import = '''import Phil.Surface.Phase0
  ( FixtureExpectation (..)
  , phase0EnvironmentProfile
  , phase0ExpectationFor
  )
'''
if new_import not in test:
    if old_import not in test:
        raise SystemExit('portable negative test Phase0 import does not match expected form')
    test = test.replace(old_import, new_import, 1)

old_call = '''  case phase0EnvironmentFor path of
    Left detail -> failCase ("environment adapter failed: " <> Text.unpack detail)
'''
new_call = '''  case phase0EnvironmentProfile (negativeCaseEnvironmentProfile negativeCase) of
    Left detail -> failCase ("environment profile failed: " <> Text.unpack detail)
'''
if new_call not in test:
    if old_call not in test:
        raise SystemExit('portable negative test environment call does not match expected form')
    test = test.replace(old_call, new_call, 1)

test_path.write_text(test)

readme_path = Path('test/fixtures/phase1-negative/README.md')
readme = readme_path.read_text()
old_readme = '''The current first slice intentionally keeps `Phil.Surface.Phase0.phase0EnvironmentFor` only as a temporary Haskell adapter for the named environment profiles and checks parity with the frozen legacy classification table. The manifest, not the filename table, owns the expected rejection class for the INT-004 replay. A subsequent slice will materialize the environment profiles portably and remove filename dispatch from the replay path.
'''
new_readme = '''The portable replay selects its checker environment by the manifest's stable `environment_profile` field through `Phil.Surface.Phase0.phase0EnvironmentProfile`; fixture filenames are no longer inputs to environment selection. `phase0EnvironmentFor` remains only as a compatibility adapter for legacy callers. The profile implementations are still Haskell-side boundary material in this slice, so INT-004 is not yet complete: later work must make the profile definitions themselves portable and migrate constructor-only Phase-1 negatives.
'''
if new_readme not in readme:
    if old_readme not in readme:
        raise SystemExit('portable negative README does not match expected migration text')
    readme = readme.replace(old_readme, new_readme, 1)
readme_path.write_text(readme)
