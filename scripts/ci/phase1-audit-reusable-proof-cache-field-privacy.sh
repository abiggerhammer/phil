#!/usr/bin/env bash
# Compile external clients to guard the prepared reusable-evidence boundary.
set -euo pipefail
cd "$(dirname "$0")/../.."
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

# First ensure the entire imported module and public read API compile; a broken
# substrate cannot be mistaken for a successful negative boundary test.
cat > "$scratch/ReadCache.hs" <<'HS'
module ReadCache where

import Phil.Verification.ProofEvidence
  ( ReusableProofEvidence
  , reusableCheckedProofEvidence
  , reusableProofDependencies
  , reusableProofValidityScope
  )

viewChecked = reusableCheckedProofEvidence
viewDependencies = reusableProofDependencies
viewValidityScope = reusableProofValidityScope

allRead :: ReusableProofEvidence -> Bool
allRead token =
  seq (viewChecked token)
    (seq (viewDependencies token)
      (seq (viewValidityScope token) True))
HS
cabal exec -- ghc -isrc -Wall -Werror -fno-code "$scratch/ReadCache.hs"

while read -r field; do
  cat > "$scratch/ForgeCache.hs" <<HS
module ForgeCache where
import Phil.Verification.ProofEvidence
  ( ReusableProofEvidence
  , $field
  )
forge :: ReusableProofEvidence -> ReusableProofEvidence
forge token = token { $field = undefined }
HS
  if cabal exec -- ghc -isrc -fno-code "$scratch/ForgeCache.hs" >"$scratch/output" 2>&1; then
    echo "FAIL: external cache record update unexpectedly compiled ($field)" >&2
    exit 1
  fi
  if ! grep -Fq "$field" "$scratch/output"; then
    echo "FAIL: compilation did not identify the targeted inaccessible label $field" >&2
    cat "$scratch/output" >&2
    exit 1
  fi
  echo "PASS: external cache update rejected ($field)"
done <<'FIELDS'
reusableCheckedProofEvidence
reusableProofDependencies
reusableProofValidityScope
FIELDS

# Run actual producer/checker/preparation/consumer fixtures, not a fake cache
# oracle. In particular: same-context and unrelated edits reuse; dependent,
# scope, revision and declared validity changes fail closed.
cabal exec -- runghc -Wall -Werror -isrc test/Phase1VerificationEvidenceReuseInvalidationMain.hs
