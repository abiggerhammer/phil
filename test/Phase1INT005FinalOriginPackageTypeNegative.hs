-- Intentionally uncompilable external-client control. The CI script checks
-- that the failure names the opaque AcceptedVerifiedFinalOrigin type.
module Main (main) where

import Phil.Assurance.Types (AssuranceLedger)
import Phil.Verification.CertifiedRelease (CertifiedReleaseArtifact)
import Phil.Verification.ReleasePackage
  ( ReleasePackageError
  , VerifiedOriginReleasePackage
  , buildCertifiedReleasePackage
  )

legacyBypass
  :: AssuranceLedger -> CertifiedReleaseArtifact
  -> Either ReleasePackageError VerifiedOriginReleasePackage
legacyBypass = buildCertifiedReleasePackage

main :: IO ()
main = pure ()
