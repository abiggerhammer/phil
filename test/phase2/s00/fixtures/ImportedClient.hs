{-# LANGUAGE CPP #-}

module ImportedClient (attempt) where

import Phil.Experimental.Bytes8.Source

#if defined(FORGE_CONSTRUCTOR)
attempt :: BodyObservation -> CheckedBody
attempt = CheckedBody
#elif defined(UPDATE_SEALED)
attempt :: CheckedBody -> CheckedBody
attempt body = body {bodyCheckpoints = []}
#elif defined(UPGRADE_REPORT)
attempt :: BodyObservation -> Bool
attempt report = either (const False) (const True) (requireContractAuthority report)
#elif defined(FORGE_CONTRACT)
attempt :: CheckedBody -> Bool
attempt body =
  either (const False) (const True)
    (requireContractAuthority body ("C", "forged-revision", "wrong-environment", "wrong-instance", True))
#else
attempt :: CheckedBody -> Bool
attempt = either (const False) (const True) . requireContractAuthority
#endif
