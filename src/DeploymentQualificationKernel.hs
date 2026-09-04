module DeploymentQualificationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideDeploymentQualificationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool
decideDeploymentQualificationByFacts topologyIdentityValid linksWellFormed claimDomainsTotal claimDomainsSound artifactExact policyExact topologyExact claimSetExact identityValidFact qualificationCurrent everySelectedDomainHasEvidence noExtraDomainBinding compositionEvidenceValid =
  andb topologyIdentityValid
    (andb linksWellFormed
      (andb claimDomainsTotal
        (andb claimDomainsSound
          (andb artifactExact
            (andb policyExact
              (andb topologyExact
                (andb claimSetExact
                  (andb identityValidFact
                    (andb qualificationCurrent
                      (andb everySelectedDomainHasEvidence
                        (andb noExtraDomainBinding compositionEvidenceValid)))))))))))

decideDeploymentQualificationAvailableByFacts :: Prelude.Bool -> Prelude.Bool
                                                 -> Prelude.Bool
decideDeploymentQualificationAvailableByFacts =
  andb
