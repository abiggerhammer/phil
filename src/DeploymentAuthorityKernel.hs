module DeploymentAuthorityKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideDeploymentAuthorityPolicyAdmissibleByFacts :: Prelude.Bool ->
                                                    Prelude.Bool ->
                                                    Prelude.Bool ->
                                                    Prelude.Bool ->
                                                    Prelude.Bool
decideDeploymentAuthorityPolicyAdmissibleByFacts policyWellFormed deploymentPolicyExact claimPlanned claimQualified =
  andb policyWellFormed
    (andb deploymentPolicyExact (andb claimPlanned claimQualified))

decideDeploymentAuthorityGrantMatchesByFacts :: Prelude.Bool -> Prelude.Bool
                                                -> Prelude.Bool ->
                                                Prelude.Bool -> Prelude.Bool
                                                -> Prelude.Bool ->
                                                Prelude.Bool -> Prelude.Bool
decideDeploymentAuthorityGrantMatchesByFacts policyExact qualificationExact claimExact actionExact resourceExact validityEndExact contentIdentityValid =
  andb policyExact
    (andb qualificationExact
      (andb claimExact
        (andb actionExact
          (andb resourceExact (andb validityEndExact contentIdentityValid)))))

decideDeploymentAuthorityIssuedByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool
decideDeploymentAuthorityIssuedByFacts qualificationValid policyAdmissible grantMatches grantBeginsAtObservation =
  andb qualificationValid
    (andb policyAdmissible (andb grantMatches grantBeginsAtObservation))

decideDeploymentAuthorityUsableByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool
decideDeploymentAuthorityUsableByFacts qualificationValid policyAdmissible grantMatches grantCurrent =
  andb qualificationValid
    (andb policyAdmissible (andb grantMatches grantCurrent))
