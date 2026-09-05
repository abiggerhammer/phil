module SteveProviderQualificationWitnessKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideSteveProviderQualificationWitnessByFacts :: Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool ->
                                                  Prelude.Bool
decideSteveProviderQualificationWitnessByFacts bothAdmitted digestSubjectExact digestObservationMapped digestBorrowPreserved blobBorrowAllOutcomes blobWholeLayersPresent noReplaceEnforced partialPublicationForbidden blobAuthorityDispositioned obligationManifestsExact conditionsExplicit =
  andb bothAdmitted
    (andb digestSubjectExact
      (andb digestObservationMapped
        (andb digestBorrowPreserved
          (andb blobBorrowAllOutcomes
            (andb blobWholeLayersPresent
              (andb noReplaceEnforced
                (andb partialPublicationForbidden
                  (andb blobAuthorityDispositioned
                    (andb obligationManifestsExact conditionsExplicit)))))))))

