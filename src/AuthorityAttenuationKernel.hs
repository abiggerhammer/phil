module AuthorityAttenuationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

decideExplicitAuthorityAttenuation :: Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool -> Prelude.Bool ->
                                      Prelude.Bool
decideExplicitAuthorityAttenuation subjectMatches noWiden witnessSourceMatches witnessTargetMatches witnessSubjectMatches witnessOperationsMatch =
  andb subjectMatches
    (andb noWiden
      (andb witnessSourceMatches
        (andb witnessTargetMatches
          (andb witnessSubjectMatches witnessOperationsMatch))))

decideAuthorityBoundary :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                           Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                           Prelude.Bool
decideAuthorityBoundary subjectMatches noWiden sameContract sameSurface changedContract attenuationWitnessValid =
  andb subjectMatches
    (andb noWiden
      (orb (andb sameContract sameSurface)
        (andb changedContract attenuationWitnessValid)))

decideAuthorityJoin :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                       Prelude.Bool -> Prelude.Bool
decideAuthorityJoin hasContinuingBranch subjectsMatch contractsMatch operationsDoNotWiden =
  andb hasContinuingBranch
    (andb subjectsMatch (andb contractsMatch operationsDoNotWiden))
