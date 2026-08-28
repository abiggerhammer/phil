module AuthorityAttenuationKernel where

import qualified Prelude

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

decideExplicitAuthorityAttenuation :: Bool -> Bool -> Bool -> Bool -> Bool ->
                                      Bool -> Bool
decideExplicitAuthorityAttenuation subjectMatches noWiden witnessSourceMatches witnessTargetMatches witnessSubjectMatches witnessOperationsMatch =
  andb subjectMatches
    (andb noWiden
      (andb witnessSourceMatches
        (andb witnessTargetMatches
          (andb witnessSubjectMatches witnessOperationsMatch))))

decideAuthorityBoundary :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
                           Bool
decideAuthorityBoundary subjectMatches noWiden sameContract sameSurface changedContract attenuationWitnessValid =
  andb subjectMatches
    (andb noWiden
      (orb (andb sameContract sameSurface)
        (andb changedContract attenuationWitnessValid)))

decideAuthorityJoin :: Bool -> Bool -> Bool -> Bool -> Bool
decideAuthorityJoin hasContinuingBranch subjectsMatch contractsMatch operationsDoNotWiden =
  andb hasContinuingBranch
    (andb subjectsMatch (andb contractsMatch operationsDoNotWiden))
