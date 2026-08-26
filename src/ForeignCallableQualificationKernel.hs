module ForeignCallableQualificationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

data List a =
   Nil
 | Cons a (List a)

qualificationBits :: (a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool) -> (a1 ->
                     Prelude.Bool) -> (a1 -> Prelude.Bool) -> (a1 ->
                     Prelude.Bool) -> (a1 -> Prelude.Bool) -> (a1 ->
                     Prelude.Bool) -> a1 -> List Prelude.Bool
qualificationBits artifactMatches surfaceMatches hasAbiEvidence hasResourceLifecycleEvidence hasEffectConfinementEvidence hasAuthorityConfinementEvidence hasFailureBehaviorEvidence qualification =
  Cons (artifactMatches qualification) (Cons (surfaceMatches qualification)
    (Cons (hasAbiEvidence qualification) (Cons
    (hasResourceLifecycleEvidence qualification) (Cons
    (hasEffectConfinementEvidence qualification) (Cons
    (hasAuthorityConfinementEvidence qualification) (Cons
    (hasFailureBehaviorEvidence qualification) Nil))))))

allQualificationBitsb :: (List Prelude.Bool) -> Prelude.Bool
allQualificationBitsb bits =
  case bits of {
   Nil -> Prelude.True;
   Cons bit rest -> andb bit (allQualificationBitsb rest)}

decideForeignQualification :: (Prelude.Maybe a1) -> (a1 -> Prelude.Bool) ->
                              (a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool) ->
                              (a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool) ->
                              (a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool) ->
                              Prelude.Bool
decideForeignQualification maybeQualification artifactMatches surfaceMatches hasAbiEvidence hasResourceLifecycleEvidence hasEffectConfinementEvidence hasAuthorityConfinementEvidence hasFailureBehaviorEvidence =
  case maybeQualification of {
   Prelude.Just qualification ->
    allQualificationBitsb
      (qualificationBits artifactMatches surfaceMatches hasAbiEvidence
        hasResourceLifecycleEvidence hasEffectConfinementEvidence
        hasAuthorityConfinementEvidence hasFailureBehaviorEvidence
        qualification);
   Prelude.Nothing -> Prelude.False}

