module ConcurrencyActivationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideActivationBindingExplicitByFacts :: Prelude.Bool -> Prelude.Bool
decideActivationBindingExplicitByFacts bindingExplicit =
  bindingExplicit

decideRestrictedInitialOwnershipByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool
decideRestrictedInitialOwnershipByFacts =
  andb

decideDirectStatefulOwnershipByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool
decideDirectStatefulOwnershipByFacts =
  andb

decideActivationContextByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool
decideActivationContextByFacts populationValid bindingsExplicit bindingProcessesActivated restrictedBindingsExact noInventedRestrictedOwner directStatefulBindingsExact noInventedDirectStatefulOwner =
  andb populationValid
    (andb bindingsExplicit
      (andb bindingProcessesActivated
        (andb restrictedBindingsExact
          (andb noInventedRestrictedOwner
            (andb directStatefulBindingsExact noInventedDirectStatefulOwner)))))

decideParticipantClassificationByFacts :: Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool -> Prelude.Bool ->
                                          Prelude.Bool
decideParticipantClassificationByFacts classificationExact internalParticipantsActivated internalParticipantsStatic noEmptyRole =
  andb classificationExact
    (andb internalParticipantsActivated
      (andb internalParticipantsStatic noEmptyRole))

decideCertifiedConcurrencyActivationByFacts :: Prelude.Bool -> Prelude.Bool
                                               -> Prelude.Bool
decideCertifiedConcurrencyActivationByFacts =
  andb

