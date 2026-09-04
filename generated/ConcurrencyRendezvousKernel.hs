module ConcurrencyRendezvousKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideRendezvousEndpointFactsByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool
decideRendezvousEndpointFactsByFacts binaryWellFormed senderProgression receiverProgression senderInstanceExact receiverInstanceExact senderRoleExact receiverRoleExact currentSessionsDual successorSessionsDual =
  andb binaryWellFormed
    (andb senderProgression
      (andb receiverProgression
        (andb senderInstanceExact
          (andb receiverInstanceExact
            (andb senderRoleExact
              (andb receiverRoleExact
                (andb currentSessionsDual successorSessionsDual)))))))

decideRendezvousParticipantFactsByFacts :: Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool ->
                                           Prelude.Bool -> Prelude.Bool
decideRendezvousParticipantFactsByFacts classificationValid senderParticipantExact receiverParticipantExact senderRoleOccurrenceExact receiverRoleOccurrenceExact =
  andb classificationValid
    (andb senderParticipantExact
      (andb receiverParticipantExact
        (andb senderRoleOccurrenceExact receiverRoleOccurrenceExact)))

decideRendezvousMessageCoarseFactsByFacts :: Prelude.Bool -> Prelude.Bool ->
                                             Prelude.Bool -> Prelude.Bool ->
                                             Prelude.Bool -> Prelude.Bool ->
                                             Prelude.Bool -> Prelude.Bool
decideRendezvousMessageCoarseFactsByFacts messageAccepted coarseStepValid coarseInstanceExact coarseSenderRoleExact coarseReceiverRoleExact coarseSenderProcessExact coarseReceiverProcessExact =
  andb messageAccepted
    (andb coarseStepValid
      (andb coarseInstanceExact
        (andb coarseSenderRoleExact
          (andb coarseReceiverRoleExact
            (andb coarseSenderProcessExact coarseReceiverProcessExact)))))

decideExactInternalRendezvousByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool
decideExactInternalRendezvousByFacts endpointFactsValid participantFactsValid messageCoarseFactsValid =
  andb endpointFactsValid
    (andb participantFactsValid messageCoarseFactsValid)

