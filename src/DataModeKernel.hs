module DataModeKernel where

import qualified Prelude

data Mode =
   Unrestricted
 | Affine
 | Linear

modeLub :: Mode -> Mode -> Mode
modeLub left right =
  case left of {
   Unrestricted -> right;
   Affine -> case right of {
              Unrestricted -> Affine;
              x -> x};
   Linear -> Linear}

deriveRecordMode :: ([] Mode) -> Mode
deriveRecordMode modes =
  case modes of {
   [] -> Unrestricted;
   (:) mode rest -> modeLub mode (deriveRecordMode rest)}

deriveSumMode :: ([] ([] Mode)) -> Mode
deriveSumMode constructors =
  case constructors of {
   [] -> Unrestricted;
   (:) payloadModes rest ->
    modeLub (deriveRecordMode payloadModes) (deriveSumMode rest)}

modeEqb :: Mode -> Mode -> Prelude.Bool
modeEqb left right =
  case left of {
   Unrestricted ->
    case right of {
     Unrestricted -> Prelude.True;
     _ -> Prelude.False};
   Affine -> case right of {
              Affine -> Prelude.True;
              _ -> Prelude.False};
   Linear -> case right of {
              Linear -> Prelude.True;
              _ -> Prelude.False}}

modeLeb :: Mode -> Mode -> Prelude.Bool
modeLeb left right =
  case left of {
   Unrestricted -> Prelude.True;
   Affine ->
    case right of {
     Unrestricted -> Prelude.False;
     _ -> Prelude.True};
   Linear -> case right of {
              Linear -> Prelude.True;
              _ -> Prelude.False}}

data AggregateModeDecision =
   AggregateModeAcceptedDecision
 | AggregateModeMismatchDecision

decideRecordModeByCandidate :: ([] Mode) -> Mode -> AggregateModeDecision
decideRecordModeByCandidate fieldModes candidate =
  case modeEqb (deriveRecordMode fieldModes) candidate of {
   Prelude.True -> AggregateModeAcceptedDecision;
   Prelude.False -> AggregateModeMismatchDecision}

decideSumModeByCandidate :: ([] ([] Mode)) -> Mode -> AggregateModeDecision
decideSumModeByCandidate constructorPayloadModes candidate =
  case modeEqb (deriveSumMode constructorPayloadModes) candidate of {
   Prelude.True -> AggregateModeAcceptedDecision;
   Prelude.False -> AggregateModeMismatchDecision}

resolvedStrongestMode :: ([] (Prelude.Maybe Mode)) -> Prelude.Maybe Mode
resolvedStrongestMode resolvedModes =
  case resolvedModes of {
   [] -> Prelude.Just Unrestricted;
   (:) o rest ->
    case o of {
     Prelude.Just mode ->
      case resolvedStrongestMode rest of {
       Prelude.Just tailMode -> Prelude.Just (modeLub mode tailMode);
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

data NominalModeDecision =
   NominalModeAcceptedDecision Mode
 | NominalModeWeakeningDecision
 | NominalModeJustificationDecision

decideNominalModeByFact :: Mode -> (Prelude.Maybe Mode) -> Prelude.Bool ->
                           NominalModeDecision
decideNominalModeByFact derived declared strictJustificationAccepted =
  case declared of {
   Prelude.Just declaredMode ->
    case modeEqb derived declaredMode of {
     Prelude.True -> NominalModeAcceptedDecision declaredMode;
     Prelude.False ->
      case modeLeb derived declaredMode of {
       Prelude.True ->
        case strictJustificationAccepted of {
         Prelude.True -> NominalModeAcceptedDecision declaredMode;
         Prelude.False -> NominalModeJustificationDecision};
       Prelude.False -> NominalModeWeakeningDecision}};
   Prelude.Nothing -> NominalModeAcceptedDecision derived}

data AggregateFormationDecision =
   AggregateFormationAcceptedDecision
 | AggregateFormationDuplicateRestrictedDecision

decideAggregateFormationByFact :: Prelude.Bool -> AggregateFormationDecision
decideAggregateFormationByFact restrictedOccurrencesUnique =
  case restrictedOccurrencesUnique of {
   Prelude.True -> AggregateFormationAcceptedDecision;
   Prelude.False -> AggregateFormationDuplicateRestrictedDecision}
