module CallableModeKernel where

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

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

fold_left :: (a1 -> a2 -> a1) -> (List a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   Nil -> a0;
   Cons b l0 -> fold_left f l0 (f a0 b)}

data Mode =
   Unrestricted
 | Affine
 | Linear

data CaptureTransfer =
   CopyCapture
 | MoveCapture

data ClosureCapture =
   MkClosureCapture Nat CaptureTransfer Mode

captureTransfer :: ClosureCapture -> CaptureTransfer
captureTransfer c =
  case c of {
   MkClosureCapture _ captureTransfer0 _ -> captureTransfer0}

captureMode :: ClosureCapture -> Mode
captureMode c =
  case c of {
   MkClosureCapture _ _ captureMode0 -> captureMode0}

modeRestricted :: Mode -> Prelude.Bool
modeRestricted mode =
  case mode of {
   Unrestricted -> Prelude.False;
   _ -> Prelude.True}

transferIsMove :: CaptureTransfer -> Prelude.Bool
transferIsMove transfer =
  case transfer of {
   CopyCapture -> Prelude.False;
   MoveCapture -> Prelude.True}

captureTransferAllowed :: ClosureCapture -> Prelude.Bool
captureTransferAllowed capture =
  case modeRestricted (captureMode capture) of {
   Prelude.True -> transferIsMove (captureTransfer capture);
   Prelude.False -> Prelude.True}

captureMovedRestricted :: ClosureCapture -> Prelude.Bool
captureMovedRestricted capture =
  andb (modeRestricted (captureMode capture))
    (transferIsMove (captureTransfer capture))

joinMode :: Mode -> Mode -> Mode
joinMode first second =
  case first of {
   Unrestricted -> second;
   Affine -> case second of {
              Unrestricted -> Affine;
              x -> x};
   Linear -> Linear}

data CallableCaptureTransferDecision =
   CallableCaptureTransferAccepted
 | CallableRestrictedCaptureMustMove

decideCallableCaptureTransfer :: Mode -> CaptureTransfer ->
                                 CallableCaptureTransferDecision
decideCallableCaptureTransfer mode transfer =
  case captureTransferAllowed (MkClosureCapture O transfer mode) of {
   Prelude.True -> CallableCaptureTransferAccepted;
   Prelude.False -> CallableRestrictedCaptureMustMove}

captureMovedRestrictedByMode :: Mode -> CaptureTransfer -> Prelude.Bool
captureMovedRestrictedByMode mode transfer =
  captureMovedRestricted (MkClosureCapture O transfer mode)

duplicateCaptureAllowedByEquality :: Prelude.Bool -> Mode -> Mode ->
                                     Prelude.Bool
duplicateCaptureAllowedByEquality sameOccurrence firstMode secondMode =
  case sameOccurrence of {
   Prelude.True ->
    negb (orb (modeRestricted firstMode) (modeRestricted secondMode));
   Prelude.False -> Prelude.True}

data CallableDuplicateCaptureDecision =
   CallableDuplicateCaptureAccepted
 | CallableDuplicateRestrictedCapture

decideCallableDuplicateCapture :: Prelude.Bool -> Mode -> Mode ->
                                  CallableDuplicateCaptureDecision
decideCallableDuplicateCapture sameOccurrence firstMode secondMode =
  case duplicateCaptureAllowedByEquality sameOccurrence firstMode secondMode of {
   Prelude.True -> CallableDuplicateCaptureAccepted;
   Prelude.False -> CallableDuplicateRestrictedCapture}

closureStructuralModeFromModes :: (List Mode) -> Mode
closureStructuralModeFromModes modes =
  fold_left joinMode modes Unrestricted

