module ProviderRelativePathKernel where

import qualified Prelude

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

data FileSystemOccurrenceDecision =
   FileSystemOccurrenceAccepted
 | FileSystemOccurrenceEmpty

decideFileSystemOccurrenceByFacts :: Prelude.Bool ->
                                     FileSystemOccurrenceDecision
decideFileSystemOccurrenceByFacts occurrenceEmpty =
  case occurrenceEmpty of {
   Prelude.True -> FileSystemOccurrenceEmpty;
   Prelude.False -> FileSystemOccurrenceAccepted}

data ProviderRelativePathDecision =
   ProviderRelativePathAccepted
 | ProviderRelativePathEmpty
 | ProviderRelativePathAbsolute
 | ProviderRelativePathEmptySegment Nat
 | ProviderRelativePathDotSegment Nat
 | ProviderRelativePathParentSegment Nat

data ProviderRelativeSegmentFacts =
   MkProviderRelativeSegmentFacts Prelude.Bool Prelude.Bool Prelude.Bool

providerRelativeSegmentEmpty :: ProviderRelativeSegmentFacts -> Prelude.Bool
providerRelativeSegmentEmpty p =
  case p of {
   MkProviderRelativeSegmentFacts providerRelativeSegmentEmpty0 _ _ ->
    providerRelativeSegmentEmpty0}

providerRelativeSegmentDot :: ProviderRelativeSegmentFacts -> Prelude.Bool
providerRelativeSegmentDot p =
  case p of {
   MkProviderRelativeSegmentFacts _ providerRelativeSegmentDot0 _ ->
    providerRelativeSegmentDot0}

providerRelativeSegmentParent :: ProviderRelativeSegmentFacts -> Prelude.Bool
providerRelativeSegmentParent p =
  case p of {
   MkProviderRelativeSegmentFacts _ _ providerRelativeSegmentParent0 ->
    providerRelativeSegmentParent0}

decideProviderRelativeSegmentAt :: Nat -> ProviderRelativeSegmentFacts ->
                                   ProviderRelativePathDecision
decideProviderRelativeSegmentAt index facts =
  case providerRelativeSegmentEmpty facts of {
   Prelude.True -> ProviderRelativePathEmptySegment index;
   Prelude.False ->
    case providerRelativeSegmentDot facts of {
     Prelude.True -> ProviderRelativePathDotSegment index;
     Prelude.False ->
      case providerRelativeSegmentParent facts of {
       Prelude.True -> ProviderRelativePathParentSegment index;
       Prelude.False -> ProviderRelativePathAccepted}}}

decideProviderRelativeSegmentsFrom :: Nat -> (List
                                      ProviderRelativeSegmentFacts) ->
                                      ProviderRelativePathDecision
decideProviderRelativeSegmentsFrom index facts =
  case facts of {
   Nil -> ProviderRelativePathAccepted;
   Cons first rest ->
    case decideProviderRelativeSegmentAt index first of {
     ProviderRelativePathAccepted ->
      decideProviderRelativeSegmentsFrom (S index) rest;
     x -> x}}

decideProviderRelativePathByFacts :: Prelude.Bool -> Prelude.Bool -> (List
                                     ProviderRelativeSegmentFacts) ->
                                     ProviderRelativePathDecision
decideProviderRelativePathByFacts rawEmpty startsWithSourceSlash segmentFacts =
  case rawEmpty of {
   Prelude.True -> ProviderRelativePathEmpty;
   Prelude.False ->
    case startsWithSourceSlash of {
     Prelude.True -> ProviderRelativePathAbsolute;
     Prelude.False -> decideProviderRelativeSegmentsFrom (S O) segmentFacts}}

