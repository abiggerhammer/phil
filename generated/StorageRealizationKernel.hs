module StorageRealizationKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

decideStorageRealizationValidByFacts :: Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool ->
                                        Prelude.Bool -> Prelude.Bool
decideStorageRealizationValidByFacts subjectBasisAdmitted exactSubjectPresent semanticRevisionNonzero outcomeRevisionNonzero physicalStrategyNonzero selectedSemanticsNonzero physicalObjectsNonzero =
  andb subjectBasisAdmitted
    (andb exactSubjectPresent
      (andb semanticRevisionNonzero
        (andb outcomeRevisionNonzero
          (andb physicalStrategyNonzero
            (andb selectedSemanticsNonzero physicalObjectsNonzero)))))

