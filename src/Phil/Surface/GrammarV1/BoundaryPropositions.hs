module Phil.Surface.GrammarV1.BoundaryPropositions
  ( grammarV1BoundaryCorrespondences
  , grammarV1BoundaryLaws
  , grammarV1CheckedBoundaryCorrespondences
  , grammarV1CheckedBoundaryLaws
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BoundaryDecl (..)
  , GrammarV1BoundaryItem (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve every unnamed boundary correspondence in source order and route
-- each proposition through the already-verified binding-aware proposition
-- bridge. Exact absence is an empty list. If any correspondence is outside the
-- current proposition competence boundary, the whole correspondence projection
-- fails closed rather than dropping or partially accepting that item.
grammarV1BoundaryCorrespondences
  :: SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe [Proposition]
grammarV1BoundaryCorrespondences state boundary =
  mapM elaborate
    [ proposition
    | Located _ (GrammarV1BoundaryCorrespondence proposition) <- grammarV1BoundaryItems boundary
    ]
  where
    elaborate (Located _ proposition) = grammarV1BoundProposition state proposition

-- | Preserve named boundary laws as a separate ordered source category. Law
-- names retain their exact spelling while propositions delegate once to the
-- binding-aware proposition bridge. One unresolved law rejects this projection
-- in full; correspondence items are deliberately not folded into the law list.
grammarV1BoundaryLaws
  :: SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe [(Text, Proposition)]
grammarV1BoundaryLaws state boundary =
  mapM elaborate
    [ (locatedValue name, proposition)
    | Located _ (GrammarV1BoundaryLaw name proposition) <- grammarV1BoundaryItems boundary
    ]
  where
    elaborate (name, Located _ proposition) =
      (,) name <$> grammarV1BoundProposition state proposition

-- | Route every correspondence through the complete checked proposition path.
-- Source non-competence remains Nothing; the first Core focusing rejection
-- remains a distinct Left; accepted propositions retain exact focusing traces.
-- Laws remain a separate semantic category and cannot affect this projection.
grammarV1CheckedBoundaryCorrespondences
  :: StaticContext
  -> SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe (Either FocusingError [(Proposition, [FocusStep])])
grammarV1CheckedBoundaryCorrespondences staticContext state boundary = do
  checked <- mapM elaborate
    [ proposition
    | Located _ (GrammarV1BoundaryCorrespondence proposition) <- grammarV1BoundaryItems boundary
    ]
  pure (sequence checked)
  where
    elaborate (Located _ proposition) =
      grammarV1CheckedProposition staticContext state proposition

-- | Route named boundary laws through the same checked proposition authority
-- without collapsing names, law order, or law/correspondence categories. Exact
-- absence is Just (Right []). A structural gap poisons the whole law projection;
-- Core rejection remains an ordered Left with no fallback interpretation.
grammarV1CheckedBoundaryLaws
  :: StaticContext
  -> SurfaceState
  -> GrammarV1BoundaryDecl
  -> Maybe (Either FocusingError [(Text, Proposition, [FocusStep])])
grammarV1CheckedBoundaryLaws staticContext state boundary = do
  checked <- mapM elaborate
    [ (locatedValue name, proposition)
    | Located _ (GrammarV1BoundaryLaw name proposition) <- grammarV1BoundaryItems boundary
    ]
  pure (sequence checked)
  where
    elaborate (name, Located _ proposition) =
      fmap
        (fmap (\(checkedProposition, steps) -> (name, checkedProposition, steps)))
        (grammarV1CheckedProposition staticContext state proposition)
