module Phil.Surface.GrammarV1.BoundaryPropositions
  ( grammarV1BoundaryCorrespondences
  , grammarV1BoundaryLaws
  ) where

import Data.Text (Text)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
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
