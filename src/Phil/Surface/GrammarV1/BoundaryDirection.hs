module Phil.Surface.GrammarV1.BoundaryDirection
  ( grammarV1BoundaryDirection
  ) where

import Phil.Core.BoundaryDirection (BoundaryDirection (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BoundaryDecl (..)
  , GrammarV1BoundaryItem (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Derive only the direction information already explicit in a Grammar-v1
-- boundary declaration's receive/send items. Other boundary items do not imply
-- a transport direction. A boundary with no receive/send item remains unresolved
-- rather than acquiring an invented default direction.
grammarV1BoundaryDirection
  :: GrammarV1BoundaryDecl
  -> Maybe BoundaryDirection
grammarV1BoundaryDirection boundary =
  case (hasReceive, hasSend) of
    (True, False) -> Just ReceiveOnly
    (False, True) -> Just SendOnly
    (True, True) -> Just Bidirectional
    (False, False) -> Nothing
  where
    items = grammarV1BoundaryItems boundary
    hasReceive = any isReceive items
    hasSend = any isSend items

    isReceive (Located _ item) = case item of
      GrammarV1BoundaryReceive _ -> True
      _ -> False

    isSend (Located _ item) = case item of
      GrammarV1BoundarySend _ -> True
      _ -> False
