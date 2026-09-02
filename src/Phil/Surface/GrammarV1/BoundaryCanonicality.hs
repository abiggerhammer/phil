module Phil.Surface.GrammarV1.BoundaryCanonicality
  ( grammarV1BoundaryCanonicality
  ) where

import Phil.Core.EncodingCanonicality (EncodingCanonicality (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BoundaryDecl (..)
  , GrammarV1BoundaryItem (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve the source-level canonical-encoding requirement exactly.
-- Absence means canonical encoding is not required; the presence of one or more
-- canonical items means it is required. This projection does not classify any
-- concrete encoding as canonical and does not prove canonicality: those remain
-- owned by Core's EncodingForm classification and checkEncodingCanonicality.
-- Repeated canonical items are idempotent at this requirement projection; any
-- duplicate-item declaration legality is a separate boundary checker concern.
grammarV1BoundaryCanonicality
  :: GrammarV1BoundaryDecl
  -> EncodingCanonicality
grammarV1BoundaryCanonicality boundary
  | any isCanonical (grammarV1BoundaryItems boundary) = CanonicalEncodingRequired
  | otherwise = CanonicalityNotRequired
  where
    isCanonical (Located _ item) = case item of
      GrammarV1BoundaryCanonical -> True
      _ -> False
