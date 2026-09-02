module Phil.Surface.GrammarV1.BoundaryCodecReferences
  ( grammarV1BoundaryReceiveCodecs
  , grammarV1BoundarySendCodecs
  ) where

import Phil.Core.Generic.StaticActual (GenericStaticActual)
import Phil.Surface.GrammarV1.Elaborate (grammarV1BareStaticReferenceActual)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BoundaryDecl (..)
  , GrammarV1BoundaryItem (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve receive-side codec references only at the unresolved static-reference
-- boundary already established for generic actuals. A bare or qualified,
-- unspecialized source reference remains one 'ReferencedGenericStaticActual'; it
-- does not become a decoder implementation, provider qualification, boundary
-- representation, or recognition authority here. If any receive-side codec uses
-- specialization, the whole receive projection fails closed rather than erasing
-- its static arguments or partially accepting the list. Send-side items are
-- deliberately irrelevant to this projection.
grammarV1BoundaryReceiveCodecs
  :: GrammarV1BoundaryDecl
  -> Maybe [GenericStaticActual]
grammarV1BoundaryReceiveCodecs boundary =
  mapM bareCodecReference
    [ reference
    | Located _ item <- grammarV1BoundaryItems boundary
    , GrammarV1BoundaryReceive reference <- [item]
    ]

-- | Preserve send-side codec references under the same unresolved-static
-- contract as receive-side references. This does not establish encoder admission,
-- representation identity, output ownership, canonicality, or generated evidence.
-- A specialized send reference therefore remains unresolved for the exact static
-- application slice instead of being flattened to its base spelling.
grammarV1BoundarySendCodecs
  :: GrammarV1BoundaryDecl
  -> Maybe [GenericStaticActual]
grammarV1BoundarySendCodecs boundary =
  mapM bareCodecReference
    [ reference
    | Located _ item <- grammarV1BoundaryItems boundary
    , GrammarV1BoundarySend reference <- [item]
    ]

bareCodecReference
  :: Located GrammarV1StaticReference
  -> Maybe GenericStaticActual
bareCodecReference (Located _ reference) =
  grammarV1BareStaticReferenceActual
    (GrammarV1StaticReferenceArgument reference)
