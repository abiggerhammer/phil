module Phil.Core.Protocol.Generic
  ( transferProtocolEndpoint
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context
  ( consumeLinear
  , insertBinding
  )
import Phil.Core.Protocol
  ( ProtocolCheckError (..)
  , ProtocolContext (..)
  , ProtocolEndpointBinding (..)
  , lookupProtocolEndpoint
  )
import Phil.Core.Syntax
  ( Mode (Linear)
  , Name
  )

-- | Move one live endpoint occurrence to a fresh local name without inspecting
-- or exercising its session state.  This operation is therefore valid even
-- when the endpoint is indexed by an abstract SessionVar.
transferProtocolEndpoint
  :: Name
  -> Name
  -> ProtocolContext
  -> Either ProtocolCheckError ProtocolContext
transferProtocolEndpoint predecessor successor context = do
  binding <- maybe
    (Left (ProtocolEndpointUnknown predecessor))
    Right
    (lookupProtocolEndpoint predecessor context)
  if Map.member successor (protocolEndpoints context)
    then Left (ProtocolEndpointMetadataConflict successor)
    else Right ()
  (endpointTy, consumed) <- mapLeft ProtocolResourceError $
    consumeLinear predecessor (protocolResources context)
  resources <- mapLeft ProtocolResourceError $
    insertBinding Linear successor endpointTy consumed
  let successorBinding = binding { protocolEndpointName = successor }
  Right ProtocolContext
    { protocolResources = resources
    , protocolEndpoints = Map.insert successor successorBinding
        (Map.delete predecessor (protocolEndpoints context))
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
