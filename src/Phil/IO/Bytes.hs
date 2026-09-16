module Phil.IO.Bytes
  ( RuntimeBytes
  , makeRuntimeBytes
  , runtimeBytesOctets
  , runtimeBytesLength
  , runtimeBytesSemanticType
  ) where

import Data.Word (Word8)
import Phil.Core.Syntax (Ty, runtimeBytesType)

-- | Representation-neutral semantic carrier for one finite Phil `Bytes` value.
-- The constructor is hidden so callers cannot attach host buffer identity or
-- laziness to source semantics. Construction forces the spine length, so an
-- accepted value denotes a finite sequence of octets.
newtype RuntimeBytes = RuntimeBytes
  { runtimeBytesOctets :: [Word8]
  }
  deriving (Eq, Ord, Show)

makeRuntimeBytes :: [Word8] -> RuntimeBytes
makeRuntimeBytes octets =
  let finiteLength = length octets
  in finiteLength `seq` RuntimeBytes octets

runtimeBytesLength :: RuntimeBytes -> Int
runtimeBytesLength = length . runtimeBytesOctets

-- | Value-level witness that this carrier inhabits the bare runtime-sized
-- member of the existing linear Bytes family established by IO-BYTES-001.
runtimeBytesSemanticType :: RuntimeBytes -> Ty
runtimeBytesSemanticType _ = runtimeBytesType
