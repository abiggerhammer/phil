module Phil.Core.DataOperationContract
  ( DataOperation (..)
  , OperationContract
  , emptyOperationContract
  , grantOperation
  , permitsOperation
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

data DataOperation
  = Equality
  | Ordering
  | Hashing
  | Clone
  | Default
  | Serialization
  | Deserialization
  | MemcpySafety
  | ABICompatibility
  deriving (Eq, Ord, Show)

newtype OperationContract = OperationContract (Set DataOperation)
  deriving (Eq, Show)

emptyOperationContract :: OperationContract
emptyOperationContract = OperationContract Set.empty

grantOperation :: DataOperation -> OperationContract -> OperationContract
grantOperation operation (OperationContract operations) =
  OperationContract (Set.insert operation operations)

permitsOperation :: OperationContract -> DataOperation -> Bool
permitsOperation (OperationContract operations) operation =
  Set.member operation operations
