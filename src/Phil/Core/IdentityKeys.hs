module Phil.Core.IdentityKeys
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  ) where

import Data.Text (Text)

newtype DeclarationKey = DeclarationKey { unDeclarationKey :: Text }
  deriving (Eq, Ord, Show)

newtype InterfaceRevision = InterfaceRevision { unInterfaceRevision :: Text }
  deriving (Eq, Ord, Show)
