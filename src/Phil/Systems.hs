{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems
  ( module Phil.Systems.IR
  , module Phil.Systems.Verify
  , module Phil.Systems.Phase0
  , module Phil.Systems.Dataflow
  , module Phil.Systems.FieldProjection
  , module Phil.Systems.RecognizedRecord
  , module Phil.Systems.DigestValidation
  , module Phil.Systems.Storage
  , module Phil.Systems.AcceptedResponse
  , module Phil.Systems.RejectedResponse
  , module Phil.Systems.SessionChoice
  , module Phil.Systems.PayloadCancelChoice
  , module Phil.Systems.LocalRuntimeChoice
  , module Phil.Systems.VersionSessionChoice
  , module Phil.Systems.VersionChoiceOperands
  , module Phil.Systems.BeginPolicySessionChoice
  , module Phil.Systems.HelloPolicyValidation
  , module Phil.Systems.ClientOutbound
  , module Phil.Systems.RecognitionFailure
  , module Phil.Systems.StorageFailure
  , FileSystemOccurrence
  , unFileSystemOccurrence
  , ProviderRelativePath
  , providerRelativePathOccurrence
  , providerRelativePathSegments
  , ProviderRelativePathError (..)
  , fileSystemOccurrence
  , checkProviderRelativePath
  , renderProviderRelativePath
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Systems.AcceptedResponse
import Phil.Systems.BeginPolicySessionChoice
import Phil.Systems.ClientOutbound
import Phil.Systems.Dataflow
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.DigestValidation
import Phil.Systems.FieldProjection
import Phil.Systems.IR
import Phil.Systems.LocalRuntimeChoice
import Phil.Systems.Phase0
import Phil.Systems.PayloadCancelChoice
import Phil.Systems.RecognizedRecord
import Phil.Systems.RecognitionFailure
import Phil.Systems.RejectedResponse
import Phil.Systems.SessionChoice
import Phil.Systems.Storage
import Phil.Systems.StorageFailure
import Phil.Systems.VersionChoiceOperands
import Phil.Systems.VersionSessionChoice
import Phil.Systems.Verify

-- | Exact semantic occurrence of one FileSystem provider. Paths are qualified
-- by this identity rather than by a host current working directory or ambient
-- filesystem namespace.
newtype FileSystemOccurrence = FileSystemOccurrence
  { unFileSystemOccurrence :: Text
  }
  deriving (Eq, Ord, Show)

-- | Canonical source-level path relative to exactly one FileSystem occurrence.
-- The constructor is hidden so accepted paths cannot contain empty, dot, or
-- parent segments. Source '/' is the only separator; host separators are data.
data ProviderRelativePath = ProviderRelativePath
  { providerRelativePathOccurrence :: FileSystemOccurrence
  , providerRelativePathSegments :: [Text]
  }
  deriving (Eq, Ord, Show)

data ProviderRelativePathError
  = EmptyFileSystemOccurrence
  | EmptyProviderRelativePath
  | AbsoluteProviderRelativePath Text
  | EmptyProviderRelativePathSegment Int
  | DotProviderRelativePathSegment Int
  | ParentProviderRelativePathSegment Int
  deriving (Eq, Ord, Show)

fileSystemOccurrence
  :: Text
  -> Either ProviderRelativePathError FileSystemOccurrence
fileSystemOccurrence occurrence
  | Text.null occurrence = Left EmptyFileSystemOccurrence
  | otherwise = Right (FileSystemOccurrence occurrence)

checkProviderRelativePath
  :: FileSystemOccurrence
  -> Text
  -> Either ProviderRelativePathError ProviderRelativePath
checkProviderRelativePath occurrence raw
  | Text.null raw = Left EmptyProviderRelativePath
  | "/" `Text.isPrefixOf` raw = Left (AbsoluteProviderRelativePath raw)
  | otherwise = do
      let segments = Text.splitOn "/" raw
      mapM_ validateSegment (zip [1 ..] segments)
      Right ProviderRelativePath
        { providerRelativePathOccurrence = occurrence
        , providerRelativePathSegments = segments
        }
  where
    validateSegment (index, segment)
      | Text.null segment = Left (EmptyProviderRelativePathSegment index)
      | segment == "." = Left (DotProviderRelativePathSegment index)
      | segment == ".." = Left (ParentProviderRelativePathSegment index)
      | otherwise = Right ()

renderProviderRelativePath :: ProviderRelativePath -> Text
renderProviderRelativePath = Text.intercalate "/" . providerRelativePathSegments
