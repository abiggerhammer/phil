{-# LANGUAGE OverloadedStrings #-}

module Phil.IO.UTF8
  ( UTF8DecodeError (..)
  , utf8Encode
  , utf8Decode
  , ReadUTF8Outcome (..)
  , CheckedReadUTF8 (..)
  , checkReadUTF8
  , CheckedWriteUTF8 (..)
  , checkWriteUTF8
  , CheckedWriteLine (..)
  , checkWriteLine
  ) where

import qualified Data.ByteString as ByteString
import Data.Text (Text)
import qualified Data.Text.Encoding as TextEncoding
import Phil.Core.Authority
  ( AuthorityExerciseSource
  , AuthorityState
  )
import Phil.IO.Bytes
  ( RuntimeBytes
  , makeRuntimeBytes
  , runtimeBytesOctets
  )
import Phil.IO.Console
  ( CheckedConsoleWrite
  , ConsoleCheckError
  , ConsoleProviderOccurrence
  , ConsoleWriteOutcome
  , checkConsoleWrite
  )
import Phil.IO.FileSystem
  ( CheckedFileSystemRead (..)
  , CheckedFileSystemReplace
  , FileReadOutcome (..)
  , FileReplaceOutcome
  , FileSystemCheckError
  , FileSystemFailure
  , FileSystemState
  , checkFileSystemRead
  , checkFileSystemReplace
  )
import Phil.Systems
  ( FileSystemOccurrence
  , ProviderRelativePath
  )

-- | Portable semantic failure for the explicit UTF-8 decoder. Host-library
-- exception text, locale state, and replacement-character policy are not part
-- of the Phil contract.
data UTF8DecodeError = InvalidUTF8
  deriving (Eq, Ord, Show)

-- | Explicit UTF-8 encoding from Phil String semantics into the finite runtime
-- Bytes carrier. ByteString is only an implementation substrate here; the
-- returned semantic value is the representation-neutral RuntimeBytes sequence.
utf8Encode :: Text -> RuntimeBytes
utf8Encode =
  makeRuntimeBytes . ByteString.unpack . TextEncoding.encodeUtf8

-- | Strict UTF-8 decoding. Invalid input is an explicit result; there is no
-- replacement-character fallback, locale lookup, host text mode, or Unicode
-- normalization step.
utf8Decode :: RuntimeBytes -> Either UTF8DecodeError Text
utf8Decode bytes =
  case TextEncoding.decodeUtf8' (ByteString.pack (runtimeBytesOctets bytes)) of
    Left _ -> Left InvalidUTF8
    Right text -> Right text

data ReadUTF8Outcome
  = ReadUTF8Decoded Text
  | ReadUTF8DecodeFailed UTF8DecodeError
  | ReadUTF8ProviderFailed FileSystemFailure
  deriving (Eq, Ord, Show)

-- | Ordinary composition record: the exact checked binary provider call stays
-- visible alongside the codec-level outcome. Effects, authority, path identity,
-- boundedness, and provider failure therefore remain those of FileSystem.read.
data CheckedReadUTF8 = CheckedReadUTF8
  { checkedReadUTF8FileRead :: CheckedFileSystemRead
  , checkedReadUTF8Outcome :: ReadUTF8Outcome
  }
  deriving (Eq, Ord, Show)

checkReadUTF8
  :: FileSystemOccurrence
  -> ProviderRelativePath
  -> Int
  -> AuthorityExerciseSource
  -> AuthorityState
  -> FileSystemState
  -> FileReadOutcome
  -> Either FileSystemCheckError CheckedReadUTF8
checkReadUTF8 occurrence path limit authoritySource authorityState state observed = do
  checkedRead <- checkFileSystemRead
    occurrence path limit authoritySource authorityState state observed
  let outcome = case checkedFileSystemReadOutcome checkedRead of
        FileReadSucceeded bytes ->
          case utf8Decode bytes of
            Left err -> ReadUTF8DecodeFailed err
            Right text -> ReadUTF8Decoded text
        FileReadFailed failure -> ReadUTF8ProviderFailed failure
  Right CheckedReadUTF8
    { checkedReadUTF8FileRead = checkedRead
    , checkedReadUTF8Outcome = outcome
    }

-- | Ordinary write_utf8 composition. The encoded bytes and the exact checked
-- FileSystem.replace call are both retained; this layer introduces no new
-- authority, effect, failure, or replacement semantics.
data CheckedWriteUTF8 = CheckedWriteUTF8
  { checkedWriteUTF8Text :: Text
  , checkedWriteUTF8Bytes :: RuntimeBytes
  , checkedWriteUTF8FileReplace :: CheckedFileSystemReplace
  }
  deriving (Eq, Ord, Show)

checkWriteUTF8
  :: FileSystemOccurrence
  -> ProviderRelativePath
  -> AuthorityExerciseSource
  -> AuthorityState
  -> FileSystemState
  -> Text
  -> FileReplaceOutcome
  -> Either FileSystemCheckError CheckedWriteUTF8
checkWriteUTF8 occurrence path authoritySource authorityState state text observed = do
  let bytes = utf8Encode text
  checkedReplace <- checkFileSystemReplace
    occurrence path bytes authoritySource authorityState state observed
  Right CheckedWriteUTF8
    { checkedWriteUTF8Text = text
    , checkedWriteUTF8Bytes = bytes
    , checkedWriteUTF8FileReplace = checkedReplace
    }

-- | Ordinary write_line composition over ConsoleOutput.write. Exactly one LF is
-- appended at this library layer; the underlying checked write retains exact
-- occurrence authority, effect identity, failure, and partial-write progress.
data CheckedWriteLine = CheckedWriteLine
  { checkedWriteLineText :: Text
  , checkedWriteLineRequestedText :: Text
  , checkedWriteLineConsoleWrite :: CheckedConsoleWrite
  }
  deriving (Eq, Ord, Show)

checkWriteLine
  :: ConsoleProviderOccurrence
  -> AuthorityExerciseSource
  -> AuthorityState
  -> Text
  -> ConsoleWriteOutcome
  -> Either ConsoleCheckError CheckedWriteLine
checkWriteLine occurrence authoritySource authorityState text observed = do
  let requested = text <> "\n"
  checkedWrite <- checkConsoleWrite
    occurrence authoritySource authorityState requested observed
  Right CheckedWriteLine
    { checkedWriteLineText = text
    , checkedWriteLineRequestedText = requested
    , checkedWriteLineConsoleWrite = checkedWrite
    }
