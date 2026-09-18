{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1WholeSourceVerification
  ( WholeSourceFileRef (..)
  , Phase1WholeSourceVerificationDescriptor (..)
  , Phase1WholeSourceVerificationDescriptorError (..)
  , Phase1WholeSourceVerificationFileError (..)
  , phase1WholeSourceVerificationFormatV1
  , decodePhase1WholeSourceVerificationDescriptor
  , materializePhase1WholeSourceVerificationDescriptor
  ) where

import Control.Exception (IOException, try)
import Control.Monad (foldM)
import Data.Char (isControl, isDigit)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  )
import Phil.Handoff.Phase1Manifest (sha256File)
import Phil.Verification (AssurancePolicyRevision (..))
import Phil.Verification.GrammarV1WholeSource
  ( GrammarV1WholeSourceVerificationSpec (..)
  )

data WholeSourceFileRef = WholeSourceFileRef
  { wholeSourceFileLabel :: Text
  , wholeSourceFilePath :: FilePath
  , wholeSourceFileSha256 :: Text
  }
  deriving (Eq, Ord, Show)

data Phase1WholeSourceVerificationDescriptor =
  Phase1WholeSourceVerificationDescriptor
    { wholeSourceDescriptorPrimary :: WholeSourceFileRef
    , wholeSourceDescriptorSupplemental :: [WholeSourceFileRef]
    , wholeSourceDescriptorArchitectureKey :: DeclarationKey
    , wholeSourceDescriptorArchitectureRevision :: DefinitionRevision
    , wholeSourceDescriptorProgramKey :: DeclarationKey
    , wholeSourceDescriptorPolicyRevision :: AssurancePolicyRevision
    , wholeSourceDescriptorSummaryPath :: FilePath
    }
  deriving (Eq, Show)

data Phase1WholeSourceVerificationDescriptorError
  = WholeSourceDescriptorEmpty
  | WholeSourceDescriptorHeaderMismatch Text
  | WholeSourceDescriptorMalformedRecord Int Text
  | WholeSourceDescriptorMalformedPath Int Text
  | WholeSourceDescriptorMalformedDigest Int Text
  | WholeSourceDescriptorDuplicatePrimary
  | WholeSourceDescriptorMissingPrimary
  | WholeSourceDescriptorDuplicateSupplementalLabel Text
  | WholeSourceDescriptorDuplicateSourcePath FilePath
  | WholeSourceDescriptorDuplicateArchitecture
  | WholeSourceDescriptorMissingArchitecture
  | WholeSourceDescriptorDuplicateProgram
  | WholeSourceDescriptorMissingProgram
  | WholeSourceDescriptorDuplicatePolicy
  | WholeSourceDescriptorMissingPolicy
  | WholeSourceDescriptorDuplicateSummary
  | WholeSourceDescriptorMissingSummary
  deriving (Eq, Show)

data Phase1WholeSourceVerificationFileError
  = WholeSourceDescriptorFileUnreadable FilePath Text
  | WholeSourceDescriptorDigestMismatch FilePath Text Text
  deriving (Eq, Show)

phase1WholeSourceVerificationFormatV1 :: Text
phase1WholeSourceVerificationFormatV1 =
  "PHIL-PHASE1-WHOLE-SOURCE-VERIFICATION-V1"

data DecodeState = DecodeState
  { decodePrimary :: Maybe WholeSourceFileRef
  , decodeSupplemental :: [WholeSourceFileRef]
  , decodeArchitecture :: Maybe (DeclarationKey, DefinitionRevision)
  , decodeProgram :: Maybe DeclarationKey
  , decodePolicy :: Maybe AssurancePolicyRevision
  , decodeSummary :: Maybe FilePath
  }

emptyDecodeState :: DecodeState
emptyDecodeState = DecodeState Nothing [] Nothing Nothing Nothing Nothing

decodePhase1WholeSourceVerificationDescriptor
  :: Text
  -> Either
      Phase1WholeSourceVerificationDescriptorError
      Phase1WholeSourceVerificationDescriptor
decodePhase1WholeSourceVerificationDescriptor input =
  case Text.lines input of
    [] -> Left WholeSourceDescriptorEmpty
    header : rows
      | Text.strip header /= phase1WholeSourceVerificationFormatV1 ->
          Left (WholeSourceDescriptorHeaderMismatch (Text.strip header))
      | otherwise -> do
          state <- foldM decodeRow emptyDecodeState (zip [2 ..] rows)
          primary <- maybe
            (Left WholeSourceDescriptorMissingPrimary)
            Right
            (decodePrimary state)
          architecture <- maybe
            (Left WholeSourceDescriptorMissingArchitecture)
            Right
            (decodeArchitecture state)
          program <- maybe
            (Left WholeSourceDescriptorMissingProgram)
            Right
            (decodeProgram state)
          policy <- maybe
            (Left WholeSourceDescriptorMissingPolicy)
            Right
            (decodePolicy state)
          summaryPath <- maybe
            (Left WholeSourceDescriptorMissingSummary)
            Right
            (decodeSummary state)
          validateSources primary (decodeSupplemental state)
          Right Phase1WholeSourceVerificationDescriptor
            { wholeSourceDescriptorPrimary = primary
            , wholeSourceDescriptorSupplemental =
                reverse (decodeSupplemental state)
            , wholeSourceDescriptorArchitectureKey = fst architecture
            , wholeSourceDescriptorArchitectureRevision = snd architecture
            , wholeSourceDescriptorProgramKey = program
            , wholeSourceDescriptorPolicyRevision = policy
            , wholeSourceDescriptorSummaryPath = summaryPath
            }

decodeRow
  :: DecodeState
  -> (Int, Text)
  -> Either Phase1WholeSourceVerificationDescriptorError DecodeState
decodeRow state (lineNumber, rawLine)
  | Text.null stripped = Right state
  | "#" `Text.isPrefixOf` stripped = Right state
  | otherwise =
      case Text.splitOn "\t" rawLine of
        ["primary", label, rawPath, digest] -> do
          ref <- sourceRef lineNumber label rawPath digest
          case decodePrimary state of
            Nothing -> Right state { decodePrimary = Just ref }
            Just _ -> Left WholeSourceDescriptorDuplicatePrimary
        ["supplemental", label, rawPath, digest] -> do
          ref <- sourceRef lineNumber label rawPath digest
          Right state
            { decodeSupplemental = ref : decodeSupplemental state }
        ["architecture", rawKey, rawRevision]
          | allNonempty [rawKey, rawRevision] ->
              case decodeArchitecture state of
                Nothing -> Right state
                  { decodeArchitecture = Just
                      ( DeclarationKey rawKey
                      , DefinitionRevision rawRevision
                      )
                  }
                Just _ -> Left WholeSourceDescriptorDuplicateArchitecture
          | otherwise -> malformed
        ["program", rawKey]
          | not (Text.null rawKey) ->
              case decodeProgram state of
                Nothing -> Right state
                  { decodeProgram = Just (DeclarationKey rawKey) }
                Just _ -> Left WholeSourceDescriptorDuplicateProgram
          | otherwise -> malformed
        ["policy", rawRevision]
          | not (Text.null rawRevision) ->
              case decodePolicy state of
                Nothing -> Right state
                  { decodePolicy = Just (AssurancePolicyRevision rawRevision) }
                Just _ -> Left WholeSourceDescriptorDuplicatePolicy
          | otherwise -> malformed
        ["summary", rawPath] -> do
          path <- parsePath lineNumber rawPath
          case decodeSummary state of
            Nothing -> Right state { decodeSummary = Just path }
            Just _ -> Left WholeSourceDescriptorDuplicateSummary
        _ -> malformed
  where
    stripped = Text.strip rawLine
    malformed = Left
      (WholeSourceDescriptorMalformedRecord lineNumber rawLine)
    allNonempty = all (not . Text.null)

sourceRef
  :: Int
  -> Text
  -> Text
  -> Text
  -> Either Phase1WholeSourceVerificationDescriptorError WholeSourceFileRef
sourceRef lineNumber label rawPath digest
  | Text.null label =
      Left (WholeSourceDescriptorMalformedRecord lineNumber label)
  | otherwise = do
      path <- parsePath lineNumber rawPath
      validateDigest lineNumber digest
      Right WholeSourceFileRef
        { wholeSourceFileLabel = label
        , wholeSourceFilePath = path
        , wholeSourceFileSha256 = digest
        }

parsePath
  :: Int
  -> Text
  -> Either Phase1WholeSourceVerificationDescriptorError FilePath
parsePath lineNumber raw
  | raw /= Text.strip raw = malformed
  | Text.null raw = malformed
  | "/" `Text.isPrefixOf` raw = malformed
  | Text.any (\character -> character == '\\' || isControl character) raw =
      malformed
  | any invalidSegment (Text.splitOn "/" raw) = malformed
  | otherwise = Right (Text.unpack raw)
  where
    malformed = Left (WholeSourceDescriptorMalformedPath lineNumber raw)
    invalidSegment segment =
      Text.null segment || segment == "." || segment == ".."

validateDigest
  :: Int
  -> Text
  -> Either Phase1WholeSourceVerificationDescriptorError ()
validateDigest lineNumber raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest
      | Text.length digest == 64
      , Text.all lowerHex digest -> Right ()
    _ -> Left (WholeSourceDescriptorMalformedDigest lineNumber raw)
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

validateSources
  :: WholeSourceFileRef
  -> [WholeSourceFileRef]
  -> Either Phase1WholeSourceVerificationDescriptorError ()
validateSources primary supplemental = do
  unique
    wholeSourceFileLabel
    WholeSourceDescriptorDuplicateSupplementalLabel
    supplemental
  unique
    wholeSourceFilePath
    WholeSourceDescriptorDuplicateSourcePath
    (primary : supplemental)
  where
    unique project duplicateError = go Set.empty
      where
        go _ [] = Right ()
        go seen (value : rest)
          | Set.member key seen = Left (duplicateError key)
          | otherwise = go (Set.insert key seen) rest
          where
            key = project value

materializePhase1WholeSourceVerificationDescriptor
  :: FilePath
  -> Phase1WholeSourceVerificationDescriptor
  -> IO
      (Either
        Phase1WholeSourceVerificationFileError
        (GrammarV1WholeSourceVerificationSpec, Text))
materializePhase1WholeSourceVerificationDescriptor repositoryRoot descriptor = do
  primaryResult <- readChecked (wholeSourceDescriptorPrimary descriptor)
  case primaryResult of
    Left errorValue -> pure (Left errorValue)
    Right primaryText -> do
      supplementalResult <-
        materializeSupplemental (wholeSourceDescriptorSupplemental descriptor)
      case supplementalResult of
        Left errorValue -> pure (Left errorValue)
        Right supplemental -> do
          summaryResult <- readTextPath
            (wholeSourceDescriptorSummaryPath descriptor)
          pure $ fmap
            (\summaryText ->
              ( GrammarV1WholeSourceVerificationSpec
                  { wholeSourcePrimaryLabel =
                      wholeSourceFileLabel
                        (wholeSourceDescriptorPrimary descriptor)
                  , wholeSourcePrimaryText = primaryText
                  , wholeSourceSupplementalUnits = supplemental
                  , wholeSourceArchitectureKey =
                      wholeSourceDescriptorArchitectureKey descriptor
                  , wholeSourceArchitectureRevision =
                      wholeSourceDescriptorArchitectureRevision descriptor
                  , wholeSourceProgramKey =
                      wholeSourceDescriptorProgramKey descriptor
                  , wholeSourcePolicyRevision =
                      wholeSourceDescriptorPolicyRevision descriptor
                  }
              , summaryText
              ))
            summaryResult
  where
    materializeSupplemental [] = pure (Right [])
    materializeSupplemental (ref : rest) = do
      sourceResult <- readChecked ref
      case sourceResult of
        Left errorValue -> pure (Left errorValue)
        Right source -> fmap
          (fmap ((wholeSourceFileLabel ref, source) :))
          (materializeSupplemental rest)

    readChecked ref = do
      let path = wholeSourceFilePath ref
          expected = wholeSourceFileSha256 ref
          fullPath = repositoryPath repositoryRoot path
      digestResult <- sha256File fullPath
      case digestResult of
        Left detail ->
          pure (Left (WholeSourceDescriptorFileUnreadable path detail))
        Right actual
          | actual /= expected ->
              pure (Left
                (WholeSourceDescriptorDigestMismatch path expected actual))
          | otherwise -> readTextPath path

    readTextPath path = do
      result <- try (TextIO.readFile (repositoryPath repositoryRoot path))
      pure $ case result of
        Left errorValue -> Left
          (WholeSourceDescriptorFileUnreadable
            path
            (Text.pack (show (errorValue :: IOException))))
        Right source -> Right source

repositoryPath :: FilePath -> FilePath -> FilePath
repositoryPath root relative
  | null root || root == "." = relative
  | last root == '/' = root <> relative
  | otherwise = root <> "/" <> relative
