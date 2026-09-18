{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1WitnessSourceBundle
  ( HandoffSourceUnitRef (..)
  , Phase1WitnessSourceBundleDescriptor (..)
  , Phase1WitnessSourceBundleError (..)
  , Phase1WitnessSourceBundleFileError (..)
  , phase1WitnessSourceBundleFormatV1
  , decodePhase1WitnessSourceBundleDescriptor
  , materializePhase1WitnessSourceBundle
  ) where

import Control.Exception (IOException, try)
import Control.Monad (foldM)
import Data.Char (isControl, isDigit)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Handoff.Phase1Manifest (sha256File)
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , GrammarRevision (..)
  , InstanceLineageSiteId (..)
  , PortableInstanceLineage (..)
  , PortableProcessLineage (..)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , ProcessLineageSiteId (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )

data HandoffSourceUnitRef = HandoffSourceUnitRef
  { handoffSourceUnitId :: SourceUnitId
  , handoffSourceDeclarationSiteId :: DeclarationSiteId
  , handoffSourceDeclarationMetadataKey :: Maybe Text
  , handoffSourcePath :: FilePath
  , handoffSourceSha256 :: Text
  }
  deriving (Eq, Show)

data Phase1WitnessSourceBundleDescriptor = Phase1WitnessSourceBundleDescriptor
  { witnessSourceGrammarRevision :: GrammarRevision
  , witnessSourceSelectedProgramRoot :: Text
  , witnessSourceUnits :: [HandoffSourceUnitRef]
  , witnessSourceInstanceLineage :: [PortableInstanceLineage]
  , witnessSourceProcessLineage :: [PortableProcessLineage]
  }
  deriving (Eq, Show)

data Phase1WitnessSourceBundleError
  = WitnessSourceBundleEmpty
  | WitnessSourceBundleHeaderMismatch Text
  | WitnessSourceBundleMissingGrammar
  | WitnessSourceBundleDuplicateGrammar GrammarRevision GrammarRevision
  | WitnessSourceBundleMalformedGrammar Text
  | WitnessSourceBundleIncompatibleGrammar GrammarRevision GrammarRevision
  | WitnessSourceBundleMissingRoot
  | WitnessSourceBundleDuplicateRoot Text Text
  | WitnessSourceBundleMalformedRecord Int Text
  | WitnessSourceBundleMalformedPath Int Text
  | WitnessSourceBundleMalformedDigest Int Text
  | WitnessSourceBundleDuplicateUnit SourceUnitId
  | WitnessSourceBundleDuplicateDeclarationSite DeclarationSiteId
  | WitnessSourceBundleDuplicateSourcePath FilePath
  | WitnessSourceBundleDuplicateInstanceSite InstanceLineageSiteId
  | WitnessSourceBundleDuplicateProcessSite ProcessLineageSiteId
  deriving (Eq, Show)

data Phase1WitnessSourceBundleFileError
  = WitnessSourceBundleSourceUnreadable SourceUnitId FilePath Text
  | WitnessSourceBundleSourceDigestMismatch SourceUnitId FilePath Text Text
  deriving (Eq, Show)

phase1WitnessSourceBundleFormatV1 :: Text
phase1WitnessSourceBundleFormatV1 = "PHIL-PHASE1-WITNESS-SOURCE-BUNDLE-V1"

data DecodeState = DecodeState
  { decodeGrammar :: Maybe GrammarRevision
  , decodeRoot :: Maybe Text
  , decodeUnits :: [HandoffSourceUnitRef]
  , decodeInstances :: [PortableInstanceLineage]
  , decodeProcesses :: [PortableProcessLineage]
  }

emptyDecodeState :: DecodeState
emptyDecodeState = DecodeState Nothing Nothing [] [] []

decodePhase1WitnessSourceBundleDescriptor
  :: Text
  -> Either Phase1WitnessSourceBundleError Phase1WitnessSourceBundleDescriptor
decodePhase1WitnessSourceBundleDescriptor input =
  case Text.lines input of
    [] -> Left WitnessSourceBundleEmpty
    header : records
      | Text.strip header /= phase1WitnessSourceBundleFormatV1 ->
          Left (WitnessSourceBundleHeaderMismatch (Text.strip header))
      | otherwise -> do
          decoded <- foldM decodeRecord emptyDecodeState (zip [2 ..] records)
          grammarRevision <- maybe
            (Left WitnessSourceBundleMissingGrammar)
            Right
            (decodeGrammar decoded)
          if grammarRevision == canonicalGrammarRevisionV1
            then Right ()
            else Left
              (WitnessSourceBundleIncompatibleGrammar
                canonicalGrammarRevisionV1 grammarRevision)
          root <- maybe
            (Left WitnessSourceBundleMissingRoot)
            Right
            (decodeRoot decoded)
          let descriptor = Phase1WitnessSourceBundleDescriptor
                { witnessSourceGrammarRevision = grammarRevision
                , witnessSourceSelectedProgramRoot = root
                , witnessSourceUnits = reverse (decodeUnits decoded)
                , witnessSourceInstanceLineage = reverse (decodeInstances decoded)
                , witnessSourceProcessLineage = reverse (decodeProcesses decoded)
                }
          validateDescriptor descriptor
          Right descriptor

decodeRecord
  :: DecodeState
  -> (Int, Text)
  -> Either Phase1WitnessSourceBundleError DecodeState
decodeRecord state (lineNumber, rawLine)
  | Text.null stripped = Right state
  | "#" `Text.isPrefixOf` stripped = Right state
  | otherwise =
      case Text.splitOn "\t" rawLine of
        ["grammar", rawGrammar] -> do
          grammarRevision <- parseGrammar rawGrammar
          case decodeGrammar state of
            Nothing -> Right state { decodeGrammar = Just grammarRevision }
            Just existing ->
              Left (WitnessSourceBundleDuplicateGrammar existing grammarRevision)
        ["root", rawRoot] ->
          let root = Text.strip rawRoot
          in if Text.null root
              then malformed
              else case decodeRoot state of
                Nothing -> Right state { decodeRoot = Just root }
                Just existing -> Left (WitnessSourceBundleDuplicateRoot existing root)
        ["unit", rawUnitId, rawSiteId, rawMetadataKey, rawPath, rawDigest] -> do
          if any (Text.null . Text.strip) [rawUnitId, rawSiteId]
            then malformed
            else Right ()
          path <- parsePath lineNumber rawPath
          digest <- parseDigest lineNumber rawDigest
          let metadataKey = case Text.strip rawMetadataKey of
                "-" -> Nothing
                value
                  | Text.null value -> Nothing
                  | otherwise -> Just value
              unit = HandoffSourceUnitRef
                { handoffSourceUnitId = SourceUnitId (Text.strip rawUnitId)
                , handoffSourceDeclarationSiteId =
                    DeclarationSiteId (Text.strip rawSiteId)
                , handoffSourceDeclarationMetadataKey = metadataKey
                , handoffSourcePath = path
                , handoffSourceSha256 = digest
                }
          Right state { decodeUnits = unit : decodeUnits state }
        ["instance", rawSiteId, rawKey]
          | all (not . Text.null . Text.strip) [rawSiteId, rawKey] ->
              Right state
                { decodeInstances =
                    PortableInstanceLineage
                      (InstanceLineageSiteId (Text.strip rawSiteId))
                      (Text.strip rawKey)
                      : decodeInstances state
                }
          | otherwise -> malformed
        ["process", rawSiteId, rawKey]
          | all (not . Text.null . Text.strip) [rawSiteId, rawKey] ->
              Right state
                { decodeProcesses =
                    PortableProcessLineage
                      (ProcessLineageSiteId (Text.strip rawSiteId))
                      (Text.strip rawKey)
                      : decodeProcesses state
                }
          | otherwise -> malformed
        _ -> malformed
  where
    stripped = Text.strip rawLine
    malformed = Left (WitnessSourceBundleMalformedRecord lineNumber rawLine)

parseGrammar :: Text -> Either Phase1WitnessSourceBundleError GrammarRevision
parseGrammar raw
  | validSha256 raw = Right (GrammarRevision raw)
  | otherwise = Left (WitnessSourceBundleMalformedGrammar raw)

parsePath
  :: Int
  -> Text
  -> Either Phase1WitnessSourceBundleError FilePath
parsePath lineNumber raw
  | raw /= Text.strip raw = malformed
  | Text.null raw = malformed
  | "/" `Text.isPrefixOf` raw = malformed
  | Text.any (\character -> character == '\\' || isControl character) raw = malformed
  | any invalidSegment (Text.splitOn "/" raw) = malformed
  | otherwise = Right (Text.unpack raw)
  where
    malformed = Left (WitnessSourceBundleMalformedPath lineNumber raw)
    invalidSegment segment =
      Text.null segment || segment == "." || segment == ".."

parseDigest
  :: Int
  -> Text
  -> Either Phase1WitnessSourceBundleError Text
parseDigest lineNumber raw
  | validSha256 raw = Right raw
  | otherwise = Left (WitnessSourceBundleMalformedDigest lineNumber raw)

validSha256 :: Text -> Bool
validSha256 raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest ->
      Text.length digest == 64 && Text.all lowerHex digest
    Nothing -> False
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

validateDescriptor
  :: Phase1WitnessSourceBundleDescriptor
  -> Either Phase1WitnessSourceBundleError ()
validateDescriptor descriptor = do
  unique
    (map handoffSourceUnitId (witnessSourceUnits descriptor))
    WitnessSourceBundleDuplicateUnit
  unique
    (map handoffSourceDeclarationSiteId (witnessSourceUnits descriptor))
    WitnessSourceBundleDuplicateDeclarationSite
  unique
    (map handoffSourcePath (witnessSourceUnits descriptor))
    WitnessSourceBundleDuplicateSourcePath
  unique
    (map portableInstanceSiteId (witnessSourceInstanceLineage descriptor))
    WitnessSourceBundleDuplicateInstanceSite
  unique
    (map portableProcessSiteId (witnessSourceProcessLineage descriptor))
    WitnessSourceBundleDuplicateProcessSite
  where
    unique values duplicateError = go Set.empty values
      where
        go _ [] = Right ()
        go seen (value : rest)
          | Set.member value seen = Left (duplicateError value)
          | otherwise = go (Set.insert value seen) rest

materializePhase1WitnessSourceBundle
  :: FilePath
  -> Phase1WitnessSourceBundleDescriptor
  -> IO
      (Either
        Phase1WitnessSourceBundleFileError
        PortableSourceBundle)
materializePhase1WitnessSourceBundle repositoryRoot descriptor = do
  unitsResult <- materializeUnits (witnessSourceUnits descriptor)
  pure $ fmap
    (\units -> PortableSourceBundle
      { portableGrammarRevision = witnessSourceGrammarRevision descriptor
      , portableSelectedProgramRoot = witnessSourceSelectedProgramRoot descriptor
      , portableSourceUnits = units
      , portableInstanceLineage = witnessSourceInstanceLineage descriptor
      , portableProcessLineage = witnessSourceProcessLineage descriptor
      })
    unitsResult
  where
    materializeUnits [] = pure (Right [])
    materializeUnits (unitRef : rest) = do
      unitResult <- materializeUnit unitRef
      case unitResult of
        Left errorValue -> pure (Left errorValue)
        Right unit -> fmap (fmap (unit :)) (materializeUnits rest)

    materializeUnit unitRef = do
      let relativePath = handoffSourcePath unitRef
          path = repositoryPath repositoryRoot relativePath
          unitId = handoffSourceUnitId unitRef
          expected = handoffSourceSha256 unitRef
      digestResult <- sha256File path
      case digestResult of
        Left detail ->
          pure (Left (WitnessSourceBundleSourceUnreadable unitId relativePath detail))
        Right actual
          | actual /= expected ->
              pure (Left
                (WitnessSourceBundleSourceDigestMismatch
                  unitId relativePath expected actual))
          | otherwise -> do
              sourceResult <- try (TextIO.readFile path)
              pure $ case sourceResult of
                Left errorValue ->
                  Left (WitnessSourceBundleSourceUnreadable
                    unitId relativePath (Text.pack (show (errorValue :: IOException))))
                Right source ->
                  Right PortableSourceUnit
                    { portableSourceUnitId = unitId
                    , portableDeclarationSiteId =
                        handoffSourceDeclarationSiteId unitRef
                    , portableDeclarationMetadataKey =
                        handoffSourceDeclarationMetadataKey unitRef
                    , portableSourceText = source
                    }

repositoryPath :: FilePath -> FilePath -> FilePath
repositoryPath root relative
  | null root || root == "." = relative
  | last root == '/' = root <> relative
  | otherwise = root <> "/" <> relative
