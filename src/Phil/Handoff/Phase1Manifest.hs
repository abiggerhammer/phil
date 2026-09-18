{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1Manifest
  ( HandoffArtifactId (..)
  , HandoffArtifactKind (..)
  , HandoffAuthorityRef (..)
  , HandoffArtifact (..)
  , Phase1HandoffManifest (..)
  , Phase1HandoffManifestError (..)
  , Phase1HandoffFileError (..)
  , phase1HandoffFormatV1
  , decodePhase1HandoffManifest
  , checkPhase1HandoffManifestFiles
  , sha256File
  ) where

import Control.Exception (IOException, try)
import qualified Crypto.Hash.SHA256 as SHA256
import Data.Char (isAlphaNum, isControl, isDigit, isSpace)
import qualified Data.ByteString as ByteString
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word8)
import Numeric (showHex)

newtype HandoffArtifactId = HandoffArtifactId
  { unHandoffArtifactId :: Text
  }
  deriving (Eq, Ord, Show)

data HandoffArtifactKind
  = HandoffGrammar
  | HandoffParserCorpus
  | HandoffSourceBundle
  | HandoffWholeSource
  | HandoffCheckedSemantics
  | HandoffArchitectureInstance
  | HandoffVerificationInput
  | HandoffVerificationBundle
  | HandoffEvidence
  | HandoffCertificate
  | HandoffPolicyInput
  | HandoffArchitectureRealization
  | HandoffSystems
  | HandoffStageContract
  | HandoffLowering
  | HandoffCost
  | HandoffAssuranceManifest
  | HandoffConformanceManifest
  | HandoffTCB
  deriving (Eq, Ord, Show)

data HandoffAuthorityRef
  = HandoffMatrixAuthority Text
  | HandoffCertifiedAuthority Text
  deriving (Eq, Ord, Show)

data HandoffArtifact = HandoffArtifact
  { handoffArtifactId :: HandoffArtifactId
  , handoffArtifactKind :: HandoffArtifactKind
  , handoffArtifactPath :: FilePath
  , handoffArtifactSha256 :: Text
  , handoffArtifactAuthorities :: [HandoffAuthorityRef]
  }
  deriving (Eq, Show)

newtype Phase1HandoffManifest = Phase1HandoffManifest
  { handoffArtifacts :: [HandoffArtifact]
  }
  deriving (Eq, Show)

data Phase1HandoffManifestError
  = HandoffManifestEmpty
  | HandoffManifestHeaderMismatch Text
  | HandoffManifestColumnsMismatch Text
  | HandoffManifestMalformedRow Int Text
  | HandoffManifestMalformedArtifactId Int Text
  | HandoffManifestUnknownKind Int Text
  | HandoffManifestMalformedPath Int Text
  | HandoffManifestMalformedDigest Int Text
  | HandoffManifestMalformedAuthority Int Text
  | HandoffManifestDuplicateAuthority Int HandoffAuthorityRef
  | HandoffManifestDuplicateArtifactId HandoffArtifactId
  | HandoffManifestDuplicatePath FilePath
  deriving (Eq, Show)

data Phase1HandoffFileError
  = HandoffArtifactUnreadable HandoffArtifactId FilePath Text
  | HandoffArtifactDigestMismatch HandoffArtifactId FilePath Text Text
  deriving (Eq, Show)

phase1HandoffFormatV1 :: Text
phase1HandoffFormatV1 = "PHIL-PHASE1-HANDOFF-MANIFEST-V1"

manifestColumns :: Text
manifestColumns = Text.intercalate "\t"
  [ "artifact_id"
  , "artifact_kind"
  , "repository_path"
  , "sha256"
  , "governing_authority"
  ]

decodePhase1HandoffManifest
  :: Text
  -> Either Phase1HandoffManifestError Phase1HandoffManifest
decodePhase1HandoffManifest input =
  case Text.lines input of
    [] -> Left HandoffManifestEmpty
    formatLine : rest
      | formatLine /= phase1HandoffFormatV1 ->
          Left (HandoffManifestHeaderMismatch formatLine)
      | otherwise ->
          case rest of
            [] -> Left (HandoffManifestColumnsMismatch "")
            columns : rows
              | columns /= manifestColumns ->
                  Left (HandoffManifestColumnsMismatch columns)
              | otherwise -> do
                  artifacts <- mapM parseRow
                    [ (lineNumber, row)
                    | (lineNumber, row) <- zip [3 ..] rows
                    , let stripped = Text.strip row
                    , not (Text.null stripped)
                    , not ("#" `Text.isPrefixOf` stripped)
                    ]
                  if null artifacts
                    then Left HandoffManifestEmpty
                    else validateUnique artifacts
  where
    parseRow (lineNumber, row) =
      case Text.splitOn "\t" row of
        [rawId, rawKind, rawPath, rawDigest, rawAuthorities] -> do
          artifactId <- parseArtifactId lineNumber rawId
          artifactKind <- parseKind lineNumber rawKind
          artifactPath <- parsePath lineNumber rawPath
          digest <- parseDigest lineNumber rawDigest
          authorities <- parseAuthorities lineNumber rawAuthorities
          Right HandoffArtifact
            { handoffArtifactId = artifactId
            , handoffArtifactKind = artifactKind
            , handoffArtifactPath = artifactPath
            , handoffArtifactSha256 = digest
            , handoffArtifactAuthorities = authorities
            }
        _ -> Left (HandoffManifestMalformedRow lineNumber row)

    validateUnique artifacts = do
      uniqueArtifactIds artifacts
      uniquePaths artifacts
      Right (Phase1HandoffManifest artifacts)

parseArtifactId
  :: Int
  -> Text
  -> Either Phase1HandoffManifestError HandoffArtifactId
parseArtifactId lineNumber raw
  | validToken raw = Right (HandoffArtifactId raw)
  | otherwise = Left (HandoffManifestMalformedArtifactId lineNumber raw)

parseKind
  :: Int
  -> Text
  -> Either Phase1HandoffManifestError HandoffArtifactKind
parseKind lineNumber raw =
  maybe
    (Left (HandoffManifestUnknownKind lineNumber raw))
    Right
    (lookup raw kinds)
  where
    kinds =
      [ ("grammar", HandoffGrammar)
      , ("parser-corpus", HandoffParserCorpus)
      , ("source-bundle", HandoffSourceBundle)
      , ("whole-source", HandoffWholeSource)
      , ("checked-semantics", HandoffCheckedSemantics)
      , ("architecture-instance", HandoffArchitectureInstance)
      , ("verification-input", HandoffVerificationInput)
      , ("verification-bundle", HandoffVerificationBundle)
      , ("evidence", HandoffEvidence)
      , ("certificate", HandoffCertificate)
      , ("policy-input", HandoffPolicyInput)
      , ("architecture-realization", HandoffArchitectureRealization)
      , ("systems", HandoffSystems)
      , ("stage-contract", HandoffStageContract)
      , ("lowering", HandoffLowering)
      , ("cost", HandoffCost)
      , ("assurance-manifest", HandoffAssuranceManifest)
      , ("conformance-manifest", HandoffConformanceManifest)
      , ("tcb", HandoffTCB)
      ]

parsePath
  :: Int
  -> Text
  -> Either Phase1HandoffManifestError FilePath
parsePath lineNumber raw
  | raw /= Text.strip raw = malformed
  | Text.null raw = malformed
  | "/" `Text.isPrefixOf` raw = malformed
  | Text.any (\character -> character == '\\' || isControl character) raw = malformed
  | any invalidSegment (Text.splitOn "/" raw) = malformed
  | otherwise = Right (Text.unpack raw)
  where
    malformed = Left (HandoffManifestMalformedPath lineNumber raw)
    invalidSegment segment =
      Text.null segment || segment == "." || segment == ".."

parseDigest
  :: Int
  -> Text
  -> Either Phase1HandoffManifestError Text
parseDigest lineNumber raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest
      | Text.length digest == 64
      , Text.all lowerHex digest -> Right raw
    _ -> Left (HandoffManifestMalformedDigest lineNumber raw)
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

parseAuthorities
  :: Int
  -> Text
  -> Either Phase1HandoffManifestError [HandoffAuthorityRef]
parseAuthorities lineNumber raw
  | Text.null raw = Left (HandoffManifestMalformedAuthority lineNumber raw)
  | otherwise = do
      refs <- mapM parseAuthority (Text.splitOn ";" raw)
      unique refs
      Right refs
  where
    parseAuthority value
      | value /= Text.strip value =
          Left (HandoffManifestMalformedAuthority lineNumber value)
      | Just caseId <- Text.stripPrefix "matrix:" value
      , validAuthorityToken caseId =
          Right (HandoffMatrixAuthority caseId)
      | Just obligationId <- Text.stripPrefix "certified:" value
      , validAuthorityToken obligationId =
          Right (HandoffCertifiedAuthority obligationId)
      | otherwise =
          Left (HandoffManifestMalformedAuthority lineNumber value)

    unique = go Set.empty
    go _ [] = Right ()
    go seen (ref : rest)
      | Set.member ref seen =
          Left (HandoffManifestDuplicateAuthority lineNumber ref)
      | otherwise = go (Set.insert ref seen) rest

validToken :: Text -> Bool
validToken raw =
  not (Text.null raw)
    && raw == Text.strip raw
    && Text.all allowed raw
  where
    allowed character =
      isAlphaNum character || character `elem` (".-_" :: String)

validAuthorityToken :: Text -> Bool
validAuthorityToken raw =
  not (Text.null raw)
    && raw == Text.strip raw
    && not (Text.any (\character -> isSpace character || isControl character) raw)
    && Text.all (\character -> character /= ';' && character /= '\t') raw

uniqueArtifactIds
  :: [HandoffArtifact]
  -> Either Phase1HandoffManifestError ()
uniqueArtifactIds = go Set.empty
  where
    go _ [] = Right ()
    go seen (artifact : rest)
      | Set.member artifactId seen =
          Left (HandoffManifestDuplicateArtifactId artifactId)
      | otherwise = go (Set.insert artifactId seen) rest
      where
        artifactId = handoffArtifactId artifact

uniquePaths
  :: [HandoffArtifact]
  -> Either Phase1HandoffManifestError ()
uniquePaths = go Set.empty
  where
    go _ [] = Right ()
    go seen (artifact : rest)
      | Set.member path seen = Left (HandoffManifestDuplicatePath path)
      | otherwise = go (Set.insert path seen) rest
      where
        path = handoffArtifactPath artifact

checkPhase1HandoffManifestFiles
  :: FilePath
  -> Phase1HandoffManifest
  -> IO [Phase1HandoffFileError]
checkPhase1HandoffManifestFiles repositoryRoot manifest =
  fmap concat $ mapM checkArtifact (handoffArtifacts manifest)
  where
    checkArtifact artifact = do
      let path = repositoryPath repositoryRoot (handoffArtifactPath artifact)
      actual <- sha256File path
      pure $ case actual of
        Left detail ->
          [ HandoffArtifactUnreadable
              (handoffArtifactId artifact)
              (handoffArtifactPath artifact)
              detail
          ]
        Right digest
          | digest == handoffArtifactSha256 artifact -> []
          | otherwise ->
              [ HandoffArtifactDigestMismatch
                  (handoffArtifactId artifact)
                  (handoffArtifactPath artifact)
                  (handoffArtifactSha256 artifact)
                  digest
              ]

sha256File :: FilePath -> IO (Either Text Text)
sha256File path = do
  readResult <- try (ByteString.readFile path)
  pure $ case readResult of
    Left errorValue ->
      Left (Text.pack (show (errorValue :: IOException)))
    Right bytes ->
      Right ("sha256:" <> renderDigest (SHA256.hash bytes))

repositoryPath :: FilePath -> FilePath -> FilePath
repositoryPath root relative
  | null root || root == "." = relative
  | last root == '/' = root <> relative
  | otherwise = root <> "/" <> relative

renderDigest :: ByteString.ByteString -> Text
renderDigest = Text.pack . concatMap hexByte . ByteString.unpack

hexByte :: Word8 -> String
hexByte value = case showHex value "" of
  [digit] -> ['0', digit]
  digits -> digits
