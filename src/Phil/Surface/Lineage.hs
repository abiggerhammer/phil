{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Lineage
  ( SourceUnitId (..)
  , DeclarationSiteId (..)
  , InstanceLineageSiteId (..)
  , ProcessLineageSiteId (..)
  , GrammarRevision (..)
  , canonicalGrammarRevisionV1
  , PortableSourceUnit (..)
  , PortableInstanceLineage (..)
  , PortableProcessLineage (..)
  , PortableSourceBundle (..)
  , ResolvedSourceBundleLineage (..)
  , LineageError (..)
  , decodePortableSourceBundle
  , decodePortableSourceBundleForGrammar
  , resolveSourceBundleLineage
  ) where

import Control.Monad (foldM)
import Data.Char (isAlphaNum, isControl, isDigit, isLetter, isSpace)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Process (ProcessKey (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , InstanceKey (..)
  )

-- | Stable identifiers used only by the portable SourceBundle interchange
-- fixture. They locate carriers; they are never themselves semantic lineage.
newtype SourceUnitId = SourceUnitId { unSourceUnitId :: Text }
  deriving (Eq, Ord, Show)

newtype DeclarationSiteId = DeclarationSiteId { unDeclarationSiteId :: Text }
  deriving (Eq, Ord, Show)

newtype InstanceLineageSiteId = InstanceLineageSiteId { unInstanceLineageSiteId :: Text }
  deriving (Eq, Ord, Show)

newtype ProcessLineageSiteId = ProcessLineageSiteId { unProcessLineageSiteId :: Text }
  deriving (Eq, Ord, Show)

-- | Exact concrete-grammar identity carried by a portable SourceBundle.
-- Grammar compatibility is not inferred from this value: Phase 1 accepts only
-- the exact revision selected by the current front end.
newtype GrammarRevision = GrammarRevision { unGrammarRevision :: Text }
  deriving (Eq, Ord, Show)

canonicalGrammarRevisionV1 :: GrammarRevision
canonicalGrammarRevisionV1 = GrammarRevision "sha256:1bc73beb296475f96d739181c0a7609eaf53a61362b2aa0cf7bd7184d06e67ac"

-- | Implementation-independent SourceBundle fixture record. The metadata key is
-- deliberately kept as text until the lineage competence check validates it.
data PortableSourceUnit = PortableSourceUnit
  { portableSourceUnitId :: SourceUnitId
  , portableDeclarationSiteId :: DeclarationSiteId
  , portableDeclarationMetadataKey :: Maybe Text
  , portableSourceText :: Text
  }
  deriving (Eq, Show)

data PortableInstanceLineage = PortableInstanceLineage
  { portableInstanceSiteId :: InstanceLineageSiteId
  , portableInstanceMetadataKey :: Text
  }
  deriving (Eq, Show)

data PortableProcessLineage = PortableProcessLineage
  { portableProcessSiteId :: ProcessLineageSiteId
  , portableProcessMetadataKey :: Text
  }
  deriving (Eq, Show)

data PortableSourceBundle = PortableSourceBundle
  { portableGrammarRevision :: GrammarRevision
  , portableSelectedProgramRoot :: Text
  , portableSourceUnits :: [PortableSourceUnit]
  , portableInstanceLineage :: [PortableInstanceLineage]
  , portableProcessLineage :: [PortableProcessLineage]
  }
  deriving (Eq, Show)

data ResolvedSourceBundleLineage = ResolvedSourceBundleLineage
  { resolvedDeclarationKeys :: Map DeclarationSiteId DeclarationKey
  , resolvedInstanceKeys :: Map InstanceLineageSiteId InstanceKey
  , resolvedProcessKeys :: Map ProcessLineageSiteId ProcessKey
  }
  deriving (Eq, Show)

data LineageError
  = InvalidBundleHeader Text
  | MissingGrammarRevision
  | DuplicateGrammarRevision GrammarRevision GrammarRevision
  | MalformedGrammarRevision Text
  | IncompatibleGrammarRevision GrammarRevision GrammarRevision
  | MissingSelectedProgramRoot
  | DuplicateSelectedProgramRoot Text Text
  | MalformedPortableRecord Int Text
  | DuplicateSourceUnit SourceUnitId
  | DuplicateDeclarationSite DeclarationSiteId
  | DuplicateInstanceLineageSite InstanceLineageSiteId
  | DuplicateProcessLineageSite ProcessLineageSiteId
  | EmptySourceUnit DeclarationSiteId
  | MalformedAttributeSyntax DeclarationSiteId Text
  | UnknownSemanticAttribute DeclarationSiteId Text
  | DuplicateDeclarationKeyAttribute DeclarationSiteId
  | ConflictingDeclarationLineage DeclarationSiteId DeclarationKey DeclarationKey
  | MissingDeclarationLineage DeclarationSiteId
  | MalformedDeclarationKey DeclarationSiteId Text
  | MalformedInstanceKey InstanceLineageSiteId Text
  | MalformedProcessKey ProcessLineageSiteId Text
  | DuplicateDeclarationKey DeclarationKey DeclarationSiteId DeclarationSiteId
  | DuplicateInstanceKey InstanceKey InstanceLineageSiteId InstanceLineageSiteId
  | DuplicateProcessKey ProcessKey ProcessLineageSiteId ProcessLineageSiteId
  deriving (Eq, Show)

portableHeader :: Text
portableHeader = "PHIL-SOURCE-BUNDLE-LINEAGE-V1"

validateGrammarRevision :: Text -> Either LineageError GrammarRevision
validateGrammarRevision raw =
  case Text.stripPrefix "sha256:" raw of
    Just digestValue
      | raw == Text.strip raw
      , Text.length digestValue == 64
      , Text.all isLowerHex digestValue -> Right (GrammarRevision raw)
    _ -> Left (MalformedGrammarRevision raw)
  where
    isLowerHex character = isDigit character || (character >= 'a' && character <= 'f')

data DecodeState = DecodeState
  { decodeGrammar :: Maybe GrammarRevision
  , decodeRoot :: Maybe Text
  , decodeUnits :: [PortableSourceUnit]
  , decodeInstances :: [PortableInstanceLineage]
  , decodeProcesses :: [PortableProcessLineage]
  }

emptyDecodeState :: DecodeState
emptyDecodeState = DecodeState
  { decodeGrammar = Nothing
  , decodeRoot = Nothing
  , decodeUnits = []
  , decodeInstances = []
  , decodeProcesses = []
  }

-- | Decode the bounded, line-oriented Phase-1 conformance/handoff fixture.
-- This is test/interchange infrastructure, not permanent Phil source syntax or
-- a commitment to a long-term stable-key wire encoding.
decodePortableSourceBundle :: Text -> Either LineageError PortableSourceBundle
decodePortableSourceBundle = decodePortableSourceBundleForGrammar canonicalGrammarRevisionV1

-- | Decode for one explicitly selected concrete-grammar revision. Phase 1 has
-- no implicit migration or compatibility relation: a different exact digest is
-- an incompatible input and fails before source lineage can be resolved.
decodePortableSourceBundleForGrammar
  :: GrammarRevision
  -> Text
  -> Either LineageError PortableSourceBundle
decodePortableSourceBundleForGrammar expectedGrammar input =
  case Text.lines input of
    [] -> Left (InvalidBundleHeader "")
    header : records
      | Text.strip header /= portableHeader ->
          Left (InvalidBundleHeader (Text.strip header))
      | otherwise -> do
          decoded <- foldM decodeRecord emptyDecodeState (zip [2 ..] records)
          grammarRevision <- maybe (Left MissingGrammarRevision) Right (decodeGrammar decoded)
          if grammarRevision == expectedGrammar
            then Right ()
            else Left (IncompatibleGrammarRevision expectedGrammar grammarRevision)
          root <- maybe (Left MissingSelectedProgramRoot) Right (decodeRoot decoded)
          Right PortableSourceBundle
            { portableGrammarRevision = grammarRevision
            , portableSelectedProgramRoot = root
            , portableSourceUnits = reverse (decodeUnits decoded)
            , portableInstanceLineage = reverse (decodeInstances decoded)
            , portableProcessLineage = reverse (decodeProcesses decoded)
            }

decodeRecord :: DecodeState -> (Int, Text) -> Either LineageError DecodeState
decodeRecord state (lineNumber, rawLine)
  | Text.null stripped = Right state
  | "#" `Text.isPrefixOf` stripped = Right state
  | otherwise =
      case Text.splitOn "\t" rawLine of
        ["grammar", rawRevision] -> do
          revisionValue <- validateGrammarRevision (Text.strip rawRevision)
          case decodeGrammar state of
            Nothing -> Right state { decodeGrammar = Just revisionValue }
            Just existing -> Left (DuplicateGrammarRevision existing revisionValue)
        ["root", root] ->
          let root' = Text.strip root
          in if Text.null root'
              then malformed
              else case decodeRoot state of
                Nothing -> Right state { decodeRoot = Just root' }
                Just existing -> Left (DuplicateSelectedProgramRoot existing root')
        ["unit", unitId, siteId, metadataKey, source] ->
          if any (Text.null . Text.strip) [unitId, siteId] || Text.null (Text.strip source)
            then malformed
            else Right state
              { decodeUnits = PortableSourceUnit
                  { portableSourceUnitId = SourceUnitId (Text.strip unitId)
                  , portableDeclarationSiteId = DeclarationSiteId (Text.strip siteId)
                  , portableDeclarationMetadataKey =
                      case Text.strip metadataKey of
                        "-" -> Nothing
                        value -> Just value
                  , portableSourceText = Text.strip source
                  }
                  : decodeUnits state
              }
        ["instance", siteId, key] ->
          if any (Text.null . Text.strip) [siteId, key]
            then malformed
            else Right state
              { decodeInstances = PortableInstanceLineage
                  (InstanceLineageSiteId (Text.strip siteId))
                  (Text.strip key)
                  : decodeInstances state
              }
        ["process", siteId, key] ->
          if any (Text.null . Text.strip) [siteId, key]
            then malformed
            else Right state
              { decodeProcesses = PortableProcessLineage
                  (ProcessLineageSiteId (Text.strip siteId))
                  (Text.strip key)
                  : decodeProcesses state
              }
        _ -> malformed
  where
    stripped = Text.strip rawLine
    malformed = Left (MalformedPortableRecord lineNumber rawLine)

-- | Resolve only persisted lineage competence. No fallback derives identity
-- from display names, source-unit IDs, declaration-site IDs, source text,
-- source positions, selected-root spelling, or container order.
resolveSourceBundleLineage
  :: PortableSourceBundle
  -> Either LineageError ResolvedSourceBundleLineage
resolveSourceBundleLineage bundle = do
  declarationKeys <- resolveDeclarations (portableSourceUnits bundle)
  instanceKeys <- resolveInstances (portableInstanceLineage bundle)
  processKeys <- resolveProcesses (portableProcessLineage bundle)
  Right ResolvedSourceBundleLineage
    { resolvedDeclarationKeys = declarationKeys
    , resolvedInstanceKeys = instanceKeys
    , resolvedProcessKeys = processKeys
    }

resolveDeclarations
  :: [PortableSourceUnit]
  -> Either LineageError (Map DeclarationSiteId DeclarationKey)
resolveDeclarations units = do
  (_, sites, _) <- foldM addUnit (Set.empty, Map.empty, Map.empty) units
  Right sites
  where
    addUnit
      :: (Set SourceUnitId, Map DeclarationSiteId DeclarationKey, Map DeclarationKey DeclarationSiteId)
      -> PortableSourceUnit
      -> Either LineageError
          (Set SourceUnitId, Map DeclarationSiteId DeclarationKey, Map DeclarationKey DeclarationSiteId)
    addUnit (seenUnits, bySite, byKey) unit = do
      let unitId = portableSourceUnitId unit
          siteId = portableDeclarationSiteId unit
      if Set.member unitId seenUnits
        then Left (DuplicateSourceUnit unitId)
        else Right ()
      if Map.member siteId bySite
        then Left (DuplicateDeclarationSite siteId)
        else Right ()
      key <- resolveDeclarationKey unit
      case Map.lookup key byKey of
        Just previousSite -> Left (DuplicateDeclarationKey key previousSite siteId)
        Nothing -> Right
          ( Set.insert unitId seenUnits
          , Map.insert siteId key bySite
          , Map.insert key siteId byKey
          )

resolveDeclarationKey :: PortableSourceUnit -> Either LineageError DeclarationKey
resolveDeclarationKey unit = do
  let siteId = portableDeclarationSiteId unit
      source = portableSourceText unit
  if Text.null (Text.strip source)
    then Left (EmptySourceUnit siteId)
    else Right ()
  (attributes, declarationRemainder) <- parseLeadingAttributes siteId source
  if Text.null (Text.strip declarationRemainder)
    then Left (EmptySourceUnit siteId)
    else Right ()
  case [ name | SourceAttribute name _ <- attributes, name /= "key" ] of
    unknown : _ -> Left (UnknownSemanticAttribute siteId unknown)
    [] -> Right ()
  inlineRaw <- case [ value | SourceAttribute "key" value <- attributes ] of
    [] -> Right Nothing
    [value] -> Just <$> validateDeclarationKey siteId value
    _ -> Left (DuplicateDeclarationKeyAttribute siteId)
  metadataKey <- traverse (validateDeclarationKey siteId) (portableDeclarationMetadataKey unit)
  case (inlineRaw, metadataKey) of
    (Nothing, Nothing) -> Left (MissingDeclarationLineage siteId)
    (Just inlineKey, Nothing) -> Right inlineKey
    (Nothing, Just persistedKey) -> Right persistedKey
    (Just inlineKey, Just persistedKey)
      | inlineKey == persistedKey -> Right inlineKey
      | otherwise -> Left
          (ConflictingDeclarationLineage siteId inlineKey persistedKey)

data SourceAttribute = SourceAttribute Text Text
  deriving (Eq, Show)

parseLeadingAttributes
  :: DeclarationSiteId
  -> Text
  -> Either LineageError ([SourceAttribute], Text)
parseLeadingAttributes siteId = go [] . Text.stripStart
  where
    go attributes remaining =
      case Text.stripPrefix "@" remaining of
        Nothing -> Right (reverse attributes, remaining)
        Just afterAt -> do
          (name, afterName) <- parseAttributeIdentifier siteId (Text.stripStart afterAt)
          afterOpen <- requireToken "(" siteId (Text.stripStart afterName)
          (value, afterString) <- parseAttributeString siteId (Text.stripStart afterOpen)
          afterClose <- requireToken ")" siteId (Text.stripStart afterString)
          go (SourceAttribute name value : attributes) (Text.stripStart afterClose)

parseAttributeIdentifier
  :: DeclarationSiteId
  -> Text
  -> Either LineageError (Text, Text)
parseAttributeIdentifier siteId input =
  case Text.uncons input of
    Just (first, rest)
      | isLetter first || first == '_' ->
          let (suffix, remaining) = Text.span identifierContinue rest
          in Right (Text.cons first suffix, remaining)
    _ -> Left (MalformedAttributeSyntax siteId input)
  where
    identifierContinue character =
      isAlphaNum character || character == '_' || character == '\''

requireToken
  :: Text
  -> DeclarationSiteId
  -> Text
  -> Either LineageError Text
requireToken token siteId input =
  maybe
    (Left (MalformedAttributeSyntax siteId input))
    Right
    (Text.stripPrefix token input)

parseAttributeString
  :: DeclarationSiteId
  -> Text
  -> Either LineageError (Text, Text)
parseAttributeString siteId input =
  case Text.stripPrefix "\"" input of
    Nothing -> Left (MalformedAttributeSyntax siteId input)
    Just body -> go [] body
  where
    go reversed remaining =
      case Text.uncons remaining of
        Nothing -> Left (MalformedAttributeSyntax siteId input)
        Just ('\"', rest) -> Right (Text.pack (reverse reversed), rest)
        Just ('\\', rest) ->
          case Text.uncons rest of
            Just ('\"', tail') -> go ('\"' : reversed) tail'
            Just ('\\', tail') -> go ('\\' : reversed) tail'
            Just ('n', tail') -> go ('\n' : reversed) tail'
            Just ('r', tail') -> go ('\r' : reversed) tail'
            Just ('t', tail') -> go ('\t' : reversed) tail'
            _ -> Left (MalformedAttributeSyntax siteId input)
        Just (character, rest)
          | isControl character -> Left (MalformedAttributeSyntax siteId input)
          | otherwise -> go (character : reversed) rest

validateDeclarationKey
  :: DeclarationSiteId
  -> Text
  -> Either LineageError DeclarationKey
validateDeclarationKey siteId raw
  | validPortableKey "decl:" raw = Right (DeclarationKey raw)
  | otherwise = Left (MalformedDeclarationKey siteId raw)

validateInstanceKey
  :: InstanceLineageSiteId
  -> Text
  -> Either LineageError InstanceKey
validateInstanceKey siteId raw
  | validPortableKey "inst:" raw = Right (InstanceKey raw)
  | otherwise = Left (MalformedInstanceKey siteId raw)

validateProcessKey
  :: ProcessLineageSiteId
  -> Text
  -> Either LineageError ProcessKey
validateProcessKey siteId raw
  | validPortableKey "proc:" raw = Right (ProcessKey raw)
  | otherwise = Left (MalformedProcessKey siteId raw)

-- These prefixes belong only to the portable conformance fixture encoding. They
-- deliberately do not settle Phil's eventual cryptographic key representation.
validPortableKey :: Text -> Text -> Bool
validPortableKey prefix raw =
  raw == Text.strip raw
    && prefix `Text.isPrefixOf` raw
    && Text.length raw > Text.length prefix
    && not (Text.any (\character -> isSpace character || isControl character) raw)

resolveInstances
  :: [PortableInstanceLineage]
  -> Either LineageError (Map InstanceLineageSiteId InstanceKey)
resolveInstances records = do
  (bySite, _) <- foldM addInstance (Map.empty, Map.empty) records
  Right bySite
  where
    addInstance (bySite, byKey) record = do
      let siteId = portableInstanceSiteId record
      if Map.member siteId bySite
        then Left (DuplicateInstanceLineageSite siteId)
        else Right ()
      key <- validateInstanceKey siteId (portableInstanceMetadataKey record)
      case Map.lookup key byKey of
        Just previousSite -> Left (DuplicateInstanceKey key previousSite siteId)
        Nothing -> Right (Map.insert siteId key bySite, Map.insert key siteId byKey)

resolveProcesses
  :: [PortableProcessLineage]
  -> Either LineageError (Map ProcessLineageSiteId ProcessKey)
resolveProcesses records = do
  (bySite, _) <- foldM addProcess (Map.empty, Map.empty) records
  Right bySite
  where
    addProcess (bySite, byKey) record = do
      let siteId = portableProcessSiteId record
      if Map.member siteId bySite
        then Left (DuplicateProcessLineageSite siteId)
        else Right ()
      key <- validateProcessKey siteId (portableProcessMetadataKey record)
      case Map.lookup key byKey of
        Just previousSite -> Left (DuplicateProcessKey key previousSite siteId)
        Nothing -> Right (Map.insert siteId key bySite, Map.insert key siteId byKey)
