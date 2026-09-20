{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1AssuranceClosure
  ( Phase1ResidualTCB (..)
  , Phase1AssuranceClosureDecodeError (..)
  , phase1AssuranceManifestFormatV1
  , phase1ResidualTCBFormatV1
  , renderPhase1AssuranceManifest
  , decodePhase1AssuranceManifest
  , derivePhase1ResidualTCB
  , renderPhase1ResidualTCB
  , decodePhase1ResidualTCB
  ) where

import qualified Data.ByteString as ByteString
import Data.Char (isDigit)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Numeric (showHex)
import Phil.Assurance.Types
  ( AssuranceLedger (..)
  , AssuranceManifest (..)
  , AssuranceUseId (..)
  , AssumptionId (..)
  , Digest (..)
  , EvidenceEntryId (..)
  , ExportId (..)
  , RevisionId (..)
  , deriveManifestId
  )
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseArtifact
  , ReleaseProfileRevision (..)
  , ReleaseTrustBoundary (..)
  , ReleaseTrustBoundaryId (..)
  , ReleaseTrustKind (..)
  , certifiedReleaseManifest
  , certifiedReleaseProfile
  , certifiedReleaseTrustBoundaries
  , releaseProfileRequiredTrustKinds
  , releaseProfileRevision
  )

data Phase1ResidualTCB = Phase1ResidualTCB
  { residualTCBManifestId :: Digest
  , residualTCBReleaseProfileRevision :: ReleaseProfileRevision
  , residualTCBRequiredKinds :: Set ReleaseTrustKind
  , residualTCBBoundaries :: Map ReleaseTrustBoundaryId ReleaseTrustBoundary
  }
  deriving (Eq, Show)

newtype Phase1AssuranceClosureDecodeError =
  Phase1AssuranceClosureDecodeError Text
  deriving (Eq, Show)

phase1AssuranceManifestFormatV1 :: Text
phase1AssuranceManifestFormatV1 = "PHIL-PHASE1-ASSURANCE-MANIFEST-V1"

phase1ResidualTCBFormatV1 :: Text
phase1ResidualTCBFormatV1 = "PHIL-PHASE1-RESIDUAL-TCB-V1"

renderPhase1AssuranceManifest :: AssuranceManifest -> Text
renderPhase1AssuranceManifest manifest = Text.unlines $
  [ phase1AssuranceManifestFormatV1
  , row ["manifest-id", digestToken (manifestId manifest)]
  , row ["architecture", digestToken (manifestArchitectureDigest manifest)]
  , row ["phil-core", digestToken (manifestPhilCoreDigest manifest)]
  , row ["implementation", digestToken (manifestImplementationDigest manifest)]
  , row ["target", hexText (manifestTarget manifest)]
  , row ["compilation-profile", hexText (manifestCompilationProfile manifest)]
  , row ["lowering-root", digestToken (manifestLoweringLedgerRoot manifest)]
  ]
  <> map (row . ("obligation" :) . pure . unRevisionId)
      (Set.toAscList (manifestObligationRevisions manifest))
  <> map (row . ("scope" :) . pure . unRevisionId)
      (Set.toAscList (manifestCertificationScope manifest))
  <> map (row . ("evidence" :) . pure . unEvidenceEntryId)
      (Set.toAscList (manifestEvidenceEntries manifest))
  <> map (row . ("assumption" :) . pure . unAssumptionId)
      (Set.toAscList (manifestAssumptionNodes manifest))
  <> map (row . ("export" :) . pure . unExportId)
      (Set.toAscList (manifestExports manifest))
  <> map (row . ("use" :) . pure . unAssuranceUseId)
      (Set.toAscList (manifestAssuranceUses manifest))
  <> [ row ["validity", hexText key, hexText value]
     | (key, value) <- Map.toAscList (manifestValidityContext manifest)
     ]

decodePhase1AssuranceManifest
  :: AssuranceLedger
  -> Text
  -> Either Phase1AssuranceClosureDecodeError AssuranceManifest
decodePhase1AssuranceManifest ledger source = do
  rows <- parseRows phase1AssuranceManifestFormatV1 source
  manifestDigest <- requireDigestRow "manifest-id" rows
  architecture <- requireDigestRow "architecture" rows
  philCore <- requireDigestRow "phil-core" rows
  implementation <- requireDigestRow "implementation" rows
  target <- requireOne "target" rows >>= decodeHex
  profile <- requireOne "compilation-profile" rows >>= decodeHex
  lowering <- requireDigestRow "lowering-root" rows
  obligations <- revisionSet "obligation" rows
  scope <- revisionSet "scope" rows
  evidence <- evidenceSet rows
  assumptions <- assumptionSet rows
  exports <- exportSet rows
  uses <- useSet rows
  validity <- validityMap rows

  requireMembers "obligation revision" obligations (Map.keysSet (ledgerRevisions ledger))
  requireMembers "certification-scope revision" scope (Map.keysSet (ledgerRevisions ledger))
  requireMembers "evidence entry" evidence (Map.keysSet (ledgerEvidence ledger))
  requireMembers "assumption" assumptions (Map.keysSet (ledgerAssumptions ledger))
  requireMembers "export" exports (Map.keysSet (ledgerExports ledger))
  requireMembers "assurance use" uses (Map.keysSet (ledgerUses ledger))

  let manifest = AssuranceManifest
        { manifestId = manifestDigest
        , manifestArchitectureDigest = architecture
        , manifestPhilCoreDigest = philCore
        , manifestImplementationDigest = implementation
        , manifestTarget = target
        , manifestCompilationProfile = profile
        , manifestObligationRevisions = obligations
        , manifestCertificationScope = scope
        , manifestEvidenceEntries = evidence
        , manifestAssumptionNodes = assumptions
        , manifestExports = exports
        , manifestAssuranceUses = uses
        , manifestLoweringLedgerRoot = lowering
        , manifestValidityContext = validity
        }
      derived = deriveManifestId ledger manifest
  if derived == manifestDigest
    then Right manifest
    else malformed
      ("manifest identity mismatch: expected "
        <> digestToken manifestDigest <> ", derived " <> digestToken derived)

derivePhase1ResidualTCB :: CertifiedReleaseArtifact -> Phase1ResidualTCB
derivePhase1ResidualTCB release = Phase1ResidualTCB
  { residualTCBManifestId = manifestId (certifiedReleaseManifest release)
  , residualTCBReleaseProfileRevision =
      releaseProfileRevision (certifiedReleaseProfile release)
  , residualTCBRequiredKinds =
      releaseProfileRequiredTrustKinds (certifiedReleaseProfile release)
  , residualTCBBoundaries = certifiedReleaseTrustBoundaries release
  }

renderPhase1ResidualTCB :: Phase1ResidualTCB -> Text
renderPhase1ResidualTCB value = Text.unlines $
  [ phase1ResidualTCBFormatV1
  , row ["manifest-id", digestToken (residualTCBManifestId value)]
  , row
      [ "release-profile"
      , hexText
          (unReleaseProfileRevision (residualTCBReleaseProfileRevision value))
      ]
  ]
  <> [row ["required-kind", trustKindToken kind]
     | kind <- Set.toAscList (residualTCBRequiredKinds value)]
  <> [ row
        [ "boundary"
        , unReleaseTrustBoundaryId key
        , trustKindToken (releaseTrustKind boundary)
        , hexText (releaseTrustName boundary)
        , hexText (releaseTrustRevision boundary)
        , hexText (releaseTrustBasis boundary)
        ]
     | (key, boundary) <- Map.toAscList (residualTCBBoundaries value)
     ]

decodePhase1ResidualTCB
  :: Text
  -> Either Phase1AssuranceClosureDecodeError Phase1ResidualTCB
decodePhase1ResidualTCB source = do
  rows <- parseRows phase1ResidualTCBFormatV1 source
  manifestDigest <- requireDigestRow "manifest-id" rows
  profile <- requireOne "release-profile" rows >>= decodeHex
  kinds <- trustKinds rows
  boundaries <- trustBoundaries rows
  if Set.null kinds
    then malformed "residual TCB required-kind domain is empty"
    else Right ()
  let actualKinds = Set.fromList (map releaseTrustKind (Map.elems boundaries))
  if actualKinds == kinds
    then Right ()
    else malformed "residual TCB boundary kind domain does not match required-kind domain"
  Right Phase1ResidualTCB
    { residualTCBManifestId = manifestDigest
    , residualTCBReleaseProfileRevision = ReleaseProfileRevision profile
    , residualTCBRequiredKinds = kinds
    , residualTCBBoundaries = boundaries
    }

parseRows
  :: Text
  -> Text
  -> Either Phase1AssuranceClosureDecodeError (Map Text [[Text]])
parseRows expected source =
  case Text.lines source of
    [] -> malformed "empty assurance-closure handoff"
    header : body
      | Text.strip header /= expected ->
          malformed ("unexpected header: " <> Text.strip header)
      | otherwise -> foldRows Map.empty (zip [2 :: Int ..] body)
  where
    foldRows rows [] = Right rows
    foldRows rows ((lineNumber, raw) : rest)
      | Text.null (Text.strip raw) = foldRows rows rest
      | "#" `Text.isPrefixOf` Text.strip raw = foldRows rows rest
      | otherwise = case Text.splitOn "\t" raw of
          [] -> malformedAt lineNumber "empty row"
          key : fields
            | Text.null key -> malformedAt lineNumber "empty row key"
            | otherwise ->
                foldRows (Map.insertWith (<>) key [fields] rows) rest

requireOne
  :: Text
  -> Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError Text
requireOne key rows = case Map.lookup key rows of
  Just [[value]]
    | not (Text.null value) -> Right value
  Nothing -> malformed ("missing row: " <> key)
  _ -> malformed ("duplicate or malformed row: " <> key)

requireDigestRow
  :: Text
  -> Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError Digest
requireDigestRow key rows = requireOne key rows >>= decodeDigest

decodeDigest :: Text -> Either Phase1AssuranceClosureDecodeError Digest
decodeDigest raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest
      | Text.length digest == 64
      , Text.all lowerHex digest -> Right (Digest digest)
    _ -> malformed ("malformed SHA-256 digest: " <> raw)
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

revisionSet
  :: Text
  -> Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError (Set RevisionId)
revisionSet key rows =
  uniqueSet key RevisionId (singleFieldRows key rows)

evidenceSet
  :: Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError (Set EvidenceEntryId)
evidenceSet rows = uniqueSet "evidence" EvidenceEntryId (singleFieldRows "evidence" rows)

assumptionSet
  :: Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError (Set AssumptionId)
assumptionSet rows =
  uniqueSet "assumption" AssumptionId (singleFieldRows "assumption" rows)

exportSet
  :: Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError (Set ExportId)
exportSet rows = uniqueSet "export" ExportId (singleFieldRows "export" rows)

useSet
  :: Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError (Set AssuranceUseId)
useSet rows = uniqueSet "use" AssuranceUseId (singleFieldRows "use" rows)

singleFieldRows
  :: Text
  -> Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError [Text]
singleFieldRows key rows = mapM one (Map.findWithDefault [] key rows)
  where
    one [value]
      | not (Text.null value) = Right value
    one _ = malformed ("malformed row: " <> key)

uniqueSet
  :: Ord a
  => Text
  -> (Text -> a)
  -> Either Phase1AssuranceClosureDecodeError [Text]
  -> Either Phase1AssuranceClosureDecodeError (Set a)
uniqueSet label wrap valuesResult = do
  values <- valuesResult
  let valuesSet = Set.fromList (map wrap values)
  if Set.size valuesSet == length values
    then Right valuesSet
    else malformed ("duplicate " <> label)

validityMap
  :: Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError (Map Text Text)
validityMap rows = do
  pairs <- mapM decodePair (Map.findWithDefault [] "validity" rows)
  let result = Map.fromList pairs
  if Map.size result == length pairs
    then Right result
    else malformed "duplicate validity key"
  where
    decodePair [rawKey, rawValue] = do
      key <- decodeHex rawKey
      value <- decodeHex rawValue
      Right (key, value)
    decodePair _ = malformed "malformed validity row"

trustKinds
  :: Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError (Set ReleaseTrustKind)
trustKinds rows = do
  kinds <- mapM decodeRow (Map.findWithDefault [] "required-kind" rows)
  let result = Set.fromList kinds
  if Set.size result == length kinds
    then Right result
    else malformed "duplicate residual TCB required kind"
  where
    decodeRow [token] = decodeTrustKind token
    decodeRow _ = malformed "malformed required-kind row"

trustBoundaries
  :: Map Text [[Text]]
  -> Either Phase1AssuranceClosureDecodeError
      (Map ReleaseTrustBoundaryId ReleaseTrustBoundary)
trustBoundaries rows = do
  pairs <- mapM decodeBoundary (Map.findWithDefault [] "boundary" rows)
  let result = Map.fromList pairs
  if Map.size result == length pairs
    then Right result
    else malformed "duplicate residual TCB boundary identity"
  where
    decodeBoundary [rawId, rawKind, rawName, rawRevision, rawBasis] = do
      if Text.null rawId
        then malformed "empty residual TCB boundary identity"
        else Right ()
      kind <- decodeTrustKind rawKind
      name <- decodeNonemptyHex "TCB boundary name" rawName
      revision <- decodeNonemptyHex "TCB boundary revision" rawRevision
      basis <- decodeNonemptyHex "TCB boundary basis" rawBasis
      let key = ReleaseTrustBoundaryId rawId
      Right
        ( key
        , ReleaseTrustBoundary
            { releaseTrustBoundaryId = key
            , releaseTrustKind = kind
            , releaseTrustName = name
            , releaseTrustRevision = revision
            , releaseTrustBasis = basis
            }
        )
    decodeBoundary _ = malformed "malformed residual TCB boundary row"

decodeNonemptyHex
  :: Text
  -> Text
  -> Either Phase1AssuranceClosureDecodeError Text
decodeNonemptyHex label raw = do
  value <- decodeHex raw
  if Text.null (Text.strip value)
    then malformed (label <> " is empty")
    else Right value

trustKindToken :: ReleaseTrustKind -> Text
trustKindToken kind = case kind of
  CompilerCheckerTrust -> "compiler-checker"
  LLVMToolchainTrust -> "llvm-toolchain"
  RuntimeTrust -> "runtime"
  ProviderTrust -> "provider"
  ExternalCheckerTrust -> "external-checker"
  TargetAssumptionTrust -> "target-assumption"

decodeTrustKind
  :: Text
  -> Either Phase1AssuranceClosureDecodeError ReleaseTrustKind
decodeTrustKind token = case token of
  "compiler-checker" -> Right CompilerCheckerTrust
  "llvm-toolchain" -> Right LLVMToolchainTrust
  "runtime" -> Right RuntimeTrust
  "provider" -> Right ProviderTrust
  "external-checker" -> Right ExternalCheckerTrust
  "target-assumption" -> Right TargetAssumptionTrust
  _ -> malformed ("unknown residual TCB kind: " <> token)

requireMembers
  :: (Ord a, Show a)
  => Text
  -> Set a
  -> Set a
  -> Either Phase1AssuranceClosureDecodeError ()
requireMembers label selected available =
  case Set.lookupMin (selected `Set.difference` available) of
    Nothing -> Right ()
    Just missing -> malformed
      (label <> " is not present in selected assurance ledger: "
        <> Text.pack (show missing))

hexText :: Text -> Text
hexText value =
  Text.pack (concatMap hexByte (ByteString.unpack (TextEncoding.encodeUtf8 value)))
  where
    hexByte byte = case showHex byte "" of
      [digit] -> ['0', digit]
      digits -> digits

decodeHex :: Text -> Either Phase1AssuranceClosureDecodeError Text
decodeHex raw
  | odd (Text.length raw) = malformed "odd-length canonical hex text"
  | Text.any (not . lowerHex) raw = malformed "invalid canonical hex text"
  | otherwise =
      case TextEncoding.decodeUtf8' (ByteString.pack (decodeBytes (Text.unpack raw))) of
        Left _ -> malformed "canonical hex text is not valid UTF-8"
        Right value -> Right value
  where
    decodeBytes [] = []
    decodeBytes (high : low : rest) =
      fromIntegral (hexValue high * 16 + hexValue low) : decodeBytes rest
    decodeBytes _ = []

    hexValue character
      | isDigit character = fromEnum character - fromEnum '0'
      | otherwise = 10 + fromEnum character - fromEnum 'a'

    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

digestToken :: Digest -> Text
digestToken (Digest value) = "sha256:" <> value

row :: [Text] -> Text
row = Text.intercalate "\t"

malformed :: Text -> Either Phase1AssuranceClosureDecodeError a
malformed = Left . Phase1AssuranceClosureDecodeError

malformedAt :: Int -> Text -> Either Phase1AssuranceClosureDecodeError a
malformedAt lineNumber detail =
  malformed ("line " <> Text.pack (show lineNumber) <> ": " <> detail)
