{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.DistributionRelease
  ( DistributionReleaseRevision (..)
  , DistributionArchiveRevision (..)
  , DistributionTrustKind (..)
  , DistributionTrustBoundaryId (..)
  , DistributionTrustBoundary (..)
  , Phase1DistributionRelease
  , Phase1DistributionArchive
  , DistributionReleaseError (..)
  , phase1DistributionReleaseRevisionV1
  , phase1DistributionArchiveRevisionV1
  , requiredPhase1DistributionTrustKinds
  , phase1LinuxDistributionTrust
  , distributionReleaseId
  , distributionReleasePackageName
  , distributionReleasePackageVersion
  , distributionReleaseTarget
  , distributionReleaseSourceCommit
  , distributionReleaseHandoffManifestDigest
  , distributionReleaseCompilerDigest
  , distributionReleaseTrustBoundaries
  , distributionArchiveId
  , distributionArchiveReleaseId
  , distributionArchiveName
  , distributionArchiveDigest
  , distributionArchivePackageManifestDigest
  , buildPhase1DistributionRelease
  , buildPhase1DistributionArchive
  , renderPhase1DistributionRelease
  , renderPhase1DistributionArchive
  , parseSha256Digest
  , parseRenderedDistributionReleaseId
  ) where

import Data.Char (isDigit)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest (..), digestText)

newtype DistributionReleaseRevision = DistributionReleaseRevision
  { unDistributionReleaseRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype DistributionArchiveRevision = DistributionArchiveRevision
  { unDistributionArchiveRevision :: Text
  }
  deriving (Eq, Ord, Show)

data DistributionTrustKind
  = DistributionCompilerCheckerTrust
  | DistributionBuildToolchainTrust
  | DistributionLLVMToolchainTrust
  | DistributionTargetAssumptionTrust
  deriving (Eq, Ord, Show)

newtype DistributionTrustBoundaryId = DistributionTrustBoundaryId
  { unDistributionTrustBoundaryId :: Text
  }
  deriving (Eq, Ord, Show)

data DistributionTrustBoundary = DistributionTrustBoundary
  { distributionTrustBoundaryId :: DistributionTrustBoundaryId
  , distributionTrustKind :: DistributionTrustKind
  , distributionTrustName :: Text
  , distributionTrustRevision :: Text
  , distributionTrustBasis :: Text
  }
  deriving (Eq, Ord, Show)

data Phase1DistributionRelease = Phase1DistributionRelease
  { distributionReleaseId :: Digest
  , distributionReleasePackageName :: Text
  , distributionReleasePackageVersion :: Text
  , distributionReleaseTarget :: Text
  , distributionReleaseSourceCommit :: Text
  , distributionReleaseHandoffManifestDigest :: Digest
  , distributionReleaseCompilerDigest :: Digest
  , distributionReleaseTrustBoundaries
      :: Map DistributionTrustBoundaryId DistributionTrustBoundary
  }
  deriving (Eq, Show)

data Phase1DistributionArchive = Phase1DistributionArchive
  { distributionArchiveId :: Digest
  , distributionArchiveReleaseId :: Digest
  , distributionArchiveName :: Text
  , distributionArchiveDigest :: Digest
  , distributionArchivePackageManifestDigest :: Digest
  }
  deriving (Eq, Show)

data DistributionReleaseError
  = DistributionReleaseBlankPackageName
  | DistributionReleaseBlankPackageVersion
  | DistributionReleaseBlankTarget
  | DistributionReleaseMalformedSourceCommit Text
  | DistributionReleaseMalformedDigest Text
  | DistributionReleaseDuplicateTrustBoundary DistributionTrustBoundaryId
  | DistributionReleaseEmptyTrustBoundaryId
  | DistributionReleaseEmptyTrustName DistributionTrustBoundaryId
  | DistributionReleaseEmptyTrustRevision DistributionTrustBoundaryId
  | DistributionReleaseEmptyTrustBasis DistributionTrustBoundaryId
  | DistributionReleaseTrustKindDomainMismatch
      (Set DistributionTrustKind)
      (Set DistributionTrustKind)
  | DistributionArchiveBlankName
  deriving (Eq, Show)

phase1DistributionReleaseRevisionV1 :: DistributionReleaseRevision
phase1DistributionReleaseRevisionV1 =
  DistributionReleaseRevision "phase1.int011.distribution-release.v1"

phase1DistributionArchiveRevisionV1 :: DistributionArchiveRevision
phase1DistributionArchiveRevisionV1 =
  DistributionArchiveRevision "phase1.int011.distribution-archive.v1"

requiredPhase1DistributionTrustKinds :: Set DistributionTrustKind
requiredPhase1DistributionTrustKinds = Set.fromList
  [ DistributionCompilerCheckerTrust
  , DistributionBuildToolchainTrust
  , DistributionLLVMToolchainTrust
  , DistributionTargetAssumptionTrust
  ]

phase1LinuxDistributionTrust :: [DistributionTrustBoundary]
phase1LinuxDistributionTrust =
  [ trust "compiler-checker" DistributionCompilerCheckerTrust
      "Phil Haskell compiler/checker"
      "phase1-current"
      "first implementation remains trusted until Phase 2"
  , trust "build-toolchain" DistributionBuildToolchainTrust
      "GHC and conventional x86-64 Linux host linker/runtime"
      "ghc-9.6.7+phase1-linux-host-v1"
      "native philc executable is built by the conventional Haskell host toolchain"
  , trust "llvm-toolchain" DistributionLLVMToolchainTrust
      "LLVM semantics and conventional LLVM 18.x tooling"
      "LLVM 18.x"
      "emitted LLVM remains subject to the declared LLVM language/tool boundary"
  , trust "target-assumptions" DistributionTargetAssumptionTrust
      "x86_64 Linux distribution target assumptions"
      "phase1-x86_64-linux-v1"
      "selected host ABI, loader, operating-system, and runtime assumptions"
  ]
  where
    trust ident kind name revision basis = DistributionTrustBoundary
      { distributionTrustBoundaryId = DistributionTrustBoundaryId ident
      , distributionTrustKind = kind
      , distributionTrustName = name
      , distributionTrustRevision = revision
      , distributionTrustBasis = basis
      }

buildPhase1DistributionRelease
  :: Text
  -> Text
  -> Text
  -> Text
  -> Digest
  -> Digest
  -> [DistributionTrustBoundary]
  -> Either DistributionReleaseError Phase1DistributionRelease
buildPhase1DistributionRelease packageName version target sourceCommit handoff compiler trust = do
  if blank packageName then Left DistributionReleaseBlankPackageName else Right ()
  if blank version then Left DistributionReleaseBlankPackageVersion else Right ()
  if blank target then Left DistributionReleaseBlankTarget else Right ()
  if validSourceCommit sourceCommit
    then Right ()
    else Left (DistributionReleaseMalformedSourceCommit sourceCommit)
  validateDigest handoff
  validateDigest compiler
  boundaries <- validateTrust trust
  let provisional = Phase1DistributionRelease
        { distributionReleaseId = Digest ""
        , distributionReleasePackageName = packageName
        , distributionReleasePackageVersion = version
        , distributionReleaseTarget = target
        , distributionReleaseSourceCommit = sourceCommit
        , distributionReleaseHandoffManifestDigest = handoff
        , distributionReleaseCompilerDigest = compiler
        , distributionReleaseTrustBoundaries = boundaries
        }
      releaseId = digestText (renderDistributionReleaseBody provisional)
  Right (provisional { distributionReleaseId = releaseId })

buildPhase1DistributionArchive
  :: Digest
  -> Text
  -> Digest
  -> Digest
  -> Either DistributionReleaseError Phase1DistributionArchive
buildPhase1DistributionArchive releaseId archiveName archiveDigest packageManifestDigest = do
  validateDigest releaseId
  validateDigest archiveDigest
  validateDigest packageManifestDigest
  if blank archiveName then Left DistributionArchiveBlankName else Right ()
  let provisional = Phase1DistributionArchive
        { distributionArchiveId = Digest ""
        , distributionArchiveReleaseId = releaseId
        , distributionArchiveName = archiveName
        , distributionArchiveDigest = archiveDigest
        , distributionArchivePackageManifestDigest = packageManifestDigest
        }
      bindingId = digestText (renderDistributionArchiveBody provisional)
  Right (provisional { distributionArchiveId = bindingId })

renderPhase1DistributionRelease :: Phase1DistributionRelease -> Text
renderPhase1DistributionRelease release = Text.unlines
  [ "PHIL-PHASE1-DISTRIBUTION-RELEASE-V1"
  , recordLine "release" [("id", digestToken (distributionReleaseId release))]
  , renderDistributionReleaseBody release
  ]

renderDistributionReleaseBody :: Phase1DistributionRelease -> Text
renderDistributionReleaseBody release = Text.unlines $
  [ recordLine "format"
      [("revision", unDistributionReleaseRevision phase1DistributionReleaseRevisionV1)]
  , recordLine "package"
      [ ("name", distributionReleasePackageName release)
      , ("version", distributionReleasePackageVersion release)
      , ("target", distributionReleaseTarget release)
      ]
  , recordLine "source"
      [("commit", distributionReleaseSourceCommit release)]
  , recordLine "handoff"
      [("sha256", digestToken (distributionReleaseHandoffManifestDigest release))]
  , recordLine "compiler"
      [("sha256", digestToken (distributionReleaseCompilerDigest release))]
  ]
  <> map renderTrust
      (Map.toAscList (distributionReleaseTrustBoundaries release))
  where
    renderTrust (key, boundary) = recordLine "tcb"
      [ ("id", unDistributionTrustBoundaryId key)
      , ("kind", trustKindToken (distributionTrustKind boundary))
      , ("name", distributionTrustName boundary)
      , ("revision", distributionTrustRevision boundary)
      , ("basis", distributionTrustBasis boundary)
      ]

renderPhase1DistributionArchive :: Phase1DistributionArchive -> Text
renderPhase1DistributionArchive binding = Text.unlines
  [ "PHIL-PHASE1-DISTRIBUTION-ARCHIVE-V1"
  , recordLine "archive-binding"
      [("id", digestToken (distributionArchiveId binding))]
  , renderDistributionArchiveBody binding
  ]

renderDistributionArchiveBody :: Phase1DistributionArchive -> Text
renderDistributionArchiveBody binding = Text.unlines
  [ recordLine "format"
      [("revision", unDistributionArchiveRevision phase1DistributionArchiveRevisionV1)]
  , recordLine "release"
      [("id", digestToken (distributionArchiveReleaseId binding))]
  , recordLine "archive"
      [ ("name", distributionArchiveName binding)
      , ("sha256", digestToken (distributionArchiveDigest binding))
      ]
  , recordLine "package-manifest"
      [("sha256", digestToken (distributionArchivePackageManifestDigest binding))]
  ]

parseSha256Digest :: Text -> Either DistributionReleaseError Digest
parseSha256Digest raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest
      | validDigestText digest -> Right (Digest digest)
    _ -> Left (DistributionReleaseMalformedDigest raw)

parseRenderedDistributionReleaseId
  :: Text
  -> Either DistributionReleaseError Digest
parseRenderedDistributionReleaseId source =
  case
      [ value
      | line <- Text.lines source
      , ["release", field] <- [Text.splitOn "\t" line]
      , Just value <- [Text.stripPrefix "id=" field]
      ] of
    [raw] -> parseSha256Digest raw
    _ -> Left (DistributionReleaseMalformedDigest "missing/duplicate release id")

validateDigest :: Digest -> Either DistributionReleaseError ()
validateDigest (Digest value)
  | validDigestText value = Right ()
  | otherwise = Left (DistributionReleaseMalformedDigest value)

validateTrust
  :: [DistributionTrustBoundary]
  -> Either
      DistributionReleaseError
      (Map DistributionTrustBoundaryId DistributionTrustBoundary)
validateTrust values = do
  mapM_ validateBoundary values
  case firstDuplicate (map distributionTrustBoundaryId values) of
    Just duplicateId -> Left (DistributionReleaseDuplicateTrustBoundary duplicateId)
    Nothing -> Right ()
  let actualKinds = Set.fromList (map distributionTrustKind values)
  if actualKinds /= requiredPhase1DistributionTrustKinds
    then Left
      (DistributionReleaseTrustKindDomainMismatch
        requiredPhase1DistributionTrustKinds
        actualKinds)
    else Right (Map.fromList
      [(distributionTrustBoundaryId value, value) | value <- values])
  where
    validateBoundary boundary
      | blank (unDistributionTrustBoundaryId (distributionTrustBoundaryId boundary)) =
          Left DistributionReleaseEmptyTrustBoundaryId
      | blank (distributionTrustName boundary) =
          Left (DistributionReleaseEmptyTrustName (distributionTrustBoundaryId boundary))
      | blank (distributionTrustRevision boundary) =
          Left (DistributionReleaseEmptyTrustRevision (distributionTrustBoundaryId boundary))
      | blank (distributionTrustBasis boundary) =
          Left (DistributionReleaseEmptyTrustBasis (distributionTrustBoundaryId boundary))
      | otherwise = Right ()

validSourceCommit :: Text -> Bool
validSourceCommit value =
  Text.length value == 40 && Text.all lowerHex value

validDigestText :: Text -> Bool
validDigestText value =
  Text.length value == 64 && Text.all lowerHex value

lowerHex :: Char -> Bool
lowerHex character =
  isDigit character || (character >= 'a' && character <= 'f')

trustKindToken :: DistributionTrustKind -> Text
trustKindToken kind = case kind of
  DistributionCompilerCheckerTrust -> "compiler-checker"
  DistributionBuildToolchainTrust -> "build-toolchain"
  DistributionLLVMToolchainTrust -> "llvm-toolchain"
  DistributionTargetAssumptionTrust -> "target-assumption"

digestToken :: Digest -> Text
digestToken (Digest value) = "sha256:" <> value

recordLine :: Text -> [(Text, Text)] -> Text
recordLine tag fields = Text.intercalate "\t"
  (tag : [key <> "=" <> escapeText value | (key, value) <- fields])

escapeText :: Text -> Text
escapeText = Text.concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '\n' = "\\n"
    escapeChar '\r' = "\\r"
    escapeChar '\t' = "\\t"
    escapeChar char = Text.singleton char

blank :: Text -> Bool
blank = Text.null . Text.strip

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (value : rest)
      | Set.member value seen = Just value
      | otherwise = go (Set.insert value seen) rest
