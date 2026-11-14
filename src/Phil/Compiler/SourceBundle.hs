module Phil.Compiler.SourceBundle
  ( SourceEnvironmentMap
  , SourceRootMap
  , CheckedSourceEvidenceOccurrence (..)
  , checkedSourceEvidenceOccurrences
  , CheckedSourceUnit (..)
  , CheckedSourceBundle (..)
  , SourceBundleCheckError (..)
  , checkPortableSourceBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.Check
  ( SurfaceCheckError
  , SurfaceCheckResult
  , SurfaceEnvironment
  , SourceEvidenceEvent
  , checkSurfaceComponentWithEvidence
  )
import Phil.Surface.Lineage
  ( DeclarationSiteId
  , LineageError
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , ResolvedSourceBundleLineage (..)
  , SourceUnitId
  , resolveSourceBundleLineage
  , unSourceUnitId
  )
import Phil.Surface.Parser (ParseDiagnostic, parseSurfaceFile)
import Phil.Surface.Syntax (Component, Located, SurfaceFile (..))

-- | Explicit source-checking environments indexed by persisted declaration
-- identity.  Carrier names, paths, component display names, and selected-root
-- spellings are not accepted as environment lookup keys.
type SourceEnvironmentMap = Map DeclarationKey SurfaceEnvironment

-- | Explicit selected-root binding supplied by the architecture/source-bundle
-- integration layer.  The generic compiler consumes this relation; it does not
-- recognize witness names or infer roots from source presentation.
type SourceRootMap = Map Text DeclarationKey

-- | Public observational data, NOT a credential. Only the private raw-source
-- rechecking VerifiedSourceSystemsProduction can seal these occurrences.
-- Unit and persisted declaration site remain separate from editable spans,
-- names, and the selected Architecture instance key.
data CheckedSourceEvidenceOccurrence = CheckedSourceEvidenceOccurrence
  { checkedEvidenceUnitId :: SourceUnitId
  , checkedEvidenceDeclarationSite :: DeclarationSiteId
  , checkedEvidenceDeclarationKey :: DeclarationKey
  , checkedEvidenceEvent :: SourceEvidenceEvent
  }
  deriving (Eq, Show)

-- | One ordinary source unit after exact lineage resolution, parsing, and the
-- ordinary surface checker have all accepted it.
data CheckedSourceUnit = CheckedSourceUnit
  { checkedSourceUnitId :: SourceUnitId
  , checkedSourceDeclarationSite :: DeclarationSiteId
  , checkedSourceDeclarationKey :: DeclarationKey
  , checkedSourceComponent :: Located Component
  , checkedSourceResult :: SurfaceCheckResult
  , checkedSourceEvidenceEvents :: [SourceEvidenceEvent]
  }
  deriving (Eq, Show)

-- | Witness-neutral checked front-end product.  Later INT-001 slices consume
-- this value when binding ordinary source to checked Architecture/Core and the
-- already-Certified generic Core-to-Systems path.
data CheckedSourceBundle = CheckedSourceBundle
  { checkedSourceSelectedRoot :: Text
  , checkedSourceSelectedRootKey :: DeclarationKey
  , checkedSourceLineage :: ResolvedSourceBundleLineage
  , checkedSourceUnits :: [CheckedSourceUnit]
  }
  deriving (Eq, Show)

-- | Public projection for diagnostics and tests. Constructing or modifying a
-- CheckedSourceBundle does NOT mint a source-owned P9 acceptance.
checkedSourceEvidenceOccurrences
  :: CheckedSourceBundle -> [CheckedSourceEvidenceOccurrence]
checkedSourceEvidenceOccurrences bundle =
  [ CheckedSourceEvidenceOccurrence
      { checkedEvidenceUnitId = checkedSourceUnitId unit
      , checkedEvidenceDeclarationSite = checkedSourceDeclarationSite unit
      , checkedEvidenceDeclarationKey = checkedSourceDeclarationKey unit
      , checkedEvidenceEvent = event
      }
  | unit <- checkedSourceUnits bundle
  , event <- checkedSourceEvidenceEvents unit
  ]

data SourceBundleCheckError
  = SourceBundleLineageError LineageError
  | SourceBundleUnknownSelectedRoot Text
  | SourceBundleSelectedRootNotInBundle Text DeclarationKey
  | SourceBundleResolvedDeclarationMissing DeclarationSiteId
  | SourceBundleEnvironmentMissing DeclarationKey
  | SourceBundleParseError SourceUnitId ParseDiagnostic
  | SourceBundleDeclarationCountMismatch SourceUnitId Int
  | SourceBundleSurfaceCheckError SourceUnitId DeclarationKey SurfaceCheckError
  deriving (Eq, Show)

-- | Resolve and check one portable ordinary-source bundle without consulting
-- witness identity.  Every semantic lookup is anchored either in persisted
-- lineage or in an explicit root/environment map supplied by the caller.
checkPortableSourceBundle
  :: SourceRootMap
  -> SourceEnvironmentMap
  -> PortableSourceBundle
  -> Either SourceBundleCheckError CheckedSourceBundle
checkPortableSourceBundle roots environments bundle = do
  lineage <- mapLeft SourceBundleLineageError (resolveSourceBundleLineage bundle)
  let selectedRoot = portableSelectedProgramRoot bundle
  rootKey <- maybe
    (Left (SourceBundleUnknownSelectedRoot selectedRoot))
    Right
    (Map.lookup selectedRoot roots)
  if Set.member rootKey (Set.fromList (Map.elems (resolvedDeclarationKeys lineage)))
    then Right ()
    else Left (SourceBundleSelectedRootNotInBundle selectedRoot rootKey)
  units <- mapM (checkUnit lineage) (portableSourceUnits bundle)
  Right CheckedSourceBundle
    { checkedSourceSelectedRoot = selectedRoot
    , checkedSourceSelectedRootKey = rootKey
    , checkedSourceLineage = lineage
    , checkedSourceUnits = units
    }
  where
    checkUnit lineage unit = do
      let siteId = portableDeclarationSiteId unit
          unitId = portableSourceUnitId unit
      declarationKey <- maybe
        (Left (SourceBundleResolvedDeclarationMissing siteId))
        Right
        (Map.lookup siteId (resolvedDeclarationKeys lineage))
      environment <- maybe
        (Left (SourceBundleEnvironmentMissing declarationKey))
        Right
        (Map.lookup declarationKey environments)
      surfaceFile <- mapLeft (SourceBundleParseError unitId) $
        parseSurfaceFile (unSourceUnitId unitId) (portableSourceText unit)
      component <- exactlyOneComponent unitId surfaceFile
      (checked, events) <- mapLeft (SourceBundleSurfaceCheckError unitId declarationKey) $
        checkSurfaceComponentWithEvidence environment component
      Right CheckedSourceUnit
        { checkedSourceUnitId = unitId
        , checkedSourceDeclarationSite = siteId
        , checkedSourceDeclarationKey = declarationKey
        , checkedSourceComponent = component
        , checkedSourceResult = checked
        , checkedSourceEvidenceEvents = events
        }

exactlyOneComponent
  :: SourceUnitId
  -> SurfaceFile
  -> Either SourceBundleCheckError (Located Component)
exactlyOneComponent _unitId (SurfaceFile [component]) = Right component
exactlyOneComponent unitId (SurfaceFile components) =
  Left (SourceBundleDeclarationCountMismatch unitId (length components))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
