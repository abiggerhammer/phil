module Phil.Surface.GrammarV1.GenericDischarge
  ( GrammarV1ResolvedGenericRequirementSet (..)
  , GrammarV1ResolvedRequirementDisposition (..)
  , GrammarV1CheckedGenericRequirement (..)
  , GrammarV1CheckedSpecializedGenericDischarge (..)
  , GrammarV1GenericDischargeError (..)
  , grammarV1CheckedStrictSpecializedGenericDischarge
  ) where

import qualified Data.Set as Set
import Phil.Core.Focusing (FocusStep)
import Phil.Core.Generic
  ( GenericApplicationIdentity (..)
  , GenericDischargeLineage
  , GenericInstantiationError
  , GenericInstantiationRecord
  , GenericRequirement
  , GenericRequirementDisposition
  , checkGenericInstantiation
  , deriveGenericDischargeLineage
  , strictGenericInstantiationPolicy
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , InterfaceRevision
  , StaticContext
  )
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.GenericRequirementCore
  ( GrammarV1GenericRequirementCoreError
  , GrammarV1ResolvedProviderRequirement
  , GrammarV1ResolvedStructuralRequirement
  , grammarV1CheckedCoreGenericRequirement
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1GenericRequirement)
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1CheckedSpecializedStaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact declaration-side requirement set for one already-resolved generic
-- target. Stable identity is supplied by the declaration-resolution layer; this
-- bridge does not derive it from the declaration's display spelling.
data GrammarV1ResolvedGenericRequirementSet = GrammarV1ResolvedGenericRequirementSet
  { resolvedGenericRequirementSetDeclarationKey :: DeclarationKey
  , resolvedGenericRequirementSetInterfaceRevision :: InterfaceRevision
  , resolvedGenericRequirementSetSourceRequirements
      :: [Located GrammarV1GenericRequirement]
  }
  deriving (Eq, Show)

-- | One disposition supplied by the competent semantic layer for one exact
-- located source requirement. Repeating the located source occurrence prevents
-- positional evidence from drifting onto another requirement with similar text.
data GrammarV1ResolvedRequirementDisposition = GrammarV1ResolvedRequirementDisposition
  { resolvedRequirementDispositionSource
      :: Located GrammarV1GenericRequirement
  , resolvedRequirementDispositionValue :: GenericRequirementDisposition
  }
  deriving (Eq, Show)

-- | Exact source/Core correspondence retained after requirement checking.
data GrammarV1CheckedGenericRequirement = GrammarV1CheckedGenericRequirement
  { checkedGenericRequirementSource :: Located GrammarV1GenericRequirement
  , checkedGenericRequirementCore :: GenericRequirement
  , checkedGenericRequirementFocusSteps :: [FocusStep]
  }
  deriving (Eq, Show)

-- | Strict generic discharge for one already-checked specialized source
-- reference. The Core instantiation record and discharge lineage are retained
-- separately so callers cannot confuse successful requirement checking with a
-- new application identity or implementation choice.
data GrammarV1CheckedSpecializedGenericDischarge =
  GrammarV1CheckedSpecializedGenericDischarge
    { checkedGenericDischargeApplication
        :: GrammarV1CheckedSpecializedStaticReference
    , checkedGenericDischargeRequirements :: [GrammarV1CheckedGenericRequirement]
    , checkedGenericDischargeInstantiation :: GenericInstantiationRecord
    , checkedGenericDischargeLineage :: GenericDischargeLineage
    }
  deriving (Eq, Show)

data GrammarV1GenericDischargeError
  = GrammarV1GenericRequirementTargetMismatch
      DeclarationKey
      InterfaceRevision
      DeclarationKey
      InterfaceRevision
  | GrammarV1GenericDischargeRequirementError GrammarV1GenericRequirementCoreError
  | GrammarV1MissingRequirementDisposition (Located GrammarV1GenericRequirement)
  | GrammarV1DuplicateRequirementDisposition (Located GrammarV1GenericRequirement)
  | GrammarV1UnexpectedRequirementDisposition (Located GrammarV1GenericRequirement)
  | GrammarV1GenericInstantiationError GenericInstantiationError
  deriving (Eq, Show)

-- | Compose the exact checked application identity from the specialized-static
-- reference bridge with the exact Core-backed requirement subset and Core's
-- strict generic-instantiation/discharge authority.
--
-- The requirement set must carry the same stable DeclarationKey and
-- InterfaceRevision as the checked application. Each located source requirement
-- must have exactly one supplied semantic disposition, and no disposition may
-- name a source occurrence outside the resolved declaration-side requirement
-- set. Requirement checking is delegated to 'grammarV1CheckedCoreGenericRequirement';
-- acceptance of the complete disposition domain and each disposition's semantic
-- validity is delegated exactly once to 'checkGenericInstantiation'. Finally,
-- 'deriveGenericDischargeLineage' records the already-checked application,
-- caller-supplied DefinitionRevision, and accepted instantiation record.
--
-- Strict policy is intentional: this bridge cannot manufacture or silently
-- admit assumption/export dispositions. Those require their own competent
-- source/assurance route. Likewise this function does not establish binder scope
-- (SURF-009), resolve providers, choose implementations, or infer any disposition.
grammarV1CheckedStrictSpecializedGenericDischarge
  :: StaticContext
  -> SurfaceState
  -> [GrammarV1ResolvedStructuralRequirement]
  -> [GrammarV1ResolvedProviderRequirement]
  -> DefinitionRevision
  -> GrammarV1CheckedSpecializedStaticReference
  -> GrammarV1ResolvedGenericRequirementSet
  -> [GrammarV1ResolvedRequirementDisposition]
  -> Maybe
      (Either
        GrammarV1GenericDischargeError
        GrammarV1CheckedSpecializedGenericDischarge)
grammarV1CheckedStrictSpecializedGenericDischarge
    staticContext
    state
    structuralResolutions
    providerResolutions
    definitionRevision
    application
    requirementSet
    dispositions =
  if targetDeclaration /= applicationDeclaration
      || targetInterface /= applicationInterface
    then Just (Left
      (GrammarV1GenericRequirementTargetMismatch
        applicationDeclaration
        applicationInterface
        targetDeclaration
        targetInterface))
    else do
      checkedResult <- checkRequirements sourceRequirements
      pure $ do
        checked <- checkedResult
        ensureNoUnexpected sourceRequirements dispositions
        dispositionPairs <- mapM dispositionFor checked
        instantiation <- mapLeft GrammarV1GenericInstantiationError
          (checkGenericInstantiation
            strictGenericInstantiationPolicy
            (Set.fromList (map checkedGenericRequirementCore checked))
            dispositionPairs)
        let lineage = deriveGenericDischargeLineage
              applicationIdentity
              definitionRevision
              instantiation
        Right GrammarV1CheckedSpecializedGenericDischarge
          { checkedGenericDischargeApplication = application
          , checkedGenericDischargeRequirements = checked
          , checkedGenericDischargeInstantiation = instantiation
          , checkedGenericDischargeLineage = lineage
          }
  where
    applicationIdentity = checkedSpecializedStaticApplicationIdentity application
    applicationDeclaration = genericApplicationDeclarationKey applicationIdentity
    applicationInterface = genericApplicationInterfaceRevision applicationIdentity
    targetDeclaration = resolvedGenericRequirementSetDeclarationKey requirementSet
    targetInterface = resolvedGenericRequirementSetInterfaceRevision requirementSet
    sourceRequirements = resolvedGenericRequirementSetSourceRequirements requirementSet

    checkRequirements [] = Just (Right [])
    checkRequirements (source : rest) = do
      current <- grammarV1CheckedCoreGenericRequirement
        staticContext
        state
        structuralResolutions
        providerResolutions
        (locatedValue source)
      remaining <- checkRequirements rest
      pure $ do
        (coreRequirement, focusSteps) <-
          mapLeft GrammarV1GenericDischargeRequirementError current
        tailChecked <- remaining
        Right
          ( GrammarV1CheckedGenericRequirement
              { checkedGenericRequirementSource = source
              , checkedGenericRequirementCore = coreRequirement
              , checkedGenericRequirementFocusSteps = focusSteps
              }
          : tailChecked
          )

    dispositionFor checked =
      case
        [ resolvedRequirementDispositionValue disposition
        | disposition <- dispositions
        , resolvedRequirementDispositionSource disposition
            == checkedGenericRequirementSource checked
        ] of
          [] -> Left
            (GrammarV1MissingRequirementDisposition
              (checkedGenericRequirementSource checked))
          [disposition] -> Right
            (checkedGenericRequirementCore checked, disposition)
          _ -> Left
            (GrammarV1DuplicateRequirementDisposition
              (checkedGenericRequirementSource checked))

ensureNoUnexpected
  :: [Located GrammarV1GenericRequirement]
  -> [GrammarV1ResolvedRequirementDisposition]
  -> Either GrammarV1GenericDischargeError ()
ensureNoUnexpected sourceRequirements dispositions =
  case
    [ resolvedRequirementDispositionSource disposition
    | disposition <- dispositions
    , resolvedRequirementDispositionSource disposition
        `notElem` sourceRequirements
    ] of
      [] -> Right ()
      source : _ -> Left (GrammarV1UnexpectedRequirementDisposition source)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
