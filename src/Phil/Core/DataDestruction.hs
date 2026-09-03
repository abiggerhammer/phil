module Phil.Core.DataDestruction
  ( OwnedField (..)
  , FieldDisposition (..)
  , AggregateDisposition (..)
  , DataDestructionError (..)
  , checkFieldDispositions
  , checkAggregateDisposition
  , consumeAggregateFields
  ) where

import Control.Monad (foldM, unless)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , insertBinding
  , useBinding
  )
import qualified Phil.Core.DataEliminationKernelBridge as KernelBridge
import Phil.Core.Syntax (Mode (..), Name, Ty)

data OwnedField = OwnedField
  { ownedFieldName :: Name
  , ownedFieldMode :: Mode
  , ownedFieldType :: Ty
  }
  deriving (Eq, Show)

data FieldDisposition
  = FieldBound
  | FieldOmitted
  deriving (Eq, Show)

data AggregateDisposition
  = WholeAggregateConsumed
  | ExplicitTypedRemainder Ty
  | ImplicitPartialRemainder
  deriving (Eq, Show)

data DataDestructionError
  = DuplicateFieldDisposition Name
  | UnknownFieldDisposition Name
  | MissingLinearFieldDisposition Name
  | DataDestructionContextError CheckError
  | AggregateEliminationRequiresRestrictedOwner Name
  | ImplicitPartialRemainderRejected
  | CertifiedDataEliminationKernelDisagreement
  deriving (Eq, Show)

checkFieldDispositions
  :: [OwnedField]
  -> [(Name, FieldDisposition)]
  -> Either DataDestructionError ()
checkFieldDispositions fields dispositions = do
  dispositionMap <- buildDispositionMap dispositions
  mapM_ (checkField dispositionMap) fields
  mapM_ (checkKnownField fields) (Map.keys dispositionMap)
  unless (KernelBridge.eliminationPlanAccepted True True) $
    Left CertifiedDataEliminationKernelDisagreement

checkAggregateDisposition
  :: AggregateDisposition
  -> Either DataDestructionError ()
checkAggregateDisposition disposition =
  let kernelAccepted = KernelBridge.aggregateDispositionAccepted $
        case disposition of
          WholeAggregateConsumed -> KernelBridge.KernelWholeAggregate
          ExplicitTypedRemainder _ -> KernelBridge.KernelExplicitTypedRemainder
          ImplicitPartialRemainder -> KernelBridge.KernelImplicitPartialRemainder
  in case disposition of
    ImplicitPartialRemainder
      | kernelAccepted -> Left CertifiedDataEliminationKernelDisagreement
      | otherwise -> Left ImplicitPartialRemainderRejected
    _
      | kernelAccepted -> Right ()
      | otherwise -> Left CertifiedDataEliminationKernelDisagreement

consumeAggregateFields
  :: Name
  -> [OwnedField]
  -> [(Name, FieldDisposition)]
  -> ResourceContext
  -> Either DataDestructionError ResourceContext
consumeAggregateFields aggregateName fields dispositions context = do
  checkFieldDispositions fields dispositions
  checkAggregateDisposition WholeAggregateConsumed
  dispositionMap <- buildDispositionMap dispositions
  (aggregateMode, _, afterAggregate) <-
    mapLeft DataDestructionContextError $ useBinding aggregateName context
  case aggregateMode of
    Unrestricted -> Left (AggregateEliminationRequiresRestrictedOwner aggregateName)
    Affine -> Right ()
    Linear -> Right ()
  afterSuccessors <- foldM (restoreField dispositionMap) afterAggregate fields
  let aggregateConsumed = bindingAbsent aggregateName afterAggregate
      boundFields = filter (isBound dispositionMap) fields
      successorsExact = all (fieldInstalled afterSuccessors) boundFields
      successorNames = map ownedFieldName boundFields
      successorsDistinct = length successorNames == length (nub successorNames)
  unless
    ( KernelBridge.consumingEliminationAccepted
        aggregateConsumed
        successorsExact
        successorsDistinct
    ) $
    Left CertifiedDataEliminationKernelDisagreement
  Right afterSuccessors

buildDispositionMap
  :: [(Name, FieldDisposition)]
  -> Either DataDestructionError (Map Name FieldDisposition)
buildDispositionMap = foldl insertOne (Right Map.empty)
  where
    insertOne accumulated (name, disposition) = do
      current <- accumulated
      if Map.member name current
        then Left (DuplicateFieldDisposition name)
        else Right (Map.insert name disposition current)

checkField
  :: Map Name FieldDisposition
  -> OwnedField
  -> Either DataDestructionError ()
checkField dispositions field =
  let disposition = Map.lookup (ownedFieldName field) dispositions
      nativeAllowed = fieldDispositionAllowed (ownedFieldMode field) disposition
      kernelAllowed = KernelBridge.fieldDispositionAccepted
        (ownedFieldMode field)
        (fmap toKernelFieldDisposition disposition)
  in if nativeAllowed /= kernelAllowed
      then Left CertifiedDataEliminationKernelDisagreement
      else if nativeAllowed
        then Right ()
        else Left (MissingLinearFieldDisposition (ownedFieldName field))

fieldDispositionAllowed :: Mode -> Maybe FieldDisposition -> Bool
fieldDispositionAllowed mode disposition = case mode of
  Linear -> disposition == Just FieldBound
  Affine -> True
  Unrestricted -> True

checkKnownField
  :: [OwnedField]
  -> Name
  -> Either DataDestructionError ()
checkKnownField fields name
  | any ((== name) . ownedFieldName) fields = Right ()
  | otherwise = Left (UnknownFieldDisposition name)

restoreField
  :: Map Name FieldDisposition
  -> ResourceContext
  -> OwnedField
  -> Either DataDestructionError ResourceContext
restoreField dispositions context field =
  case Map.lookup (ownedFieldName field) dispositions of
    Just FieldBound -> mapLeft DataDestructionContextError $
      insertBinding
        (ownedFieldMode field)
        (ownedFieldName field)
        (ownedFieldType field)
        context
    Just FieldOmitted -> Right context
    Nothing -> Right context

isBound :: Map Name FieldDisposition -> OwnedField -> Bool
isBound dispositions field =
  Map.lookup (ownedFieldName field) dispositions == Just FieldBound

fieldInstalled :: ResourceContext -> OwnedField -> Bool
fieldInstalled context field =
  let name = ownedFieldName field
      ty = ownedFieldType field
  in case ownedFieldMode field of
    Unrestricted -> Map.lookup name (unrestrictedBindings context) == Just ty
    Affine -> Map.lookup name (affineBindings context) == Just ty
    Linear -> Map.lookup name (linearBindings context) == Just ty

bindingAbsent :: Name -> ResourceContext -> Bool
bindingAbsent name context =
  Map.notMember name (unrestrictedBindings context)
    && Map.notMember name (affineBindings context)
    && Map.notMember name (linearBindings context)

toKernelFieldDisposition
  :: FieldDisposition
  -> KernelBridge.KernelFieldDisposition
toKernelFieldDisposition disposition = case disposition of
  FieldBound -> KernelBridge.KernelFieldBound
  FieldOmitted -> KernelBridge.KernelFieldOmitted

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
