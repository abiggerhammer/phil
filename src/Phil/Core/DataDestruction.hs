{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.DataDestruction
  ( OwnedField (..)
  , FieldDisposition (..)
  , AggregateDisposition (..)
  , DataDestructionError (..)
  , checkOwnedFieldSchema
  , checkFieldDispositions
  , checkAggregateDisposition
  , nominalRecordIdentity
  , consumeNominalRecordFields
  , consumeAggregateFields
  ) where

import Control.Monad (foldM, unless)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , insertBinding
  , useBinding
  )
import qualified Phil.Core.DataEliminationKernelBridge as KernelBridge
import Phil.Core.Static
  ( DeclarationDescriptor (..), DeclarationIdentity (..), DeclarationKey
  , DeclarationPresentation (..), SemanticForm (..), deriveDeclarationIdentity
  )
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))

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
  = DuplicateOwnedField Name
  | DuplicateFieldDisposition Name
  | UnknownFieldDisposition Name
  | MissingLinearFieldDisposition Name
  | DataDestructionContextError CheckError
  | AggregateEliminationRequiresRestrictedOwner Name
  | NominalRecordSchemaUnsupported
  | NominalRecordOwnerMismatch Name
  | NominalRecordRequiresTypedElimination Name
  | ImplicitPartialRemainderRejected
  | CertifiedDataEliminationKernelDisagreement
  deriving (Eq, Show)

-- | Aggregate elimination receives an explicitly supplied Phase-1 field schema.
-- It does not infer nominal declaration identity from names or modes, so that
-- association remains a caller premise. Once a schema reaches this consumer,
-- however, field identity must be unambiguous before a name-based disposition
-- map can discard source multiplicity.
checkOwnedFieldSchema
  :: [OwnedField]
  -> Either DataDestructionError ()
checkOwnedFieldSchema = go Map.empty
  where
    go _ [] = Right ()
    go seen (field : rest)
      | Map.member name seen = Left (DuplicateOwnedField name)
      | otherwise = go (Map.insert name () seen) rest
      where
        name = ownedFieldName field

checkFieldDispositions
  :: [OwnedField]
  -> [(Name, FieldDisposition)]
  -> Either DataDestructionError ()
checkFieldDispositions fields dispositions = do
  checkOwnedFieldSchema fields
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
consumeAggregateFields = consumeFields rejectNominal
  where
    rejectNominal name _ ty = case ty of
      TyRecordNominal _ _ -> Left (NominalRecordRequiresTypedElimination name)
      TyRefined _ base _ -> rejectNominal name Unrestricted base
      _ -> Right ()

-- | Derive the interface from the ordered public schema. This checks the
-- bounded representation, while origin of the schema and key is a caller
-- premise at Core level.
nominalRecordIdentity
  :: DeclarationKey -> [OwnedField] -> Either DataDestructionError DeclarationIdentity
nominalRecordIdentity key fields = do
  checkOwnedFieldSchema fields
  unless (length (filter ((== Linear) . ownedFieldMode) fields) == 1) $
    Left NominalRecordSchemaUnsupported
  semantics <- mapM fieldSemantics fields
  let interface = SemanticOrdered
        [SemanticAtom "closed-record-v1", SemanticAtom "Linear", SemanticOrdered semantics]
  Right $ deriveDeclarationIdentity $
    DeclarationDescriptor (DeclarationPresentation "" []) key interface interface
  where
    fieldSemantics (OwnedField (Name label) mode ty) = do
      typeForm <- case (mode, ty) of
        (Unrestricted, TyUnit) -> Right [SemanticAtom "Unit"]
        (Unrestricted, TyBool) -> Right [SemanticAtom "Bool"]
        (Unrestricted, TyUInt n) | n > 0 -> Right [SemanticAtom "U", number n]
        (Linear, TyBytes (RefNat n)) | n >= 0 -> Right [SemanticAtom "Bytes", number n]
        _ -> Left NominalRecordSchemaUnsupported
      Right $ SemanticOrdered
        [SemanticAtom label, SemanticAtom (Text.pack (show mode)), SemanticOrdered typeForm]
    number :: Show a => a -> SemanticForm
    number = SemanticAtom . Text.pack . show

-- | Bind each original field to at most one fresh destination. The actual
-- aggregate has to match the independently recomputed interface before
-- the native transition can commit successor bindings.
consumeNominalRecordFields
  :: DeclarationKey
  -> Name
  -> [(OwnedField, Maybe Name)]
  -> ResourceContext
  -> Either DataDestructionError ResourceContext
consumeNominalRecordFields key owner plan context = do
  identity <- nominalRecordIdentity key (map fst plan)
  checkFieldDispositions (map fst plan)
    [(ownedFieldName field, FieldBound) | (field, Just _) <- plan]
  let expected = TyRecordNominal key (identityInterfaceRevision identity)
      checkOwner name mode actual =
        unless (mode == Linear && actual == expected) $
          Left (NominalRecordOwnerMismatch name)
      destinations =
        [field { ownedFieldName = destination } | (field, Just destination) <- plan]
  unless (all ((/= owner) . ownedFieldName) destinations) $
    Left (NominalRecordOwnerMismatch owner)
  consumeFields checkOwner owner destinations
    [(ownedFieldName field, FieldBound) | field <- destinations] context

consumeFields
  :: (Name -> Mode -> Ty -> Either DataDestructionError ())
  -> Name
  -> [OwnedField]
  -> [(Name, FieldDisposition)]
  -> ResourceContext
  -> Either DataDestructionError ResourceContext
consumeFields checkOwner aggregateName fields dispositions context = do
  checkFieldDispositions fields dispositions
  checkAggregateDisposition WholeAggregateConsumed
  dispositionMap <- buildDispositionMap dispositions
  (aggregateMode, aggregateType, afterAggregate) <-
    mapLeft DataDestructionContextError $ useBinding aggregateName context
  checkOwner aggregateName aggregateMode aggregateType
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
