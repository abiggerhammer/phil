module Phil.Core.DataSum
  ( SumConstructor (..)
  , DataSumError (..)
  , selectSumConstructorPayload
  , consumeSelectedSumPayload
  , checkContinuingSumArm
  , joinSumContinuing
  , joinPackagedSumContinuing
  ) where

import Control.Monad (unless)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , ensureComplete
  , joinContinuing
  )
import Phil.Core.DataDestruction
  ( DataDestructionError
  , FieldDisposition (..)
  , OwnedField (..)
  , checkOwnedFieldSchema
  , consumeAggregateFields
  )
import qualified Phil.Core.DataSumKernelBridge as KernelBridge
import Phil.Core.Syntax (Mode (..), Name, Ty)

data SumConstructor = SumConstructor
  { sumConstructorTag :: Int
  , sumConstructorPayload :: [OwnedField]
  }
  deriving (Eq, Show)

data DataSumError
  = DuplicateSumConstructorTag Int
  | UnknownSumConstructor Int
  | DataSumDestructionError DataDestructionError
  | DataSumContextError CheckError
  | MissingExplicitSumPackage Name Ty
  | CertifiedDataSumKernelDisagreement
  deriving (Eq, Show)

selectSumConstructorPayload
  :: Int
  -> [SumConstructor]
  -> Either DataSumError [OwnedField]
selectSumConstructorPayload tag constructors = do
  -- Constructor tags are the supplied Phase-1 consumer schema. Make them
  -- unambiguous before the existing lookup can select a first matching entry.
  checkConstructorTags constructors
  let selected = find ((== tag) . sumConstructorTag) constructors
      nativeDeclared = maybe False (const True) selected
      kernelAccepted = KernelBridge.constructorSelectionAccepted nativeDeclared
  if nativeDeclared /= kernelAccepted
    then Left CertifiedDataSumKernelDisagreement
    else case selected of
      Nothing -> Left (UnknownSumConstructor tag)
      Just constructor -> do
        let payload = sumConstructorPayload constructor
        mapLeft DataSumDestructionError (checkOwnedFieldSchema payload)
        Right payload

consumeSelectedSumPayload
  :: Name
  -> Int
  -> [SumConstructor]
  -> ResourceContext
  -> Either DataSumError ResourceContext
consumeSelectedSumPayload aggregateName tag constructors context = do
  payload <- selectSumConstructorPayload tag constructors
  let dispositions = map (\field -> (ownedFieldName field, FieldBound)) payload
  next <- mapLeft DataSumDestructionError $
    consumeAggregateFields aggregateName payload dispositions context
  unless (KernelBridge.selectedPayloadRestorationAccepted True True) $
    Left CertifiedDataSumKernelDisagreement
  Right next

checkContinuingSumArm
  :: [OwnedField]
  -> ResourceContext
  -> Either DataSumError ()
checkContinuingSumArm selectedPayload context = do
  mapLeft DataSumContextError (ensureComplete context)
  let selectedPayloadAccounted = all (linearFieldAccounted context) selectedPayload
  unless (KernelBridge.continuingArmAccepted selectedPayloadAccounted) $
    Left CertifiedDataSumKernelDisagreement

joinSumContinuing
  :: [ResourceContext]
  -> Either DataSumError ResourceContext
joinSumContinuing = joinSumContinuingByFacts False

joinPackagedSumContinuing
  :: Name
  -> Ty
  -> [ResourceContext]
  -> Either DataSumError ResourceContext
joinPackagedSumContinuing packageName packageTy contexts = do
  unless (explicitPackagePresent packageName packageTy contexts) $
    Left (MissingExplicitSumPackage packageName packageTy)
  joinSumContinuingByFacts True contexts

checkConstructorTags :: [SumConstructor] -> Either DataSumError ()
checkConstructorTags = go Map.empty
  where
    go _ [] = Right ()
    go seen (constructor : rest)
      | Map.member tag seen = Left (DuplicateSumConstructorTag tag)
      | otherwise = go (Map.insert tag () seen) rest
      where
        tag = sumConstructorTag constructor

joinSumContinuingByFacts
  :: Bool
  -> [ResourceContext]
  -> Either DataSumError ResourceContext
joinSumContinuingByFacts explicitCommonPackage contexts =
  let rawLinearShapesCompatible = linearShapesCompatible contexts
      nativeJoin = joinContinuing contexts
      ordinaryJoinAccepted = either (const False) (const True) nativeJoin
      kernelAccepted = KernelBridge.branchConvergenceAccepted
        rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted
  in case nativeJoin of
    Left err
      | kernelAccepted -> Left CertifiedDataSumKernelDisagreement
      | otherwise -> Left (DataSumContextError err)
    Right joined
      | kernelAccepted -> Right joined
      | otherwise -> Left CertifiedDataSumKernelDisagreement

linearFieldAccounted :: ResourceContext -> OwnedField -> Bool
linearFieldAccounted context field =
  case ownedFieldMode field of
    Linear -> Map.notMember (ownedFieldName field) (linearBindings context)
    Affine -> True
    Unrestricted -> True

linearShapesCompatible :: [ResourceContext] -> Bool
linearShapesCompatible [] = True
linearShapesCompatible (first : rest) =
  all ((== linearBindings first) . linearBindings) rest

explicitPackagePresent :: Name -> Ty -> [ResourceContext] -> Bool
explicitPackagePresent _ _ [] = False
explicitPackagePresent packageName packageTy contexts =
  all
    ((== Just packageTy) . Map.lookup packageName . linearBindings)
    contexts

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
