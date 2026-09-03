module Phil.Core.DataMode
  ( ModeExpr (..)
  , ProductError (..)
  , modeLub
  , deriveRecordMode
  , deriveSumMode
  , instantiateMode
  , productMode
  , formProductBinding
  , eliminateProductBinding
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , insertBinding
  , useBinding
  )
import Phil.Core.DataModeKernelBridge
  ( certifiedAggregateFormationAccepted
  , certifiedModeLub
  , certifiedRecordMode
  , certifiedResolvedStrongest
  , certifiedSumMode
  )
import qualified Phil.Core.DataProductKernelBridge as ProductKernelBridge
import Phil.Core.Syntax
  ( Mode (..)
  , Name
  , ProductElementType (..)
  , ProductValue (..)
  , Ty (..)
  )

data ModeExpr
  = FixedMode Mode
  | ParameterMode String
  | StrongestMode [ModeExpr]
  deriving (Eq, Show)

data ProductError
  = ProductContextError CheckError
  | ProductExpected Name Ty
  | ProductModeMismatch Name Mode Mode
  | ProductArityMismatch Int Int
  | ProductFormationKernelDisagreement
  | ProductEliminationKernelDisagreement
  | ProductRestorationKernelDisagreement
  deriving (Eq, Show)

modeLub :: Mode -> Mode -> Mode
modeLub = certifiedModeLub

deriveRecordMode :: [Mode] -> Mode
deriveRecordMode = certifiedRecordMode

deriveSumMode :: [[Mode]] -> Mode
deriveSumMode = certifiedSumMode

instantiateMode :: [(String, Mode)] -> ModeExpr -> Either String Mode
instantiateMode environment expression = case expression of
  FixedMode mode -> Right mode
  ParameterMode parameter ->
    case lookup parameter environment of
      Just mode -> Right mode
      Nothing -> Left ("unknown generic mode parameter: " <> parameter)
  StrongestMode expressions -> do
    resolved <- traverse (instantiateMode environment) expressions
    case certifiedResolvedStrongest resolved of
      Just mode -> Right mode
      Nothing ->
        Left "certified data-mode kernel rejected fully resolved strongest-mode input"

productMode :: [ProductElementType] -> Mode
productMode = deriveRecordMode . map productElementMode

formProductBinding
  :: Name
  -> [Name]
  -> ResourceContext
  -> Either ProductError (ProductValue, ResourceContext)
formProductBinding productName sourceNames context = do
  (elements, afterSources) <- collectSources sourceNames context
  let restrictedSourceNames =
        [ name
        | (name, element) <- zip sourceNames elements
        , productElementMode element /= Unrestricted
        ]
      restrictedOccurrencesUnique = noDuplicates restrictedSourceNames
  if certifiedAggregateFormationAccepted restrictedOccurrencesUnique
    then Right ()
    else Left ProductFormationKernelDisagreement
  let value = ProductValue elements
      ty = TyProduct elements
      mode = productMode elements
  next <- mapLeft ProductContextError $
    insertBinding mode productName ty afterSources
  Right (value, next)

eliminateProductBinding
  :: Name
  -> [Name]
  -> ResourceContext
  -> Either ProductError ResourceContext
eliminateProductBinding productName successorNames context = do
  (actualMode, ty, afterProduct) <- mapLeft ProductContextError $
    useBinding productName context
  elements <- case ty of
    TyProduct productElements -> Right productElements
    _ -> Left (ProductExpected productName ty)
  let expectedMode = productMode elements
  if actualMode /= expectedMode
    then Left (ProductModeMismatch productName expectedMode actualMode)
    else Right ()
  let exactArity = length successorNames == length elements
      successorsDistinct = noDuplicates successorNames
      kernelDecision =
        ProductKernelBridge.classifyProductElimination
          exactArity
          successorsDistinct
  case (exactArity, successorsDistinct, kernelDecision) of
    (False, _, ProductKernelBridge.KernelProductEliminationArity) ->
      Left (ProductArityMismatch (length elements) (length successorNames))
    (True, False, ProductKernelBridge.KernelProductEliminationDuplicateSuccessor) ->
      case foldM restore afterProduct (zip successorNames elements) of
        Left nativeError -> Left nativeError
        Right _ -> Left ProductEliminationKernelDisagreement
    (True, True, ProductKernelBridge.KernelProductEliminationAccepted) -> do
      restored <- foldM restore afterProduct (zip successorNames elements)
      let ownerObligationSatisfied =
            actualMode == Unrestricted || bindingAbsent productName afterProduct
          successorsInstalledExact =
            all (successorInstalled restored) (zip successorNames elements)
      if ProductKernelBridge.productRestorationAccepted
          ownerObligationSatisfied
          successorsInstalledExact
        then Right restored
        else Left ProductRestorationKernelDisagreement
    _ -> Left ProductEliminationKernelDisagreement
  where
    restore current (name, element) =
      mapLeft ProductContextError $
        insertBinding
          (productElementMode element)
          name
          (productElementType element)
          current

collectSources
  :: [Name]
  -> ResourceContext
  -> Either ProductError ([ProductElementType], ResourceContext)
collectSources sourceNames initial = go sourceNames initial []
  where
    go [] current reversed = Right (reverse reversed, current)
    go (name : rest) current reversed = do
      (mode, ty, next) <- mapLeft ProductContextError $ useBinding name current
      go rest next (ProductElementType mode ty : reversed)

bindingAbsent :: Name -> ResourceContext -> Bool
bindingAbsent name context =
  Map.notMember name (unrestrictedBindings context)
    && Map.notMember name (affineBindings context)
    && Map.notMember name (linearBindings context)

successorInstalled
  :: ResourceContext
  -> (Name, ProductElementType)
  -> Bool
successorInstalled context (name, element) =
  case productElementMode element of
    Unrestricted ->
      Map.lookup name (unrestrictedBindings context) == Just (productElementType element)
    Affine ->
      Map.lookup name (affineBindings context) == Just (productElementType element)
    Linear ->
      Map.lookup name (linearBindings context) == Just (productElementType element)

noDuplicates :: Eq a => [a] -> Bool
noDuplicates values = case values of
  [] -> True
  value : rest -> value `notElem` rest && noDuplicates rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
