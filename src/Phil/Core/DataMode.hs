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
import Phil.Core.Context
  ( CheckError
  , ResourceContext
  , insertBinding
  , useBinding
  )
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
  deriving (Eq, Show)

modeLub :: Mode -> Mode -> Mode
modeLub left right = case (left, right) of
  (Linear, _) -> Linear
  (_, Linear) -> Linear
  (Affine, _) -> Affine
  (_, Affine) -> Affine
  _ -> Unrestricted

deriveRecordMode :: [Mode] -> Mode
deriveRecordMode = foldr modeLub Unrestricted

deriveSumMode :: [[Mode]] -> Mode
deriveSumMode = foldr (modeLub . deriveRecordMode) Unrestricted

instantiateMode :: [(String, Mode)] -> ModeExpr -> Either String Mode
instantiateMode environment expression = case expression of
  FixedMode mode -> Right mode
  ParameterMode parameter ->
    case lookup parameter environment of
      Just mode -> Right mode
      Nothing -> Left ("unknown generic mode parameter: " <> parameter)
  StrongestMode expressions ->
    foldr modeLub Unrestricted <$> traverse (instantiateMode environment) expressions

productMode :: [ProductElementType] -> Mode
productMode = deriveRecordMode . map productElementMode

formProductBinding
  :: Name
  -> [Name]
  -> ResourceContext
  -> Either ProductError (ProductValue, ResourceContext)
formProductBinding productName sourceNames context = do
  (elements, afterSources) <- collectSources sourceNames context
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
  if length successorNames /= length elements
    then Left (ProductArityMismatch (length elements) (length successorNames))
    else foldM restore afterProduct (zip successorNames elements)
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
