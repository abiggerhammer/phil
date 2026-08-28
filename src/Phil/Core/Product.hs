module Phil.Core.Product
  ( ProductError (..)
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

data ProductError
  = ProductContextError CheckError
  | ProductExpected Name Ty
  | ProductModeMismatch Name Mode Mode
  | ProductArityMismatch Int Int
  deriving (Eq, Show)

productMode :: [ProductElementType] -> Mode
productMode = foldr strongest Unrestricted . map productElementMode
  where
    strongest Linear _ = Linear
    strongest _ Linear = Linear
    strongest Affine _ = Affine
    strongest _ Affine = Affine
    strongest _ _ = Unrestricted

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
