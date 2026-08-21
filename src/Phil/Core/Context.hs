module Phil.Core.Context
  ( ResourceContext (..)
  , CheckError (..)
  , emptyContext
  , insertBinding
  , useUnrestricted
  , consumeAffine
  , consumeLinear
  , startSharedLoan
  , endSharedLoan
  , ensureComplete
  , joinContinuing
  ) where

import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Phil.Core.Syntax (Mode (..), Name, Ty)

data ResourceContext = ResourceContext
  { unrestrictedBindings :: Map Name Ty
  , affineBindings :: Map Name Ty
  , linearBindings :: Map Name Ty
  , sharedLoans :: Set Name
  }
  deriving (Eq, Show)

data CheckError
  = DuplicateBinding Name
  | UnknownBinding Name
  | WrongStructuralMode Name Mode Mode
  | OwnerBorrowed Name
  | LoanAlreadyActive Name
  | LoanNotActive Name
  | EscapingLoans (Set Name)
  | UnconsumedLinearResources (Map Name Ty)
  | UnrestrictedBranchMismatch (Map Name Ty) (Map Name Ty)
  | LinearBranchMismatch (Map Name Ty) (Map Name Ty)
  | AffineBranchTypeMismatch Name Ty Ty
  deriving (Eq, Show)

emptyContext :: ResourceContext
emptyContext = ResourceContext Map.empty Map.empty Map.empty Set.empty

insertBinding :: Mode -> Name -> Ty -> ResourceContext -> Either CheckError ResourceContext
insertBinding mode name ty context
  | bindingExists name context = Left (DuplicateBinding name)
  | otherwise = Right $ case mode of
      Unrestricted -> context { unrestrictedBindings = Map.insert name ty (unrestrictedBindings context) }
      Affine -> context { affineBindings = Map.insert name ty (affineBindings context) }
      Linear -> context { linearBindings = Map.insert name ty (linearBindings context) }

useUnrestricted :: Name -> ResourceContext -> Either CheckError (Ty, ResourceContext)
useUnrestricted name context =
  case Map.lookup name (unrestrictedBindings context) of
    Just ty -> Right (ty, context)
    Nothing -> case actualMode name context of
      Just mode -> Left (WrongStructuralMode name Unrestricted mode)
      Nothing -> Left (UnknownBinding name)

consumeAffine :: Name -> ResourceContext -> Either CheckError (Ty, ResourceContext)
consumeAffine name context
  | Set.member name (sharedLoans context) = Left (OwnerBorrowed name)
  | otherwise =
      case Map.lookup name (affineBindings context) of
        Just ty -> Right (ty, context { affineBindings = Map.delete name (affineBindings context) })
        Nothing -> case actualMode name context of
          Just mode -> Left (WrongStructuralMode name Affine mode)
          Nothing -> Left (UnknownBinding name)

consumeLinear :: Name -> ResourceContext -> Either CheckError (Ty, ResourceContext)
consumeLinear name context
  | Set.member name (sharedLoans context) = Left (OwnerBorrowed name)
  | otherwise =
      case Map.lookup name (linearBindings context) of
        Just ty -> Right (ty, context { linearBindings = Map.delete name (linearBindings context) })
        Nothing -> case actualMode name context of
          Just mode -> Left (WrongStructuralMode name Linear mode)
          Nothing -> Left (UnknownBinding name)

startSharedLoan :: Name -> ResourceContext -> Either CheckError ResourceContext
startSharedLoan name context
  | Set.member name (sharedLoans context) = Left (LoanAlreadyActive name)
  | Map.member name (affineBindings context) || Map.member name (linearBindings context) =
      Right (context { sharedLoans = Set.insert name (sharedLoans context) })
  | Map.member name (unrestrictedBindings context) =
      Left (WrongStructuralMode name Affine Unrestricted)
  | otherwise = Left (UnknownBinding name)

endSharedLoan :: Name -> ResourceContext -> Either CheckError ResourceContext
endSharedLoan name context
  | Set.member name (sharedLoans context) =
      Right (context { sharedLoans = Set.delete name (sharedLoans context) })
  | otherwise = Left (LoanNotActive name)

ensureComplete :: ResourceContext -> Either CheckError ()
ensureComplete context
  | not (Set.null (sharedLoans context)) = Left (EscapingLoans (sharedLoans context))
  | not (Map.null (linearBindings context)) = Left (UnconsumedLinearResources (linearBindings context))
  | otherwise = Right ()

joinContinuing :: [ResourceContext] -> Either CheckError ResourceContext
joinContinuing [] = Right emptyContext
joinContinuing (firstContext : rest) = do
  mapM_ ensureNoEscapingLoans (firstContext : rest)
  mapM_ (ensureSameUnrestricted firstContext) rest
  mapM_ (ensureSameLinear firstContext) rest
  commonAffine <- foldl' intersectAffine (Right (affineBindings firstContext)) (map affineBindings rest)
  pure (ResourceContext
    { unrestrictedBindings = unrestrictedBindings firstContext
    , affineBindings = commonAffine
    , linearBindings = linearBindings firstContext
    , sharedLoans = Set.empty
    })

bindingExists :: Name -> ResourceContext -> Bool
bindingExists name context =
  Map.member name (unrestrictedBindings context)
    || Map.member name (affineBindings context)
    || Map.member name (linearBindings context)

actualMode :: Name -> ResourceContext -> Maybe Mode
actualMode name context
  | Map.member name (unrestrictedBindings context) = Just Unrestricted
  | Map.member name (affineBindings context) = Just Affine
  | Map.member name (linearBindings context) = Just Linear
  | otherwise = Nothing

ensureNoEscapingLoans :: ResourceContext -> Either CheckError ()
ensureNoEscapingLoans context
  | Set.null (sharedLoans context) = Right ()
  | otherwise = Left (EscapingLoans (sharedLoans context))

ensureSameUnrestricted :: ResourceContext -> ResourceContext -> Either CheckError ()
ensureSameUnrestricted expected actual
  | unrestrictedBindings expected == unrestrictedBindings actual = Right ()
  | otherwise = Left (UnrestrictedBranchMismatch (unrestrictedBindings expected) (unrestrictedBindings actual))

ensureSameLinear :: ResourceContext -> ResourceContext -> Either CheckError ()
ensureSameLinear expected actual
  | linearBindings expected == linearBindings actual = Right ()
  | otherwise = Left (LinearBranchMismatch (linearBindings expected) (linearBindings actual))

intersectAffine :: Either CheckError (Map Name Ty) -> Map Name Ty -> Either CheckError (Map Name Ty)
intersectAffine accumulated next = do
  current <- accumulated
  case firstTypeMismatch current next of
    Just (name, leftTy, rightTy) -> Left (AffineBranchTypeMismatch name leftTy rightTy)
    Nothing -> Right (Map.intersection current next)

firstTypeMismatch :: Map Name Ty -> Map Name Ty -> Maybe (Name, Ty, Ty)
firstTypeMismatch left right =
  case
    [ (name, leftTy, rightTy)
    | (name, leftTy) <- Map.toList left
    , Just rightTy <- [Map.lookup name right]
    , leftTy /= rightTy
    ] of
      [] -> Nothing
      mismatch : _ -> Just mismatch
