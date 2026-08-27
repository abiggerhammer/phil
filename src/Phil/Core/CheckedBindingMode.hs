module Phil.Core.CheckedBindingMode
  ( BindingOrigin (..)
  , CheckedTypeMode (..)
  , CheckedBindingModeError (..)
  , insertCheckedBinding
  ) where

import Phil.Core.Context
  ( CheckError
  , ResourceContext
  , insertBinding
  )
import Phil.Core.Syntax (Mode, Name, Ty)

-- | Ordinary source/elaboration sites that create owning bindings.  The origin
-- is diagnostic/accounting information; every origin is governed by the same
-- checked type-to-mode relation.
data BindingOrigin
  = TermParameterBinding
  | LetBinding
  | OwningPatternBinding
  | EntryValueBinding
  | SuccessorBinding
  deriving (Eq, Ord, Show)

-- | The exact structural mode established by checking the binding's type or
-- semantic resource contract.  This is the authority for zone placement; a
-- separately carried implementation mode may not reclassify the binding.
data CheckedTypeMode = CheckedTypeMode
  { checkedBindingType :: Ty
  , checkedBindingMode :: Mode
  }
  deriving (Eq, Show)

data CheckedBindingModeError
  = CheckedBindingTypeMismatch BindingOrigin Name Ty Ty
  | CheckedBindingModeMismatch BindingOrigin Name Mode Mode
  | CheckedBindingContextError BindingOrigin CheckError
  deriving (Eq, Show)

-- | RES-012 bridge from checked type semantics to ResourceContext placement.
-- The caller may carry type and mode separately for implementation convenience,
-- but both must agree exactly with the checked type-mode contract.
insertCheckedBinding
  :: BindingOrigin
  -> CheckedTypeMode
  -> Mode
  -> Name
  -> Ty
  -> ResourceContext
  -> Either CheckedBindingModeError ResourceContext
insertCheckedBinding origin checked suppliedMode name suppliedType context
  | suppliedType /= checkedBindingType checked =
      Left (CheckedBindingTypeMismatch
        origin name (checkedBindingType checked) suppliedType)
  | suppliedMode /= checkedBindingMode checked =
      Left (CheckedBindingModeMismatch
        origin name (checkedBindingMode checked) suppliedMode)
  | otherwise =
      mapLeft (CheckedBindingContextError origin) $
        insertBinding (checkedBindingMode checked) name suppliedType context

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
