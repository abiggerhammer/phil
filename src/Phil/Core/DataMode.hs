module Phil.Core.DataMode
  ( modeLub
  , deriveRecordMode
  , deriveSumMode
  ) where

import Phil.Core.Syntax (Mode (..))

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
