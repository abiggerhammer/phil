module Phil.Core.DataMode
  ( ModeExpr (..)
  , modeLub
  , deriveRecordMode
  , deriveSumMode
  , instantiateMode
  ) where

import Phil.Core.Syntax (Mode (..))

data ModeExpr
  = FixedMode Mode
  | ParameterMode String
  | StrongestMode [ModeExpr]
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
