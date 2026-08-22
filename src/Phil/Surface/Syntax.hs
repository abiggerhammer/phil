module Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  , Located (..)
  , SurfaceFile (..)
  , Component (..)
  , Parameter (..)
  , Block (..)
  , Statement (..)
  , Pattern (..)
  , SurfaceType (..)
  , BinaryOperator (..)
  , SurfaceExpression (..)
  , SurfaceProposition (..)
  , CasePattern (..)
  , CaseArm (..)
  , BranchValue (..)
  , FailureTarget (..)
  , Fallback (..)
  ) where

import Data.Text (Text)

data SourcePoint = SourcePoint
  { sourcePointFile :: Text
  , sourcePointLine :: Int
  , sourcePointColumn :: Int
  , sourcePointOffset :: Int
  }
  deriving (Eq, Ord, Show)

data SourceSpan = SourceSpan
  { sourceSpanStart :: SourcePoint
  , sourceSpanEnd :: SourcePoint
  }
  deriving (Eq, Ord, Show)

data Located a = Located
  { locatedSpan :: SourceSpan
  , locatedValue :: a
  }
  deriving (Eq, Ord, Show)

newtype SurfaceFile = SurfaceFile
  { surfaceComponents :: [Located Component]
  }
  deriving (Eq, Show)

data Component = Component
  { componentName :: Text
  , componentParameters :: [Located Parameter]
  , componentProvides :: Maybe (Located SurfaceType)
  , componentBody :: Located Block
  }
  deriving (Eq, Show)

data Parameter = Parameter
  { parameterName :: Text
  , parameterType :: Maybe (Located SurfaceType)
  }
  deriving (Eq, Show)

newtype Block = Block
  { blockStatements :: [Located Statement]
  }
  deriving (Eq, Show)

data Statement
  = LetStatement (Located Pattern) (Located SurfaceExpression)
  | ReturnStatement (Located SurfaceExpression)
  | ExpressionStatement (Located SurfaceExpression)
  deriving (Eq, Show)

data Pattern
  = BindPattern Text
  | TuplePattern [Located Pattern]
  deriving (Eq, Show)

data SurfaceType
  = SurfaceUnitType
  | SurfaceBoolType
  | SurfaceUIntType Int
  | SurfaceBytesType (Located SurfaceExpression)
  | SurfaceFrameType Text
  | SurfaceProofType (Located SurfaceProposition)
  | SurfaceValidatedType Text (Located SurfaceExpression) (Located SurfaceExpression)
  | SurfaceNamedType Text [Located SurfaceExpression]
  deriving (Eq, Show)

data BinaryOperator
  = Add
  | Subtract
  | Multiply
  deriving (Eq, Ord, Show)

data SurfaceExpression
  = VariableExpression Text
  | IntegerExpression Integer
  | BooleanExpression Bool
  | UnitExpression
  | TupleExpression [Located SurfaceExpression]
  | CallExpression Text [Located SurfaceExpression]
  | FieldExpression (Located SurfaceExpression) Text
  | BinaryExpression BinaryOperator (Located SurfaceExpression) (Located SurfaceExpression)
  | ConstructExpression Text [(Text, Located SurfaceExpression)]
  | ReceiveExpression (Located SurfaceType) (Located SurfaceExpression)
  | ReceiveFrameExpression (Located SurfaceExpression)
  | RecognizeExpression Text (Located SurfaceExpression)
  | ValidateExpression Text (Maybe (Located SurfaceExpression)) (Located SurfaceExpression)
  | SendExpression (Located SurfaceExpression) (Located SurfaceExpression)
  | SendExactExpression (Located SurfaceExpression) (Located SurfaceExpression)
  | ReceiveExactExpression
      (Located SurfaceExpression)
      (Located SurfaceExpression)
      (Maybe (Located SurfaceExpression))
  | SelectExpression BranchValue (Located SurfaceExpression) (Maybe (Located SurfaceExpression))
  | CommitReceiveExpression (Located SurfaceExpression) (Located SurfaceExpression)
  | BorrowExpression (Located SurfaceExpression) Text (Located Block)
  | DecideExpression (Located SurfaceExpression) [Located CaseArm]
  | OfferExpression (Located SurfaceExpression) [Located CaseArm]
  | FailExpression FailureTarget (Located SurfaceExpression)
  | CloseExpression (Located SurfaceExpression)
  | ReleaseExpression (Located SurfaceExpression)
  | AcceptExpression (Located SurfaceExpression) (Located SurfaceType)
  | ProveExpression (Located SurfaceProposition)
  | FallbackExpression (Located SurfaceExpression) Fallback
  deriving (Eq, Show)

data SurfaceProposition
  = PropositionTrue
  | PropositionFalse
  | PropositionEqual (Located SurfaceExpression) (Located SurfaceExpression)
  | PropositionNotEqual (Located SurfaceExpression) (Located SurfaceExpression)
  | PropositionLessThan (Located SurfaceExpression) (Located SurfaceExpression)
  | PropositionLessEqual (Located SurfaceExpression) (Located SurfaceExpression)
  | PropositionGreaterThan (Located SurfaceExpression) (Located SurfaceExpression)
  | PropositionGreaterEqual (Located SurfaceExpression) (Located SurfaceExpression)
  | PropositionAtom Text [Located SurfaceExpression]
  | PropositionConjunction (Located SurfaceProposition) (Located SurfaceProposition)
  | PropositionDisjunction (Located SurfaceProposition) (Located SurfaceProposition)
  | PropositionNegation (Located SurfaceProposition)
  deriving (Eq, Show)

data CasePattern = CasePattern
  { casePatternLabel :: Text
  , casePatternBinders :: [Text]
  }
  deriving (Eq, Ord, Show)

data CaseArm = CaseArm
  { caseArmPattern :: CasePattern
  , caseArmBody :: Located Block
  }
  deriving (Eq, Show)

data BranchValue = BranchValue
  { branchValueLabel :: Text
  , branchValueArguments :: [Located SurfaceExpression]
  }
  deriving (Eq, Show)

data FailureTarget = FailureTarget
  { failureTargetClass :: Text
  , failureTargetArguments :: [Located SurfaceExpression]
  }
  deriving (Eq, Show)

data Fallback
  = FailFallback Text
  | RejectFallback (Located SurfaceExpression)
  deriving (Eq, Show)
