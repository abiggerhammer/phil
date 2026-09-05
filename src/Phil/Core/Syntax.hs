{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Syntax
  ( Name (..)
  , GrammarId (..)
  , FrameId (..)
  , Mode (..)
  , ProductElementType (..)
  , ProductValue (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  , Proposition (..)
  , Outcome (..)
  , Branch (..)
  , PendingRecvSpec (..)
  , Session (..)
  , Control (..)
  , ObligationId (..)
  , Obligation (..)
  ) where

import Data.Text (Text)

newtype Name = Name { unName :: Text }
  deriving (Eq, Ord, Show)

newtype GrammarId = GrammarId { unGrammarId :: Text }
  deriving (Eq, Ord, Show)

newtype FrameId = FrameId { unFrameId :: Text }
  deriving (Eq, Ord, Show)

data Mode
  = Unrestricted
  | Affine
  | Linear
  deriving (Eq, Ord, Show)

data ProductElementType = ProductElementType
  { productElementMode :: Mode
  , productElementType :: Ty
  }
  deriving (Eq, Ord, Show)

newtype ProductValue = ProductValue
  { productValueElements :: [ProductElementType]
  }
  deriving (Eq, Ord, Show)

data RefSort
  = SortBool
  | SortNat
  | SortInteger
  | SortUInt Int
  | SortSInt Int
  | SortEnum Text
  | SortFiniteSeq RefSort
  | SortFiniteSet RefSort
  | SortStableId Text
  | SortOpaque Text
  deriving (Eq, Ord, Show)

-- | Structured terms in the Phase 0/1 refinement fragment. These are semantic
-- terms, not source syntax. Fixed-width integer values retain width and
-- signedness until an explicit/canonical mathematical view is requested.
data RefTerm
  = RefVar Name
  | RefNat Integer
  | RefUInt Int Integer
  | RefSInt Int Integer
  | RefBool Bool
  | RefField RefTerm Text RefSort
  | RefLen RefTerm
  | RefToNat RefTerm
  | RefToInteger RefTerm
  | RefAdd RefTerm RefTerm
  | RefSub RefTerm RefTerm
  | RefScale Integer RefTerm
  | RefOpaque RefSort Text
  deriving (Eq, Ord, Show)

data Ty
  = TyUnit
  | TyBool
  | TyUInt Int
  | TySInt Int
  | TyBytes RefTerm
  | TyFrame GrammarId
  | TyPendingRecv PendingRecvSpec
  | TyProof Proposition
  | TyValidated Text Name Name
  | TyEndpoint Session
  | TyProduct [ProductElementType]
  | TyRefined Name Ty Proposition
  | TyOpaque Text
  | TyOpaqueSorted Text RefSort
  deriving (Eq, Ord, Show)

-- | The legacy Core Value carrier remains the Phase-0 executable value surface.
-- Phase-1 fixed-width signed literals travel through ScalarLiteral/RefTerm until
-- the general executable Value carrier is widened in its own compatibility pass.
data Value
  = VVar Name
  | VUnit
  | VBool Bool
  | VUInt Int Integer
  | VAscribe Value Ty
  | VTransport Value Name Ty
  deriving (Eq, Ord, Show)

data Proposition
  = Truth
  | Falsehood
  | Equal RefTerm RefTerm
  | NotEqual RefTerm RefTerm
  | LessThan RefTerm RefTerm
  | LessEqual RefTerm RefTerm
  | Member RefTerm RefTerm
  | Disjoint RefTerm RefTerm
  | Conjunction Proposition Proposition
  | Disjunction Proposition Proposition
  | Negation Proposition
  | Atom Text [RefTerm]
  deriving (Eq, Ord, Show)

newtype Outcome = Outcome { unOutcome :: Text }
  deriving (Eq, Ord, Show)

data Branch = Branch
  { branchLabel :: Text
  , branchPayload :: Maybe (Name, Ty)
  , branchContinuation :: Session
  }
  deriving (Eq, Ord, Show)

data PendingRecvSpec = PendingRecvSpec
  { pendingSourceEndpoint :: Name
  , pendingGrammar :: GrammarId
  , pendingFrame :: FrameId
  , pendingBinder :: Name
  , pendingContinuation :: Session
  }
  deriving (Eq, Ord, Show)

data Session
  = Send Name Ty Session
  | Receive Name Ty Session
  | Select [Branch]
  | Offer [Branch]
  | End Outcome
  | Rec Name Session
  | SessionVar Name
  deriving (Eq, Ord, Show)

data Control
  = Continue
  | Return Ty
  | Closed Outcome
  | Failed Text Text
  deriving (Eq, Ord, Show)

newtype ObligationId = ObligationId { unObligationId :: Text }
  deriving (Eq, Ord, Show)

data Obligation = Obligation
  { obligationId :: ObligationId
  , obligationProposition :: Proposition
  , obligationOrigin :: Text
  , obligationScope :: Text
  , obligationRequiredPoint :: Text
  }
  deriving (Eq, Ord, Show)
