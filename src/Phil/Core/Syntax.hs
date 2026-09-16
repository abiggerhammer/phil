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
  , runtimeBytesLengthIndex
  , runtimeBytesType
  , isRuntimeBytesType
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
  | SortUInt Int
  | SortEnum Text
  | SortFiniteSeq RefSort
  | SortFiniteSet RefSort
  | SortStableId Text
  | SortOpaque Text
  deriving (Eq, Ord, Show)

-- | Structured terms in the Phase 0 refinement fragment. These are semantic
-- terms, not source syntax. UInt values remain distinct from Nat until an
-- explicit/canonical RefToNat node is present. Field/opaque leaves carry the
-- sort established by elaboration so Core never has to infer it from spelling.
data RefTerm
  = RefVar Name
  | RefNat Integer
  | RefUInt Int Integer
  | RefBool Bool
  | RefField RefTerm Text RefSort
  | RefLen RefTerm
  | RefToNat RefTerm
  | RefAdd RefTerm RefTerm
  | RefSub RefTerm RefTerm
  | RefScale Integer RefTerm
  | RefOpaque RefSort Text
  deriving (Eq, Ord, Show)

data Ty
  = TyUnit
  | TyBool
  | TyUInt Int
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

-- | Bare Phase-1 Bytes is the same semantic family as Bytes[n], with the exact
-- length index deliberately not tracked in the type.  This marker is an
-- internal type-level tag, not an existential value, host-buffer identity, or
-- claim about any particular runtime length.
runtimeBytesLengthIndex :: RefTerm
runtimeBytesLengthIndex = RefOpaque SortNat "phil.bytes.runtime-size-untracked"

runtimeBytesType :: Ty
runtimeBytesType = TyBytes runtimeBytesLengthIndex

isRuntimeBytesType :: Ty -> Bool
isRuntimeBytesType ty = case ty of
  TyBytes index -> index == runtimeBytesLengthIndex
  _ -> False

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
