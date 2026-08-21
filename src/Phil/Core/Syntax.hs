{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Syntax
  ( Name (..)
  , Mode (..)
  , Ty (..)
  , Proposition (..)
  , Outcome (..)
  , Branch (..)
  , Session (..)
  , Control (..)
  , ObligationId (..)
  , Obligation (..)
  ) where

import Data.Text (Text)

newtype Name = Name { unName :: Text }
  deriving (Eq, Ord, Show)

data Mode
  = Unrestricted
  | Affine
  | Linear
  deriving (Eq, Ord, Show)

data Ty
  = TyUnit
  | TyBool
  | TyUInt Int
  | TyBytes Text
  | TyProof Proposition
  | TyEndpoint Session
  | TyRefined Name Ty Proposition
  | TyOpaque Text
  deriving (Eq, Ord, Show)

data Proposition
  = Truth
  | Atom Text [Text]
  | Equal Text Text
  | Conjunction Proposition Proposition
  deriving (Eq, Ord, Show)

newtype Outcome = Outcome { unOutcome :: Text }
  deriving (Eq, Ord, Show)

data Branch = Branch
  { branchLabel :: Text
  , branchPayload :: Maybe (Name, Ty)
  , branchContinuation :: Session
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
  , obligationRequiredPoint :: Text
  }
  deriving (Eq, Ord, Show)
