module Phil.Surface.Check.DigestSubjectCertification
  ( DigestSubjectCertificationError (..)
  , DigestSubjectDecision
  , certifyDigestSubject
  , certifyDigestSubjectWith
  ) where

import Phil.Core.Syntax (Name, RefTerm)
import qualified SurfaceDigestSubjectKernel as Kernel

data DigestSubjectCertificationError
  = DigestSubjectKernelRejected
  | DigestSubjectKernelSubstitution
      Name
      RefTerm
      Name
      RefTerm
  deriving (Eq, Show)

type DigestSubjectDecision =
  Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
  Name -> RefTerm ->
  Kernel.SurfaceDigestSubjectDecision Name RefTerm

certifyDigestSubject
  :: Name
  -> RefTerm
  -> Either DigestSubjectCertificationError (Name, RefTerm)
certifyDigestSubject =
  certifyDigestSubjectWith Kernel.decideSurfaceDigestSubjectByFacts

certifyDigestSubjectWith
  :: DigestSubjectDecision
  -> Name
  -> RefTerm
  -> Either DigestSubjectCertificationError (Name, RefTerm)
certifyDigestSubjectWith decide beginSubject stableOwner =
  case decide
      True True True True True True True
      beginSubject stableOwner of
    Kernel.SurfaceDigestSubjectAccepted acceptedBegin acceptedOwner
      | acceptedBegin == beginSubject
      , acceptedOwner == stableOwner ->
          Right (acceptedBegin, acceptedOwner)
      | otherwise ->
          Left (DigestSubjectKernelSubstitution
            beginSubject stableOwner acceptedBegin acceptedOwner)
    _ -> Left DigestSubjectKernelRejected
