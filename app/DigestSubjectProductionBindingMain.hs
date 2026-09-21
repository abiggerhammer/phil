{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Syntax
  ( Name (..)
  , RefSort (..)
  , RefTerm (..)
  )
import Phil.Surface.Check.DigestSubjectCertification
import qualified SurfaceDigestSubjectKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  let begin = Name "begin"
      owner = RefOpaque (SortStableId "OwnedBytes") "payload"
      otherOwner = RefOpaque (SortStableId "OwnedBytes") "other"
      checks =
        [ ("real extracted kernel preserves exact subjects",
            certifyDigestSubject begin owner == Right (begin, owner))
        , ("injected kernel rejection fails closed",
            certifyDigestSubjectWith rejecting begin owner
              == Left DigestSubjectKernelRejected)
        , ("injected Begin substitution fails closed",
            case certifyDigestSubjectWith substituteBegin begin owner of
              Left (DigestSubjectKernelSubstitution _ _ _ _) -> True
              _ -> False)
        , ("injected stable-owner substitution fails closed",
            case certifyDigestSubjectWith (substituteOwner otherOwner) begin owner of
              Left (DigestSubjectKernelSubstitution _ _ _ _) -> True
              _ -> False)
        , ("distinct owners remain distinct through exact kernel",
            case
              ( certifyDigestSubject begin owner
              , certifyDigestSubject begin otherOwner
              ) of
                (Right (_, left), Right (_, right)) -> left /= right
                _ -> False)
        ]
  mapM_ report checks
  if all snd checks then pure () else exitFailure

rejecting :: DigestSubjectDecision
rejecting _ _ _ _ _ _ _ _ _ =
  Kernel.SurfaceDigestPayloadTypeRejected

substituteBegin :: DigestSubjectDecision
substituteBegin _ _ _ _ _ _ _ _ owner =
  Kernel.SurfaceDigestSubjectAccepted (Name "substituted") owner

substituteOwner :: RefTerm -> DigestSubjectDecision
substituteOwner replacement _ _ _ _ _ _ _ begin _ =
  Kernel.SurfaceDigestSubjectAccepted begin replacement

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ")
    <> "PHIL-AUD-DIGEST-SUBJECT-001 production " <> label)
