module Main (main) where

import SurfaceDigestSubjectKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  let controls =
        [ ("accepted decision carries exact Begin and stable owner",
            acceptedCarriesExact)
        , ("distinct stable owners remain distinct",
            distinctOwnersRemainDistinct)
        , ("explicit context rejects first",
            isExplicitContextReject
              (decideSurfaceDigestSubjectByFacts
                False True True True True True True "begin" "payload"))
        , ("wrong arity rejects second",
            isArityReject
              (decideSurfaceDigestSubjectByFacts
                True False True True True True True "begin" "payload"))
        , ("unnamed Begin rejects third",
            isBeginNameReject
              (decideSurfaceDigestSubjectByFacts
                True True False True True True True "begin" "payload"))
        , ("wrong Begin type rejects fourth",
            isBeginTypeReject
              (decideSurfaceDigestSubjectByFacts
                True True True False True True True "begin" "payload"))
        , ("nonborrowed payload rejects fifth",
            isPayloadBorrowReject
              (decideSurfaceDigestSubjectByFacts
                True True True True False True True "begin" "payload"))
        , ("missing stable owner rejects sixth",
            isStableOwnerReject
              (decideSurfaceDigestSubjectByFacts
                True True True True True False True "begin" "payload"))
        , ("wrong payload type rejects seventh",
            isPayloadTypeReject
              (decideSurfaceDigestSubjectByFacts
                True True True True True True False "begin" "payload"))
        ]
  mapM_ report controls
  if all snd controls then pure () else exitFailure

acceptedCarriesExact :: Bool
acceptedCarriesExact =
  case decideSurfaceDigestSubjectByFacts
      True True True True True True True
      "begin.actual" "owner.actual" of
    SurfaceDigestSubjectAccepted begin owner ->
      begin == "begin.actual" && owner == "owner.actual"
    _ -> False

distinctOwnersRemainDistinct :: Bool
distinctOwnersRemainDistinct =
  case
    ( decideSurfaceDigestSubjectByFacts
        True True True True True True True
        "begin" "owner.left"
    , decideSurfaceDigestSubjectByFacts
        True True True True True True True
        "begin" "owner.right"
    ) of
      ( SurfaceDigestSubjectAccepted _ left
        , SurfaceDigestSubjectAccepted _ right
        ) -> left /= right
      _ -> False

isExplicitContextReject :: SurfaceDigestSubjectDecision a b -> Bool
isExplicitContextReject value = case value of
  SurfaceDigestExplicitContextRejected -> True
  _ -> False

isArityReject :: SurfaceDigestSubjectDecision a b -> Bool
isArityReject value = case value of
  SurfaceDigestArityRejected -> True
  _ -> False

isBeginNameReject :: SurfaceDigestSubjectDecision a b -> Bool
isBeginNameReject value = case value of
  SurfaceDigestBeginNameRejected -> True
  _ -> False

isBeginTypeReject :: SurfaceDigestSubjectDecision a b -> Bool
isBeginTypeReject value = case value of
  SurfaceDigestBeginTypeRejected -> True
  _ -> False

isPayloadBorrowReject :: SurfaceDigestSubjectDecision a b -> Bool
isPayloadBorrowReject value = case value of
  SurfaceDigestPayloadBorrowRejected -> True
  _ -> False

isStableOwnerReject :: SurfaceDigestSubjectDecision a b -> Bool
isStableOwnerReject value = case value of
  SurfaceDigestStableOwnerRejected -> True
  _ -> False

isPayloadTypeReject :: SurfaceDigestSubjectDecision a b -> Bool
isPayloadTypeReject value = case value of
  SurfaceDigestPayloadTypeRejected -> True
  _ -> False

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ")
    <> "PHIL-AUD-DIGEST-SUBJECT-001 kernel " <> label)
