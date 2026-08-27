{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryMapping (BoundaryRepresentationId (..))
import Phil.Core.BoundarySerialization
import Phil.Core.Syntax (Name (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "BND-010 checked wire correspondence accepts" checkedWireAccepts
    , test "BND-010 raw memory layout rejects" rawMemoryRejects
    , test "BND-010 matching C struct shape rejects" matchingStructRejects
    , test "BND-010 wrong representation rejects" wrongRepresentationRejects
    , test "BND-010 wrong subject rejects" wrongSubjectRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedWireAccepts :: Either String ()
checkedWireAccepts = mapLeft show $ checkBoundarySerialization rep subject
  (SerializationCorrespondence rep subject CheckedWireCorrespondence)

rawMemoryRejects :: Either String ()
rawMemoryRejects = case checkBoundarySerialization rep subject
    (SerializationCorrespondence rep subject RawMemoryLayout) of
  Left (UncheckedSerializationBasis RawMemoryLayout) -> Right ()
  other -> Left ("expected raw-memory rejection, got: " <> show other)

matchingStructRejects :: Either String ()
matchingStructRejects = case checkBoundarySerialization rep subject
    (SerializationCorrespondence rep subject MatchingCStructShape) of
  Left (UncheckedSerializationBasis MatchingCStructShape) -> Right ()
  other -> Left ("expected matching-struct rejection, got: " <> show other)

wrongRepresentationRejects :: Either String ()
wrongRepresentationRejects = case checkBoundarySerialization rep subject
    (SerializationCorrespondence otherRep subject CheckedWireCorrespondence) of
  Left (SerializationRepresentationMismatch expected actual)
    | expected == rep && actual == otherRep -> Right ()
  other -> Left ("expected representation mismatch, got: " <> show other)

wrongSubjectRejects :: Either String ()
wrongSubjectRejects = case checkBoundarySerialization rep subject
    (SerializationCorrespondence rep otherSubject CheckedWireCorrespondence) of
  Left (SerializationSubjectMismatch expected actual)
    | expected == subject && actual == otherSubject -> Right ()
  other -> Left ("expected subject mismatch, got: " <> show other)

rep, otherRep :: BoundaryRepresentationId
rep = BoundaryRepresentationId "UploadBoundary@rev1"
otherRep = BoundaryRepresentationId "UploadBoundary@rev2"

subject, otherSubject :: Name
subject = Name "payload"
otherSubject = Name "other"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
