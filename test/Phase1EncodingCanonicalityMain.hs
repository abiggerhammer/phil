{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryMapping (BoundaryRepresentationId (..))
import Phil.Core.EncodingCanonicality
import Phil.Core.QualifiedEncoding
import Phil.Core.Syntax (Name (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "BND-009 valid encoding does not imply canonicality" validNoncanonicalWithoutCanonicalContract
    , test "BND-009 declared canonical encoding rejects noncanonical legal member" declaredCanonicalRejectsNoncanonical
    , test "BND-009 declared canonical encoding accepts canonical member" declaredCanonicalAcceptsCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validNoncanonicalWithoutCanonicalContract :: Either String ()
validNoncanonicalWithoutCanonicalContract = do
  evidence <- exactEncodingEvidence
  accepted <- mapLeft show $
    checkEncodingCanonicality CanonicalityNotRequired NonCanonicalLegalGrammarMember evidence
  assert (accepted == evidence) "ordinary valid encoding was changed or rejected by undeclared canonicality"

declaredCanonicalRejectsNoncanonical :: Either String ()
declaredCanonicalRejectsNoncanonical = do
  evidence <- exactEncodingEvidence
  case checkEncodingCanonicality CanonicalEncodingRequired NonCanonicalLegalGrammarMember evidence of
    Left (NonCanonicalEncodingRejected actualRep actualOwner) -> do
      assert (actualRep == representation) "canonicality rejection named wrong representation"
      assert (actualOwner == outputOwner) "canonicality rejection named wrong output owner"
    other -> Left ("expected noncanonical rejection, got: " <> show other)

declaredCanonicalAcceptsCanonical :: Either String ()
declaredCanonicalAcceptsCanonical = do
  evidence <- exactEncodingEvidence
  accepted <- mapLeft show $
    checkEncodingCanonicality CanonicalEncodingRequired CanonicalGrammarMember evidence
  assert (accepted == evidence) "canonical member did not preserve exact encoding evidence"

exactEncodingEvidence :: Either String GeneratedEncodingEvidence
exactEncodingEvidence =
  mapLeft show $
    establishGeneratedEncoding encoder representation outputOwner outputOwner

encoder :: QualifiedEncoder
encoder = QualifiedEncoder
  { encoderImplementation = Name "upload.encoder"
  , encoderRepresentation = representation
  , encoderAdmission = EncodingAdmitted
  }

representation :: BoundaryRepresentationId
representation = BoundaryRepresentationId "UploadBoundary@rev1"

outputOwner :: Name
outputOwner = Name "encoded-frame"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
