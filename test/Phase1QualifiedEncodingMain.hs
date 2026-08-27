{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryMapping (BoundaryRepresentationId (..))
import Phil.Core.QualifiedEncoding
import Phil.Core.Syntax (Name (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  let exact = establishGeneratedEncoding admittedEncoder representation outputOwner outputOwner
      unadmitted = establishGeneratedEncoding unadmittedEncoder representation outputOwner outputOwner
      wrongRepresentation = establishGeneratedEncoding admittedEncoder otherRepresentation outputOwner outputOwner
      wrongOwner = establishGeneratedEncoding admittedEncoder representation outputOwner otherOwner
      results =
        [ ("BND-008 admitted exact encoding establishes exact output evidence", case exact of
              Right evidence ->
                generatedByImplementation evidence == implementation
                  && generatedRepresentation evidence == representation
                  && generatedOutputOwner evidence == outputOwner
              _ -> False)
        , ("BND-008 unadmitted encoder rejects", case unadmitted of
              Left (EncoderNotAdmitted actual) -> actual == implementation
              _ -> False)
        , ("BND-008 wrong representation revision rejects", case wrongRepresentation of
              Left (EncodingRepresentationMismatch actual expected) ->
                actual == representation && expected == otherRepresentation
              _ -> False)
        , ("BND-008 wrong output subject rejects", case wrongOwner of
              Left (EncodingOutputOwnerMismatch expected actual) ->
                expected == outputOwner && actual == otherOwner
              _ -> False)
        ]
  mapM_ report results
  if all snd results then pure () else exitFailure

admittedEncoder :: QualifiedEncoder
admittedEncoder = QualifiedEncoder implementation representation EncodingAdmitted

unadmittedEncoder :: QualifiedEncoder
unadmittedEncoder = QualifiedEncoder implementation representation EncodingNotAdmitted

implementation, outputOwner, otherOwner :: Name
implementation = Name "upload-encoder@impl1"
outputOwner = Name "bytes-out"
otherOwner = Name "other-bytes"

representation, otherRepresentation :: BoundaryRepresentationId
representation = BoundaryRepresentationId "UploadBoundary@rev1"
otherRepresentation = BoundaryRepresentationId "UploadBoundary@rev2"

report :: (String, Bool) -> IO ()
report (label, ok) = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
