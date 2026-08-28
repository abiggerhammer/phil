{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.NominalDataMode
  ( NominalModeError (..)
  , NominalRestrictionJustification (..)
  , checkRecordMode
  , checkSumMode
  )
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-014 omitted record mode derives minimum" omittedRecordMode
    , test "DATA-014 omitted sum mode derives conservative minimum" omittedSumMode
    , test "DATA-014 justified record strengthening accepts" justifiedRecordStrengthening
    , test "DATA-014 justified sum strengthening accepts" justifiedSumStrengthening
    , test "DATA-014 explicit equal mode needs no extra justification" explicitEqualMode
    , test "DATA-014 weaker declared mode rejects" weakerModeRejects
    , test "DATA-014 unjustified strengthening rejects" unjustifiedStrengtheningRejects
    , test "DATA-014 unadmitted strengthening rejects" unadmittedStrengtheningRejects
    , test "DATA-014 empty admitted justification rejects" emptyJustificationRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

omittedRecordMode :: Either String ()
omittedRecordMode = do
  actual <- mapLeft show $ checkRecordMode [Unrestricted, Affine] Nothing Nothing
  assert (actual == Affine) "omitted record mode did not derive affine minimum"

omittedSumMode :: Either String ()
omittedSumMode = do
  actual <- mapLeft show $ checkSumMode [[Unrestricted], [Linear]] Nothing Nothing
  assert (actual == Linear) "omitted sum mode did not derive conservative linear minimum"

justifiedRecordStrengthening :: Either String ()
justifiedRecordStrengthening = do
  actual <- mapLeft show $ checkRecordMode
    [Unrestricted]
    (Just Linear)
    (Just (AdmittedLifecycleObligation "FireOnceToken must be discharged exactly once"))
  assert (actual == Linear) "justified record strengthening did not become linear"

justifiedSumStrengthening :: Either String ()
justifiedSumStrengthening = do
  actual <- mapLeft show $ checkSumMode
    [[Unrestricted], [Unrestricted]]
    (Just Affine)
    (Just (AdmittedResourceObligation "MaybeLease carries a droppable but non-copyable lease occurrence"))
  assert (actual == Affine) "justified sum strengthening did not become affine"

explicitEqualMode :: Either String ()
explicitEqualMode = do
  actual <- mapLeft show $ checkRecordMode [Linear] (Just Linear) Nothing
  assert (actual == Linear) "explicit mode equal to derived minimum changed semantics"

weakerModeRejects :: Either String ()
weakerModeRejects =
  case checkRecordMode [Linear] (Just Affine) Nothing of
    Left (DeclaredModeWeakensDerived Linear Affine) -> Right ()
    other -> Left ("weaker mode was not rejected correctly: " <> show other)

unjustifiedStrengtheningRejects :: Either String ()
unjustifiedStrengtheningRejects =
  case checkRecordMode [Unrestricted] (Just Linear) Nothing of
    Left (StrongerModeMissingJustification Unrestricted Linear) -> Right ()
    other -> Left ("unjustified strengthening was not rejected correctly: " <> show other)

unadmittedStrengtheningRejects :: Either String ()
unadmittedStrengtheningRejects =
  case checkSumMode [[Unrestricted]] (Just Affine)
    (Just (UnadmittedNominalRestriction "annotation has no admitted semantic contract")) of
    Left (StrongerModeUnadmittedJustification _) -> Right ()
    other -> Left ("unadmitted strengthening was not rejected correctly: " <> show other)

emptyJustificationRejects :: Either String ()
emptyJustificationRejects =
  case checkRecordMode [Unrestricted] (Just Affine)
    (Just (AdmittedAuthorityLifecycleObligation "")) of
    Left StrongerModeEmptyJustification -> Right ()
    other -> Left ("empty admitted justification was not rejected correctly: " <> show other)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
