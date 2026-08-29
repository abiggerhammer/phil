{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Authority
import Phil.Core.AuthorityAttenuation
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "AUTH-003 binding rejects empty join" emptyJoinRejects
    , test "AUTH-003 binding accepts exact attenuation" exactAttenuationAccepts
    , test "AUTH-003 binding requires witness for contract change" contractChangeNeedsWitness
    , test "AUTH-003 binding accepts witnessed boundary narrowing" witnessedBoundaryAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

emptyJoinRejects :: Either String ()
emptyJoinRejects = case checkAuthorityJoin [] readSurface of
  Left AuthorityJoinEmpty -> Right ()
  other -> Left ("empty join did not fail closed: " <> show other)

exactAttenuationAccepts :: Either String ()
exactAttenuationAccepts = case checkExplicitAuthorityAttenuation
    broadSurface readSurface readWitness of
  Right checked
    | checkedAuthorityAttenuationTarget checked == readSurface -> Right ()
    | otherwise -> Left "accepted attenuation changed target surface"
  other -> Left ("exact attenuation did not accept: " <> show other)

contractChangeNeedsWitness :: Either String ()
contractChangeNeedsWitness = case checkAuthorityBoundary
    AuthorityArchitectureBoundary broadSurface readSurface Nothing of
  Left (AuthorityBoundaryContractChangeWithoutAttenuation _ source target)
    | source == broadContract && target == readContract -> Right ()
    | otherwise -> Left "contract-change diagnostic carried wrong contracts"
  other -> Left ("contract change without witness did not reject: " <> show other)

witnessedBoundaryAccepts :: Either String ()
witnessedBoundaryAccepts = case checkAuthorityBoundary
    AuthorityGenericBinding broadSurface readSurface (Just readWitness) of
  Right checked -> case checkedAuthorityBoundaryAttenuation checked of
    Just attenuation
      | checkedAuthorityAttenuationTarget attenuation == readSurface -> Right ()
      | otherwise -> Left "boundary attenuation changed target surface"
    Nothing -> Left "witnessed narrowing lost attenuation evidence"
  other -> Left ("witnessed boundary narrowing did not accept: " <> show other)

broadContract, readContract :: AuthorityContractKey
broadContract = AuthorityContractKey "storage.read-write.v1"
readContract = AuthorityContractKey "storage.read.v1"

subject :: AuthoritySubjectKey
subject = AuthoritySubjectKey "blob-store.primary"

readOperation, writeOperation :: AuthorityOperationKey
readOperation = AuthorityOperationKey "read"
writeOperation = AuthorityOperationKey "write"

broadSurface, readSurface :: AuthoritySurface
broadSurface = AuthoritySurface broadContract subject
  (Set.fromList [readOperation, writeOperation])
readSurface = AuthoritySurface readContract subject (Set.singleton readOperation)

readWitness :: AuthorityAttenuationWitness
readWitness = AuthorityAttenuationWitness
  broadContract readContract subject (Set.singleton readOperation)
