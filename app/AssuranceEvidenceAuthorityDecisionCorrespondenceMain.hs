module Main (main) where

import qualified AssuranceEvidenceAuthorityKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ expect "artifact authority requires declared artifact" isRejected
        (Kernel.decideArtifactAuthorityByFacts False True True)
    , expect "artifact authority requires exact artifact identity" isRejected
        (Kernel.decideArtifactAuthorityByFacts True False True)
    , expect "artifact authority requires trusted digest match" isRejected
        (Kernel.decideArtifactAuthorityByFacts True True False)
    , expect "exact artifact authority facts accept" isAccepted
        (Kernel.decideArtifactAuthorityByFacts True True True)
    , expect "runtime authority requires mechanism presence" isRejected
        (Kernel.decideRuntimeAuthorityByFacts False True True True True)
    , expect "runtime authority requires complete mechanism" isRejected
        (Kernel.decideRuntimeAuthorityByFacts True False True True True)
    , expect "runtime authority requires runtime residue" isRejected
        (Kernel.decideRuntimeAuthorityByFacts True True False True True)
    , expect "runtime authority requires cost reference" isRejected
        (Kernel.decideRuntimeAuthorityByFacts True True True False True)
    , expect "runtime authority requires known cost reference" isRejected
        (Kernel.decideRuntimeAuthorityByFacts True True True True False)
    , expect "exact runtime authority facts accept" isAccepted
        (Kernel.decideRuntimeAuthorityByFacts True True True True True)
    ]
  if and results then pure () else exitFailure

expect :: String -> (a -> Bool) -> a -> IO Bool
expect label predicate actual
  | predicate actual = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = putStrLn ("FAIL: " <> label) >> pure False

isRejected :: Kernel.GateResult -> Bool
isRejected Kernel.GateRejected = True
isRejected _ = False

isAccepted :: Kernel.GateResult -> Bool
isAccepted Kernel.GateAccepted = True
isAccepted _ = False
