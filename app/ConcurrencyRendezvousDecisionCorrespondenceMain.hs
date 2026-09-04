module Main (main) where

import qualified ConcurrencyRendezvousKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "endpoint facts all true accept" True
        (endpoint True True True True True True True True True)
    , test "binary well-formed false rejects" False
        (endpoint False True True True True True True True True)
    , test "sender progression false rejects" False
        (endpoint True False True True True True True True True)
    , test "receiver progression false rejects" False
        (endpoint True True False True True True True True True)
    , test "sender instance mismatch rejects" False
        (endpoint True True True False True True True True True)
    , test "receiver instance mismatch rejects" False
        (endpoint True True True True False True True True True)
    , test "sender role mismatch rejects" False
        (endpoint True True True True True False True True True)
    , test "receiver role mismatch rejects" False
        (endpoint True True True True True True False True True)
    , test "current sessions non-dual rejects" False
        (endpoint True True True True True True True False True)
    , test "successor sessions non-dual rejects" False
        (endpoint True True True True True True True True False)
    , test "participant facts all true accept" True
        (participants True True True True True)
    , test "participant classification invalid rejects" False
        (participants False True True True True)
    , test "sender participant mismatch rejects" False
        (participants True False True True True)
    , test "receiver participant mismatch rejects" False
        (participants True True False True True)
    , test "sender role occurrence mismatch rejects" False
        (participants True True True False True)
    , test "receiver role occurrence mismatch rejects" False
        (participants True True True True False)
    , test "message/coarse facts all true accept" True
        (messageCoarse True True True True True True True)
    , test "Message admission false rejects" False
        (messageCoarse False True True True True True True)
    , test "coarse rendezvous invalid rejects" False
        (messageCoarse True False True True True True True)
    , test "coarse instance mismatch rejects" False
        (messageCoarse True True False True True True True)
    , test "coarse sender role mismatch rejects" False
        (messageCoarse True True True False True True True)
    , test "coarse receiver role mismatch rejects" False
        (messageCoarse True True True True False True True)
    , test "coarse sender process mismatch rejects" False
        (messageCoarse True True True True True False True)
    , test "coarse receiver process mismatch rejects" False
        (messageCoarse True True True True True True False)
    , test "exact rendezvous all groups true accepts" True
        (exactRendezvous True True True)
    , test "exact rendezvous endpoint group false rejects" False
        (exactRendezvous False True True)
    , test "exact rendezvous participant group false rejects" False
        (exactRendezvous True False True)
    , test "exact rendezvous Message/coarse group false rejects" False
        (exactRendezvous True True False)
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> Bool -> IO Bool
test label expected actual
  | actual == expected = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = do
      putStrLn ("FAIL: " <> label <> " -- expected " <> show expected <> ", got " <> show actual)
      pure False

endpoint
  :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> Bool
endpoint = Kernel.decideRendezvousEndpointFactsByFacts

participants :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
participants = Kernel.decideRendezvousParticipantFactsByFacts

messageCoarse :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
messageCoarse = Kernel.decideRendezvousMessageCoarseFactsByFacts

exactRendezvous :: Bool -> Bool -> Bool -> Bool
exactRendezvous = Kernel.decideExactInternalRendezvousByFacts
