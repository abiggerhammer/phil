module Main (main) where

import System.Exit (exitFailure)
import UTF8ImplementationKernel

main :: IO ()
main = do
  let controls =
        [ ("predecessor rejection wins over successful provider/decode",
            isPredecessorRejected
              (decideReadUTF8ByFacts False True True))
        , ("predecessor rejection wins over successful provider/failed decode",
            isPredecessorRejected
              (decideReadUTF8ByFacts False True False))
        , ("predecessor rejection wins over provider failure",
            isPredecessorRejected
              (decideReadUTF8ByFacts False False True))
        , ("predecessor rejection ignores provider/decode facts",
            isPredecessorRejected
              (decideReadUTF8ByFacts False False False))
        , ("successful provider plus valid decode classifies decoded",
            isDecoded
              (decideReadUTF8ByFacts True True True))
        , ("successful provider plus invalid decode classifies decode failure",
            isDecodeFailed
              (decideReadUTF8ByFacts True True False))
        , ("provider failure bypasses decode success fact",
            isProviderFailed
              (decideReadUTF8ByFacts True False True))
        , ("provider failure bypasses decode failure fact",
            isProviderFailed
              (decideReadUTF8ByFacts True False False))
        , ("write_utf8 rejects rejected predecessor",
            isCompositionRejected
              (decideWriteUTF8ByFacts False))
        , ("write_utf8 accepts accepted predecessor",
            isCompositionAccepted
              (decideWriteUTF8ByFacts True))
        , ("write_line rejects rejected predecessor",
            isCompositionRejected
              (decideWriteLineByFacts False))
        , ("write_line accepts accepted predecessor",
            isCompositionAccepted
              (decideWriteLineByFacts True))
        ]
  mapM_ report controls
  if all snd controls then pure () else exitFailure

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "IO-CODEC kernel " <> label)

isPredecessorRejected :: UTF8ReadDecision -> Bool
isPredecessorRejected value = case value of
  UTF8ReadPredecessorRejected -> True
  _ -> False

isDecoded :: UTF8ReadDecision -> Bool
isDecoded value = case value of
  UTF8ReadDecoded -> True
  _ -> False

isDecodeFailed :: UTF8ReadDecision -> Bool
isDecodeFailed value = case value of
  UTF8ReadDecodeFailed -> True
  _ -> False

isProviderFailed :: UTF8ReadDecision -> Bool
isProviderFailed value = case value of
  UTF8ReadProviderFailed -> True
  _ -> False

isCompositionAccepted :: UTF8CompositionDecision -> Bool
isCompositionAccepted value = case value of
  UTF8CompositionAccepted -> True
  _ -> False

isCompositionRejected :: UTF8CompositionDecision -> Bool
isCompositionRejected value = case value of
  UTF8CompositionPredecessorRejected -> True
  _ -> False
