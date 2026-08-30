module Main (main) where

import ArchitectureImportKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then pure () else error ("architecture import correspondence failed: " ++ label)

isAccepted :: ImportResolutionDecision -> Bool
isAccepted ImportResolutionDecisionAccepted = True
isAccepted _ = False

isUnknownExport :: ImportResolutionDecision -> Bool
isUnknownExport UnknownSelectedExportDecision = True
isUnknownExport _ = False

isDuplicateName :: ImportResolutionDecision -> Bool
isDuplicateName DuplicateResolutionNameDecision = True
isDuplicateName _ = False

planExact :: Bool
planExact =
  case planImportedBinding ("Store" :: String) ("declaration.identity" :: String) of
    MkImportedBindingPlan localName identity ->
      localName == "Store" && identity == "declaration.identity"

main :: IO ()
main = do
  assert "selected export plus fresh local name accepts"
    (isAccepted (decideImportResolutionByFacts True True))
  assert "unknown export rejects before local-name facts"
    (isUnknownExport (decideImportResolutionByFacts False True))
  assert "unknown export still wins when local name also collides"
    (isUnknownExport (decideImportResolutionByFacts False False))
  assert "duplicate local name rejects after export selection"
    (isDuplicateName (decideImportResolutionByFacts True False))
  assert "binding plan preserves local spelling and declaration identity" planExact
