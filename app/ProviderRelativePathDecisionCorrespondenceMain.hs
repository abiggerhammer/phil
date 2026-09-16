module Main (main) where

import qualified ProviderRelativePathKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  let clean = facts False False False
      empty = facts True True True
      dot = facts False True True
      parent = facts False False True
      checks =
        [ ("empty occurrence rejects",
            isOccurrenceEmpty
              (Kernel.decideFileSystemOccurrenceByFacts True))
        , ("nonempty occurrence accepts",
            isOccurrenceAccepted
              (Kernel.decideFileSystemOccurrenceByFacts False))
        , ("empty raw path dominates slash and segments",
            isPathEmpty
              (Kernel.decideProviderRelativePathByFacts
                True True (list [empty])))
        , ("source slash dominates segment rejection",
            isAbsolute
              (Kernel.decideProviderRelativePathByFacts
                False True (list [empty])))
        , ("empty segment dominates dot and parent",
            isEmptySegmentAt 1
              (Kernel.decideProviderRelativeSegmentAt
                (nat 1) empty))
        , ("dot segment dominates parent",
            isDotSegmentAt 1
              (Kernel.decideProviderRelativeSegmentAt
                (nat 1) dot))
        , ("parent segment rejects after nonempty nondot",
            isParentSegmentAt 1
              (Kernel.decideProviderRelativeSegmentAt
                (nat 1) parent))
        , ("clean prefix advances and preserves later rejection index",
            isParentSegmentAt 2
              (Kernel.decideProviderRelativePathByFacts
                False False (list [clean, parent, empty])))
        , ("all clean segments accept",
            isPathAccepted
              (Kernel.decideProviderRelativePathByFacts
                False False (list [clean, clean, clean])))
        ]
  mapM_ report checks
  if all snd checks then pure () else exitFailure
  where
    report (label, True) = putStrLn ("PASS: IO-PATH kernel " <> label)
    report (label, False) = putStrLn ("FAIL: IO-PATH kernel " <> label)

facts :: Bool -> Bool -> Bool -> Kernel.ProviderRelativeSegmentFacts
facts = Kernel.MkProviderRelativeSegmentFacts

list :: [a] -> Kernel.List a
list = foldr Kernel.Cons Kernel.Nil

nat :: Int -> Kernel.Nat
nat value
  | value <= 0 = Kernel.O
  | otherwise = Kernel.S (nat (value - 1))

natToInt :: Kernel.Nat -> Int
natToInt value =
  case value of
    Kernel.O -> 0
    Kernel.S predecessor -> 1 + natToInt predecessor

isOccurrenceAccepted :: Kernel.FileSystemOccurrenceDecision -> Bool
isOccurrenceAccepted decision =
  case decision of
    Kernel.FileSystemOccurrenceAccepted -> True
    Kernel.FileSystemOccurrenceEmpty -> False

isOccurrenceEmpty :: Kernel.FileSystemOccurrenceDecision -> Bool
isOccurrenceEmpty decision =
  case decision of
    Kernel.FileSystemOccurrenceAccepted -> False
    Kernel.FileSystemOccurrenceEmpty -> True

isPathAccepted :: Kernel.ProviderRelativePathDecision -> Bool
isPathAccepted decision =
  case decision of
    Kernel.ProviderRelativePathAccepted -> True
    _ -> False

isPathEmpty :: Kernel.ProviderRelativePathDecision -> Bool
isPathEmpty decision =
  case decision of
    Kernel.ProviderRelativePathEmpty -> True
    _ -> False

isAbsolute :: Kernel.ProviderRelativePathDecision -> Bool
isAbsolute decision =
  case decision of
    Kernel.ProviderRelativePathAbsolute -> True
    _ -> False

isEmptySegmentAt :: Int -> Kernel.ProviderRelativePathDecision -> Bool
isEmptySegmentAt expected decision =
  case decision of
    Kernel.ProviderRelativePathEmptySegment index -> natToInt index == expected
    _ -> False

isDotSegmentAt :: Int -> Kernel.ProviderRelativePathDecision -> Bool
isDotSegmentAt expected decision =
  case decision of
    Kernel.ProviderRelativePathDotSegment index -> natToInt index == expected
    _ -> False

isParentSegmentAt :: Int -> Kernel.ProviderRelativePathDecision -> Bool
isParentSegmentAt expected decision =
  case decision of
    Kernel.ProviderRelativePathParentSegment index -> natToInt index == expected
    _ -> False
