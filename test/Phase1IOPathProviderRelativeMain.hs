{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Systems
  ( ProviderRelativePathError (..)
  , checkProviderRelativePath
  , fileSystemOccurrence
  , providerRelativePathOccurrence
  , providerRelativePathSegments
  , renderProviderRelativePath
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("accepts canonical provider-relative paths", acceptsCanonicalPath)
        , ("rejects absolute source roots", rejectsAbsolutePath)
        , ("rejects empty path and empty segments", rejectsEmptyForms)
        , ("rejects dot and parent traversal segments", rejectsTraversal)
        , ("same spelling in different FileSystem occurrences is distinct", namespacesAreIdentityBearing)
        , ("host backslash is data, not a source separator", hostSeparatorIsData)
        , ("host drive spelling does not create a source absolute path", hostDriveSpellingIsData)
        , ("Unicode scalar content round-trips without normalization", unicodeContentIsExact)
        , ("empty FileSystem occurrence fails closed", rejectsEmptyOccurrence)
        ]
  mapM_ report checks
  if all (either (const False) (const True) . snd) checks
    then pure ()
    else exitFailure
  where
    report (label, Right ()) = putStrLn ("PASS: IO-PATH-001 " <> label)
    report (label, Left detail) = putStrLn ("FAIL: IO-PATH-001 " <> label <> " -- " <> detail)

acceptsCanonicalPath :: Either String ()
acceptsCanonicalPath = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  path <- mapLeft show (checkProviderRelativePath occurrence "reports/2026/final.bin")
  assert
    (providerRelativePathSegments path == ["reports", "2026", "final.bin"])
    "canonical segments changed"
  assert
    (renderProviderRelativePath path == "reports/2026/final.bin")
    "canonical rendering changed"
  assert
    (providerRelativePathOccurrence path == occurrence)
    "provider occurrence was not retained"

rejectsAbsolutePath :: Either String ()
rejectsAbsolutePath = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  case checkProviderRelativePath occurrence "/etc/passwd" of
    Left (AbsoluteProviderRelativePath raw) ->
      assert (raw == "/etc/passwd") "absolute rejection lost exact source text"
    other -> Left ("absolute path was not rejected: " <> show other)

rejectsEmptyForms :: Either String ()
rejectsEmptyForms = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  case checkProviderRelativePath occurrence "" of
    Left EmptyProviderRelativePath -> Right ()
    other -> Left ("empty path was not rejected: " <> show other)
  case checkProviderRelativePath occurrence "reports//final.bin" of
    Left (EmptyProviderRelativePathSegment 2) -> Right ()
    other -> Left ("internal empty segment was not rejected: " <> show other)
  case checkProviderRelativePath occurrence "reports/" of
    Left (EmptyProviderRelativePathSegment 2) -> Right ()
    other -> Left ("trailing empty segment was not rejected: " <> show other)

rejectsTraversal :: Either String ()
rejectsTraversal = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  case checkProviderRelativePath occurrence "./report" of
    Left (DotProviderRelativePathSegment 1) -> Right ()
    other -> Left ("dot segment was not rejected: " <> show other)
  case checkProviderRelativePath occurrence "reports/../secret" of
    Left (ParentProviderRelativePathSegment 2) -> Right ()
    other -> Left ("parent segment was not rejected: " <> show other)

namespacesAreIdentityBearing :: Either String ()
namespacesAreIdentityBearing = do
  leftOccurrence <- mapLeft show (fileSystemOccurrence "filesystem.left")
  rightOccurrence <- mapLeft show (fileSystemOccurrence "filesystem.right")
  leftPath <- mapLeft show (checkProviderRelativePath leftOccurrence "shared/data.bin")
  rightPath <- mapLeft show (checkProviderRelativePath rightOccurrence "shared/data.bin")
  assert (leftPath /= rightPath)
    "cross-namespace paths collapsed to one semantic identity"

hostSeparatorIsData :: Either String ()
hostSeparatorIsData = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  path <- mapLeft show (checkProviderRelativePath occurrence "folder\\child")
  assert
    (providerRelativePathSegments path == ["folder\\child"])
    "host backslash was interpreted as a source separator"
  assert
    (renderProviderRelativePath path == "folder\\child")
    "host backslash content did not round-trip exactly"

hostDriveSpellingIsData :: Either String ()
hostDriveSpellingIsData = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  path <- mapLeft show (checkProviderRelativePath occurrence "C:\\temp")
  assert
    (providerRelativePathSegments path == ["C:\\temp"])
    "host drive spelling acquired ambient absolute-path meaning"

unicodeContentIsExact :: Either String ()
unicodeContentIsExact = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  let composed = Text.pack ['c', 'a', 'f', '\x00e9']
      decomposed = Text.pack ['c', 'a', 'f', 'e', '\x0301']
  composedPath <- mapLeft show (checkProviderRelativePath occurrence composed)
  decomposedPath <- mapLeft show (checkProviderRelativePath occurrence decomposed)
  assert (renderProviderRelativePath composedPath == composed)
    "composed Unicode path text changed"
  assert (renderProviderRelativePath decomposedPath == decomposed)
    "decomposed Unicode path text changed"
  assert (composedPath /= decomposedPath)
    "distinct Unicode scalar sequences were implicitly normalized"

rejectsEmptyOccurrence :: Either String ()
rejectsEmptyOccurrence =
  case fileSystemOccurrence "" of
    Left EmptyFileSystemOccurrence -> Right ()
    other -> Left ("empty FileSystem occurrence was accepted: " <> show other)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
