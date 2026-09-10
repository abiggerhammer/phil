{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCorePolicy (sourceCoreCallSites)
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.Static (DeclarationKey (..))
import Phil.Examples.Steve.ApplicationShell
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  )
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , InstanceLineageSiteId (..)
  , PortableInstanceLineage (..)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  putSource <- TextIO.readFile "examples/steve/put-cli.phil"
  getSource <- TextIO.readFile "examples/steve/get-cli.phil"
  let checks =
        [ ("Phil-side Steve put/get shells pass the ordinary source path",
            ordinaryShellChecks putSource getSource)
        , ("shell call inventory contains IO and CAS operations in Phil source",
            shellCallInventory putSource getSource)
        , ("console and filesystem spellings retain exact IO provider identity",
            ioBindingsAreExact)
        , ("retrieved linear bytes must be released on every terminal path",
            unreleasedGetRejects putSource getSource)
        ]
  results <- mapM report checks
  if and results then pure () else exitFailure

report :: (String, Either String ()) -> IO Bool
report (label, result) = case result of
  Right () -> putStrLn ("PASS: INT-006 " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: INT-006 " <> label <> " -- " <> detail) >> pure False

ordinaryShellChecks :: Text.Text -> Text.Text -> Either String ()
ordinaryShellChecks putSource getSource = do
  checked <- checkedShell putSource getSource
  assert (length (checkedSourceUnits checked) == 2)
    "checked SourceBundle did not retain both shell source units"

shellCallInventory :: Text.Text -> Text.Text -> Either String ()
shellCallInventory putSource getSource = do
  checked <- checkedShell putSource getSource
  architecture <- mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:steve-shell" (InstanceLineageSiteId "instance.steve-shell"))
    checked
  let actual = List.sort (Map.elems (sourceCoreCallSites architecture))
      expected = List.sort
        [ "console_read_line"
        , "path_parse"
        , "fs_read"
        , "digest_compute"
        , "blob_install"
        , "content_id_render"
        , "console_write"
        , "content_id_render"
        , "console_write"
        , "console_read_line"
        , "content_id_parse"
        , "console_read_line"
        , "path_parse"
        , "blob_read"
        , "digest_check"
        , "fs_replace"
        ]
  assert (actual == expected)
    ("shell call inventory drifted: " <> show actual)

ioBindingsAreExact :: Either String ()
ioBindingsAreExact = do
  bindings <- mapLeft Text.unpack steveShellIOBindings
  stdinRead <- need "console_read_line" bindings
  stdoutWrite <- need "console_write" bindings
  fsRead <- need "fs_read" bindings
  fsReplace <- need "fs_replace" bindings
  assert (steveShellProviderOccurrence stdinRead == "standard.stdin")
    "console_read_line lost standard.stdin occurrence identity"
  assert (steveShellProviderOperation stdinRead == "read_line")
    "console_read_line operation identity drifted"
  assert (steveShellProviderOccurrence stdoutWrite == "standard.stdout")
    "console_write lost standard.stdout occurrence identity"
  assert (steveShellProviderOperation stdoutWrite == "write")
    "console_write operation identity drifted"
  assert (steveShellProviderOccurrence fsRead == "steve.user.fs"
       && steveShellProviderOccurrence fsReplace == "steve.user.fs")
    "filesystem operations are not tied to the same explicit occurrence"
  assert (steveShellProviderOperation fsRead == "read"
       && steveShellProviderOperation fsReplace == "replace")
    "filesystem operation identity drifted"
  let effects = map (unSemanticEffect . steveShellProviderEffect)
        [stdinRead, stdoutWrite, fsRead, fsReplace]
  assert (length (List.nub effects) == 4)
    "subject/operation-indexed IO effects collapsed"

unreleasedGetRejects :: Text.Text -> Text.Text -> Either String ()
unreleasedGetRejects putSource getSource = do
  let brokenGet = Text.replace "release bytes; " "" getSource
  putEnvironment <- mapLeft Text.unpack stevePutShellEnvironment
  getEnvironment <- mapLeft Text.unpack steveGetShellEnvironment
  let environments = Map.fromList
        [ (putDeclaration, putEnvironment)
        , (getDeclaration, getEnvironment)
        ]
  case checkPortableSourceBundle shellRoots environments (shellBundle putSource brokenGet) of
    Left (SourceBundleSurfaceCheckError _ _ SurfaceCheckError
      { surfaceErrorClass = LinearCompletion }) -> Right ()
    other -> Left ("unreleased retrieved bytes did not fail LinearCompletion: " <> show other)

checkedShell :: Text.Text -> Text.Text -> Either String CheckedSourceBundle
checkedShell putSource getSource = do
  putEnvironment <- mapLeft Text.unpack stevePutShellEnvironment
  getEnvironment <- mapLeft Text.unpack steveGetShellEnvironment
  mapLeft show $ checkPortableSourceBundle
    shellRoots
    (Map.fromList
      [ (putDeclaration, putEnvironment)
      , (getDeclaration, getEnvironment)
      ])
    (shellBundle putSource getSource)

shellBundle :: Text.Text -> Text.Text -> PortableSourceBundle
shellBundle putSource getSource = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:steve-shell"
  , portableSourceUnits =
      [ PortableSourceUnit
          (SourceUnitId "unit.steve.put-cli")
          (DeclarationSiteId "site.steve.put-cli")
          (Just "decl:steve.put-cli")
          putSource
      , PortableSourceUnit
          (SourceUnitId "unit.steve.get-cli")
          (DeclarationSiteId "site.steve.get-cli")
          (Just "decl:steve.get-cli")
          getSource
      ]
  , portableInstanceLineage =
      [ PortableInstanceLineage
          (InstanceLineageSiteId "instance.steve-shell")
          "inst:phase1.steve-shell"
      ]
  , portableProcessLineage = []
  }

shellRoots :: SourceRootMap
shellRoots = Map.singleton "program:steve-shell" putDeclaration

putDeclaration, getDeclaration :: DeclarationKey
putDeclaration = DeclarationKey "decl:steve.put-cli"
getDeclaration = DeclarationKey "decl:steve.get-cli"

need
  :: Text.Text
  -> Map.Map Text.Text SteveShellIOBinding
  -> Either String SteveShellIOBinding
need name bindings = maybe
  (Left ("missing shell IO binding: " <> Text.unpack name))
  Right
  (Map.lookup name bindings)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
