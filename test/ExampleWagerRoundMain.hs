{-# LANGUAGE OverloadedStrings #-}

-- Checks examples/wager/round.phil with the Grammar-v1 front end, and checks
-- that four single-point edits to it are each refused with one exact error.
-- Non-normative: an example's evidence, not a semantic slice.

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.NominalDataMode (NominalModeError (..))
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..))
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolBinderScope (grammarV1CheckedProtocolBinderScope)
import Phil.Surface.GrammarV1.ProtocolRoles (GrammarV1ProtocolRoleError (..))
import Phil.Surface.GrammarV1.RecordFields
  ( GrammarV1CheckedRecordMode (..)
  , GrammarV1CheckedRecordModeError (..)
  , grammarV1CheckedClosedRecordMode
  )
import Phil.Surface.GrammarV1.ReferenceAstWholeSource (grammarV1ProductionSourceCore)
import Phil.Surface.GrammarV1.SemanticProtocolRoles
  ( GrammarV1CheckedSemanticProtocolRoleError (..)
  , grammarV1CheckedSemanticProtocolRoleTemplates
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

examplePath :: FilePath
examplePath = "examples/wager/round.phil"

main :: IO ()
main = do
  source <- TextIO.readFile examplePath
  results <- sequence
    [ test "the example parses and its whole-source reference core builds"
        (wholeSource source)
    , test "Move is linear"
        (moveMode source)
    , test "WagerRound passes binder scope"
        (binderScope source)
    , test "WagerRound's Player and Program roles are dual"
        (dual source)
    , test "a Program that drops one round result is non-dual"
        (nonDual source "          Held => continue Round |\n" "")
    , test "a Program that reads a 16-byte nonce is non-dual"
        (nonDual source "receive (reveal : (U8, Bytes[32]))" "receive (reveal : (U8, Bytes[16]))")
    , test "a Program whose BothCommitted carries the other side's pull is non-dual"
        (nonDual source "      BothCommitted =>\n        receive" "      BothCommitted(theirPull : U8) =>\n        receive")
    , test "Move declared affine weakens its derived linear mode"
        (affineMove source)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

wholeSource :: Text.Text -> Either String ()
wholeSource source = do
  file <- parsed source
  either (Left . show) (const (Right ())) (grammarV1ProductionSourceCore file)

moveMode :: Text.Text -> Either String ()
moveMode source = do
  record <- onlyRecord source
  case grammarV1CheckedClosedRecordMode emptyStaticContext Nothing record of
    Just (Right checked)
      | checkedRecordStructuralMode checked == Linear -> Right ()
    other -> Left ("expected a linear Move, got " <> show other)

binderScope :: Text.Text -> Either String ()
binderScope source = do
  protocol <- onlyProtocol source
  case grammarV1CheckedProtocolBinderScope declarationKey protocol of
    Just (Right _) -> Right ()
    other -> Left ("expected checked binder scope, got " <> show other)

dual :: Text.Text -> Either String ()
dual source = do
  protocol <- onlyProtocol source
  case grammarV1CheckedSemanticProtocolRoleTemplates emptyStaticContext declarationKey protocol of
    Just (Right _) -> Right ()
    other -> Left ("expected dual semantic roles, got " <> show other)

nonDual :: Text.Text -> Text.Text -> Text.Text -> Either String ()
nonDual source needle replacement = do
  edited <- programEdit source needle replacement
  protocol <- onlyProtocol edited
  case grammarV1CheckedSemanticProtocolRoleTemplates emptyStaticContext declarationKey protocol of
    Just
      (Left
        (GrammarV1CheckedSemanticProtocolRoleSemanticError
          (NonDualProtocolRoles (ProtocolRoleKey "Player") (ProtocolRoleKey "Program")))) ->
      Right ()
    other -> Left ("expected exactly NonDualProtocolRoles Player Program, got " <> show other)

affineMove :: Text.Text -> Either String ()
affineMove source = do
  edited <- exactlyOnce source "record Move mode linear" "record Move mode affine"
  record <- onlyRecord edited
  case grammarV1CheckedClosedRecordMode emptyStaticContext Nothing record of
    Just (Left (GrammarV1RecordModeNominalError (DeclaredModeWeakensDerived Linear Affine))) ->
      Right ()
    other -> Left ("expected exactly DeclaredModeWeakensDerived Linear Affine, got " <> show other)

-- Edits only the Program role, so the Player role stays as written.
programEdit :: Text.Text -> Text.Text -> Text.Text -> Either String Text.Text
programEdit source needle replacement = do
  let (before, after) = Text.breakOn "role Program" source
  if Text.null after
    then Left "the example has no Program role"
    else (before <>) <$> exactlyOnce after needle replacement

exactlyOnce :: Text.Text -> Text.Text -> Text.Text -> Either String Text.Text
exactlyOnce source needle replacement
  | Text.count needle source == 1 = Right (Text.replace needle replacement source)
  | otherwise = Left ("expected one occurrence of " <> show needle)

declarationKey :: DeclarationKey
declarationKey = DeclarationKey "decl.WagerRound"

parsed :: Text.Text -> Either String GrammarV1SourceFile
parsed source = either (Left . show) Right (parseGrammarV1StructuralSource (Text.pack examplePath) source)

declarations :: Text.Text -> Either String [GrammarV1Declaration]
declarations source =
  map (locatedValue . grammarV1Declaration . locatedValue) . grammarV1TopLevelDecls <$> parsed source

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  decls <- declarations source
  case [protocol | GrammarV1ProtocolDeclaration protocol <- decls] of
    [protocol] -> Right protocol
    protocols -> Left ("expected one protocol, got " <> show (length protocols))

onlyRecord :: Text.Text -> Either String GrammarV1RecordDecl
onlyRecord source = do
  decls <- declarations source
  case [record | GrammarV1RecordDeclaration record <- decls] of
    [record] -> Right record
    records -> Left ("expected one record, got " <> show (length records))
