{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 REC-01: original Grammar-v1 record declarations and patterns
-- checked against actual Core.DataDestruction native operations.
-- This is NOT an executable production Surface record-pattern adapter.
module Main (main) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.DataDestruction
  ( DataDestructionError (..), FieldDisposition (..), OwnedField (..)
  , checkFieldDispositions )
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.SourceRecordFieldDisposition
  ( GrammarV1RecordDispositionError (..)
  , GrammarV1RecordDispositionTrace (..)
  , GrammarV1RecordFieldTransfer (..)
  , grammarV1CheckedSourceRecordDisposition )
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.rec01.unpack"

fixturePath :: String -> FilePath
fixturePath name = "test/fixtures/fsem01-rec01-source-record-v1/" ++ name ++ ".phil"

parse :: Text -> Either String (Maybe (Either GrammarV1RecordDispositionError GrammarV1RecordDispositionTrace))
parse input = do
  original <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-rec01-original-source" input)
  Right (grammarV1CheckedSourceRecordDisposition emptyStaticContext root original)

ensure :: Bool -> String -> Either String ()
ensure p message = if p then Right () else Left message

accepted :: Text -> Either String GrammarV1RecordDispositionTrace
accepted input = do
  outcome <- parse input
  case outcome of
    Just (Right trace) -> Right trace
    other -> Left ("source record was not accepted by REC-01: " ++ show other)

checkNative :: [Text] -> [Text] -> Integer -> GrammarV1RecordDispositionTrace
  -> Either String ()
checkNative declaredLabels selectedLabels width trace = do
  let sourceFields = recordDispositionFields trace
      schema =
        [ OwnedField (Name (recordTransferLabel field))
            (recordTransferMode field) (recordTransferType field)
        | field <- sourceFields ]
      selected =
        [ (Name (recordTransferLabel field),FieldBound)
        | field <- sourceFields
        , case recordTransferDestination field of
            Just _ -> True
            Nothing -> False ]
      selectedActual =
        [ recordTransferLabel field
        | field <- sourceFields
        , case recordTransferDestination field of
            Just _ -> True
            Nothing -> False ]
      owner = grammarV1ResolvedBinderCoreName (recordDispositionOwner trace)
      payload = grammarV1ResolvedBinderCoreName
        (recordDispositionReturnedBinder trace)
      payloadTy = TyBytes (RefNat width)
  ensure
    (recordDispositionDeclarationKey trace == root &&
     recordDispositionRecordName trace == "Packet" &&
     recordDispositionStructuralMode trace == Linear &&
     map recordTransferLabel sourceFields == declaredLabels &&
     selectedActual == selectedLabels &&
     recordDispositionReturnedType trace == payloadTy)
    "record source field order, mode, selected binders or checked Bytes type differs"
  either (Left . show) Right (checkFieldDispositions schema selected)
  initial <- either (Left . show) Right $
    Core.insertBinding Linear owner
      (recordDispositionOpaqueCarrier trace) Core.emptyContext
  ensure (initial == recordDispositionBefore trace)
    "actual native pre-consume record context is not source-derived"
  (mode,ty,afterOwner) <- either (Left . show) Right
    (Core.useBinding owner initial)
  ensure (mode == Linear && ty == recordDispositionOpaqueCarrier trace)
    "wrong native record owner/mode consumed"
  expected <- foldM restore afterOwner sourceFields
  ensure (expected == recordDispositionAfter trace &&
          Core.useBinding owner expected == Left (Core.UnknownBinding owner))
    "independent real Core insertion differs from DataDestruction or resurrected record"
  ensure (Core.linearBindings expected == Map.singleton payload payloadTy)
    "unexpected Linear resource leftover after checked record destructuring"
  (actual,afterReturn) <- either (Left . show) Right
    (Core.consumeLinear payload expected)
  ensure (actual == payloadTy &&
          afterReturn == recordDispositionTerminal trace &&
          Core.ensureComplete afterReturn == Right () &&
          Core.consumeLinear payload afterReturn == Left (Core.UnknownBinding payload))
    "original Bytes field did not complete exactly once"
  where
    restore ctx field = case recordTransferDestination field of
      Nothing -> Right ctx
      Just binder -> either (Left . show) Right $
        Core.insertBinding (recordTransferMode field)
          (grammarV1ResolvedBinderCoreName binder)
          (recordTransferType field) ctx

checkAccepted :: String -> [Text] -> [Text] -> Integer -> IO (Either String ())
checkAccepted fixture labels chosen width = do
  input <- TextIO.readFile (fixturePath fixture)
  pure (accepted input >>= checkNative labels chosen width)

checkDisposition :: String -> (DataDestructionError -> Bool) -> IO (Either String ())
checkDisposition fixture expected = do
  input <- TextIO.readFile (fixturePath fixture)
  pure $ do
    outcome <- parse input
    case outcome of
      Just (Left (SourceRecordDispositionError err)) ->
        ensure (expected err) ("wrong DataDestruction diagnostic: " ++ show err)
      other -> Left ("wrong native disposition class: " ++ fixture ++ " " ++ show other)

checkBinder :: String -> IO (Either String ())
checkBinder fixture = do
  input <- TextIO.readFile (fixturePath fixture)
  pure $ do
    outcome <- parse input
    case outcome of
      Just (Left (SourceRecordLetError _)) -> Right ()
      other -> Left ("missing duplicate/shadow lexical error: " ++ show other)

checkMismatch :: String -> String -> IO (Either String ())
checkMismatch fixture fragment = do
  input <- TextIO.readFile (fixturePath fixture)
  pure $ do
    outcome <- parse input
    case outcome of
      Just (Left (SourceRecordMismatch errorText)) ->
        ensure (Text.isInfixOf (Text.pack fragment) errorText)
          ("wrong source mismatch: " ++ show errorText)
      other -> Left ("wrong source mismatch class: " ++ fixture ++ " " ++ show other)

checkModeFailure :: IO (Either String ())
checkModeFailure = do
  input <- TextIO.readFile (fixturePath "weakened-record-mode")
  pure $ do
    outcome <- parse input
    case outcome of
      Just (Left (SourceRecordModeError _)) -> Right ()
      other -> Left ("record mode weakening evaded nominal checker: " ++ show other)

checkNoncompetence :: String -> IO (Either String ())
checkNoncompetence fixture = do
  input <- TextIO.readFile (fixturePath fixture)
  pure $ do
    outcome <- parse input
    ensure (outcome == Nothing)
      ("unsupported source classified as accepted/invalid: " ++ show outcome)

checkAlphaRoot :: IO (Either String ())
checkAlphaRoot = do
  input <- TextIO.readFile (fixturePath "accepted-alias")
  let renamed = foldl (\s (before,after) -> Text.replace before after s)
        input [("packet","bundle"),("metadata","label"),("owned","resource"),("ok","truth")]
  pure $ do
    first <- accepted input
    alpha <- accepted renamed
    ensure
      (grammarV1ResolvedBinderCoreName (recordDispositionOwner first) ==
         grammarV1ResolvedBinderCoreName (recordDispositionOwner alpha) &&
       map (fmap grammarV1ResolvedBinderCoreName . recordTransferDestination)
         (recordDispositionFields first) ==
       map (fmap grammarV1ResolvedBinderCoreName . recordTransferDestination)
         (recordDispositionFields alpha))
      "alpha-renaming changed stable declaration-rooted semantic owner identities"

main :: IO ()
main = do
  verified <- sequence
    [ checkAccepted "accepted-full" ["tag","payload","flag"] ["tag","payload","flag"] 8
    , checkAccepted "accepted-alias" ["tag","payload","flag"] ["tag","payload","flag"] 8
    , checkAccepted "accepted-omit" ["tag","payload","flag"] ["payload"] 8
    , checkAccepted "accepted-reordered" ["tag","payload","flag"] ["tag","payload","flag"] 8
    , checkAccepted "accepted-bytes16" ["flag","payload","tag"] ["flag","payload"] 16
    , checkDisposition "missing-linear" (\e -> case e of
        MissingLinearFieldDisposition (Name "payload") -> True
        _ -> False)
    , checkDisposition "unknown-field" (\e -> case e of
        UnknownFieldDisposition (Name "bogus") -> True
        _ -> False)
    , checkDisposition "duplicate-field" (\e -> case e of
        DuplicateFieldDisposition (Name "tag") -> True
        _ -> False)
    , checkDisposition "duplicate-decl-field" (\e -> case e of
        DuplicateOwnedField (Name "tag") -> True
        _ -> False)
    , checkBinder "duplicate-binder"
    , checkBinder "shadow-parameter"
    , checkMismatch "wrong-return" "returned original source binder"
    , checkMismatch "wrong-return-width" "declared return type"
    , checkModeFailure
    , checkNoncompetence "nested-field-pattern"
    , checkNoncompetence "wrong-named-type"
    , checkNoncompetence "extra-body"
    , checkNoncompetence "unknown-return"
    , checkNoncompetence "no-linear"
    , checkAlphaRoot
    ]
  case sequence verified of
    Left failure -> putStrLn ("FAIL FSEM-01 REC-01: " ++ failure) >> exitFailure
    Right _ -> putStrLn
      "PASS FSEM-01 REC-01: five checked record-source witnesses, native DataDestruction and independent Core Map/Set replay, mandatory Linear field and lexical negatives"
