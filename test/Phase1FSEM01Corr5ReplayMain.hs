{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 CORR-5: actual Grammar-v1 checker-derived Linear source transcript,
-- bound to UTF-8 source SHA256, exact resolved binders, native Core transitions.
-- The independent Rocq decoder/replayer is a separate CI consumer.
module Main (main) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as ByteString
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Encoding
import qualified Data.Text.IO as TextIO
import Numeric (showHex)
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import qualified Phil.Core.Context as Core
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..)
  , SourceBoolJoinInvariant (..), SourceLinearLoopRun (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceLinearLoopTransfer
  ( GrammarV1LinearLoopTrace (..)
  , grammarV1CheckedLinearLoopTransferTrace )
import Phil.Surface.Syntax (Located (..))
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import Text.Read (readMaybe)

data Specimen = Specimen
  { specName :: String
  , specSource :: FilePath
  , specKind :: Text
  , specExpected :: Text
  } deriving (Eq,Show)

root :: Text
root = "decl.fsem01.l2.cycle"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

cases :: [Specimen]
cases =
  [ specimen "accepted-owner" "OK" "DONE"
  , specimen "accepted-same-width-spectator" "OK" "DONE"
  , specimen "stale-original-owner" "ST" "MISSING"
  , specimen "duplicate-live-header-owner" "DU" "DUPLICATE"
  , specimen "unproved-invariant" "GA" "GATED"
  , Specimen "accepted-closed"
      "test/fixtures/fsem01-scoped-linear-loop-loan-v1/accepted-closed.phil"
      "OK" "DONE"
  , Specimen "live-loan-refusal"
      "test/fixtures/fsem01-scoped-linear-loop-loan-v1/accepted-closed.phil"
      "LO" "LOAN"
  ]
  where
    specimen name kind expected =
      Specimen name
        ("test/fixtures/fsem01-linear-loop-transfer-v1/" ++ name ++ ".phil")
        kind expected

data Trace = Trace
  { traceSourceSHA :: Text
  , traceRoot :: Text
  , traceFlag :: Text
  , traceOld :: Text
  , traceSlot :: Text
  , traceAlternate :: Text
  , traceKind :: Text
  , traceExpected :: Text
  } deriving (Eq,Show)

fields :: Trace -> [Text]
fields t =
  [ traceSourceSHA t, traceRoot t, traceFlag t, traceOld t
  , traceSlot t, traceAlternate t, traceKind t, traceExpected t ]

version :: Text
version = "PHIL-FSEM01-CORR5-V1|"

frame :: Text -> Text
frame field = Text.pack (show (Text.length field)) <> ":" <> field

encode :: Trace -> Text
encode = (version <>) . Text.concat . map frame . fields

decode :: Text -> Maybe [Text]
decode raw = do
  rest <- Text.stripPrefix version raw
  (items, suffix) <- go 8 rest
  if Text.null suffix && length items == 8 &&
       encodeFromFields items == raw
    then Just items else Nothing
  where
    encodeFromFields items = version <> Text.concat (map frame items)
    go 0 rest = Just ([],rest)
    go n rest = do
      let (digits,restWithColon) = Text.breakOn ":" rest
      lengthValue <- readMaybe (Text.unpack digits) :: Maybe Integer
      if lengthValue < 0 ||
         Text.pack (show lengthValue) /= digits
        then Nothing else do
          next <- Text.stripPrefix ":" restWithColon
          if lengthValue > toInteger (Text.length next)
            then Nothing else do
              let (field,suffix) = Text.splitAt (fromInteger lengthValue) next
              (items,tailText) <- go (n-1) suffix
              Just (field:items,tailText)

hashHex :: ByteString.ByteString -> Text
hashHex = Text.pack . concatMap byteHex . ByteString.unpack
  where
    byteHex n = let v = showHex n "" in if length v == 1 then '0':v else v

sourceHash :: Text -> Text
sourceHash = hashHex . SHA256.hash . Encoding.encodeUtf8

utf8Hex :: Text -> Text
utf8Hex = hashHex . Encoding.encodeUtf8

ownerName :: GrammarV1ResolvedBinder -> Name
ownerName = grammarV1ResolvedBinderCoreName

ownerHex :: GrammarV1ResolvedBinder -> Text
ownerHex = utf8Hex . unName . ownerName

check :: Bool -> String -> Either String ()
check condition message =
  if condition then Right () else Left message

required :: String -> Maybe a -> Either String a
required message = maybe (Left message) Right

native :: Show e => Either e a -> Either String a
native = either (Left . show) Right

cut :: BorrowTraceCheckpoint -> Core.ResourceContext
cut checkpoint = Core.ResourceContext
  (traceUnrestrictedOwners checkpoint) (traceAffineOwners checkpoint)
  (traceLinearOwners checkpoint) (traceActiveLoans checkpoint)

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne input = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-corr5" input)
  case grammarV1TopLevelDecls file of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("unexpected source declaration: " ++ show other)
    others -> Left ("expected one checked source function, got " ++
                    show (length others))

checkedSource :: Text -> Either String GrammarV1LinearLoopTrace
checkedSource source = do
  fn <- parseOne source
  case grammarV1CheckedLinearLoopTransferTrace
         emptyStaticContext (DeclarationKey root) fn of
    Just (Right trace) -> Right trace
    other -> Left ("source loop adapter not competent: " ++ show other)

-- Verify actual recorded checker cuts against independent Core operations.
-- Only after this is the source-derived transcript emitted.
checkTrace :: Specimen -> GrammarV1LinearLoopTrace -> Either String ()
checkTrace specimen trace = do
  let run = linearLoopNativeRun trace
      old = ownerName (linearLoopPayloadBinder trace)
      slot = ownerName (linearLoopHeaderBinder trace)
      flag = ownerName (linearLoopFlagBinder trace)
      maybeAlt = fmap ownerName (linearLoopAlternateBinder trace)
      kind = specKind specimen
  before <- required "no source entry context" (sourceLinearLoopBefore run)
  spent <- required "no source consumed-owner cut" (sourceLinearLoopEntryConsumed run)
  header <- required "no source loop header" (sourceLinearLoopHeaderBound run)
  let expectedInitial = Core.ResourceContext
        (Map.singleton flag TyBool) Map.empty
        (Map.fromList ((old,bytes8) :
          maybe [] (\alt -> [(alt,bytes8)]) maybeAlt))
        Set.empty
  check (before == expectedInitial && old /= slot &&
         sourceLinearLoopOutcome run == linearLoopCheckedOutcome trace)
    "source initial context/identity or checked outcome diverged"
  (movedTy,moved) <- native (Core.consumeLinear old before)
  check (movedTy == bytes8 && moved == spent) "source consumed-owner step differs"
  inserted <- native (Core.insertBinding Linear slot bytes8 spent)
  check (inserted == header && Map.notMember old (Core.linearBindings header))
    "source header rebind/old owner differs"

  case kind of
    "OK" -> do
      check (linearLoopInvariantProof trace == SourceBoolInvariantProvenTrue &&
             ownerName (linearLoopBackedgeBinder trace) == slot)
        "source ordinary backedge not selected"
      (reboundTy,backSpent) <- native (Core.consumeLinear slot header)
      rebound <- native (Core.insertBinding Linear slot reboundTy backSpent)
      check (reboundTy == bytes8 &&
             sourceLinearLoopBackedgeConsumed run == Just backSpent &&
             sourceLinearLoopBackedgeRebound run == Just rebound &&
             sourceLinearLoopReentered run == Just header &&
             Core.joinContinuing [header,rebound] == Right header &&
             sourceLinearLoopOutcome run == Right ())
        "source continuing backedge/reentry differs"
      case sourceLinearLoopLoanCuts run of
        [] -> Right ()
        [beforeLoan, started, bodyResult, closed] -> do
          check (map tracePhase [beforeLoan,started,bodyResult,closed] ==
                 [TraceBeforeLoan, TraceLoanStarted,
                  TraceBodyResult False, TraceLoanClosed])
            "source loan event phases differ"
          loaned <- native (Core.startSharedLoan slot header)
          check (map cut [beforeLoan,started,bodyResult,closed] ==
                   [header,loaned,loaned,header])
            "source scoped loan did not close before backedge"
        _ -> Left "unsupported source loan transition shape"
    "ST" -> do
      check (maybeAlt == Nothing && ownerName (linearLoopBackedgeBinder trace) == old &&
             Core.consumeLinear old header == Left (Core.UnknownBinding old) &&
             sourceLinearLoopBackedgeConsumed run == Nothing &&
             sourceLinearLoopBackedgeRebound run == Nothing &&
             sourceLinearLoopReentered run == Nothing &&
             case sourceLinearLoopOutcome run of
               Left err -> surfaceErrorClass err == StructuralUse
               _ -> False)
        "source stale original does not fail at expected prefix"
    "DU" -> do
      alt <- required "duplicate case lacks independent actual" maybeAlt
      check (ownerName (linearLoopBackedgeBinder trace) == alt)
        "duplicate case changed source actual"
      (consumedTy,backSpent) <- native (Core.consumeLinear alt header)
      check (consumedTy == bytes8 &&
             sourceLinearLoopBackedgeConsumed run == Just backSpent &&
             Core.insertBinding Linear slot bytes8 backSpent ==
               Left (Core.DuplicateBinding slot) &&
             sourceLinearLoopBackedgeRebound run == Nothing &&
             sourceLinearLoopReentered run == Nothing &&
             case sourceLinearLoopOutcome run of
               Left err -> surfaceErrorClass err == StructuralUse
               _ -> False)
        "source competing owner did not fail at duplicate rebind"
    "GA" ->
      check (maybeAlt == Nothing &&
             linearLoopInvariantProof trace == SourceBoolInvariantUnproved &&
             sourceLinearLoopBackedgeConsumed run == Nothing &&
             sourceLinearLoopBackedgeRebound run == Nothing &&
             sourceLinearLoopReentered run == Nothing &&
             case sourceLinearLoopOutcome run of
               Left err -> surfaceErrorClass err == MissingEvidence
               _ -> False)
        "unproved invariant fabricated a resource step"
    "LO" -> do
      check (maybeAlt == Nothing && sourceLinearLoopOutcome run == Right ())
        "source live-loan control was not admitted"
      case sourceLinearLoopLoanCuts run of
        [beforeLoan, started, bodyResult, closed] -> do
          loaned <- native (Core.startSharedLoan slot header)
          check (map tracePhase [beforeLoan,started,bodyResult,closed] ==
                 [TraceBeforeLoan, TraceLoanStarted,
                  TraceBodyResult False, TraceLoanClosed] &&
                 map cut [beforeLoan,started,bodyResult,closed] ==
                   [header,loaned,loaned,header] &&
                 Core.consumeLinear slot loaned == Left (Core.OwnerBorrowed slot))
            "source live-loan prefix did not forbid move"
        _ -> Left "no genuine source borrow prefix"
    _ -> Left "unknown source replay case"

mkTrace :: Specimen -> Text -> GrammarV1LinearLoopTrace -> Trace
mkTrace specimen source trace = Trace
  { traceSourceSHA = sourceHash source
  , traceRoot = utf8Hex root
  , traceFlag = ownerHex (linearLoopFlagBinder trace)
  , traceOld = ownerHex (linearLoopPayloadBinder trace)
  , traceSlot = ownerHex (linearLoopHeaderBinder trace)
  , traceAlternate = maybe "-"
      ownerHex (linearLoopAlternateBinder trace)
  , traceKind = specKind specimen
  , traceExpected = specExpected specimen
  }

mustReject :: String -> Maybe a -> Either String ()
mustReject label candidate =
  check (case candidate of Nothing -> True; Just _ -> False)
    ("accepted forged source trace wire: " ++ label)

checkWireControls :: Trace -> Either String ()
checkWireControls trace = do
  let text = encode trace
      invalid = trace { traceSourceSHA = Text.replicate 64 "0" }
      noncanonical = Text.replace
        (Text.pack (show (Text.length (traceRoot trace))) <> ":")
        ("0" <> Text.pack (show (Text.length (traceRoot trace))) <> ":")
        text
  check (decode text == Just (fields trace))
    "canonical emitted trace does not round-trip"
  mustReject "incorrect length framing" (decode noncanonical)
  mustReject "trailing bytes" (decode (text <> "junk"))
  mustReject "wrong version"
    (decode (Text.replace version "PHIL-FSEM01-CORR5-V2|" text))
  check (fields invalid /= fields trace)
    "digest mutation should differ from source fingerprint"
  check (specExpectedCase trace) "artifact case is not self-consistent"
  where
    specExpectedCase record =
      case traceKind record of
        "OK" -> traceExpected record == "DONE"
        "ST" -> traceExpected record == "MISSING" &&
                traceAlternate record == "-"
        "DU" -> traceExpected record == "DUPLICATE" &&
                traceAlternate record /= "-"
        "GA" -> traceExpected record == "GATED" &&
                traceAlternate record == "-"
        "LO" -> traceExpected record == "LOAN" &&
                traceAlternate record == "-"
        _ -> False

main :: IO ()
main = do
  args <- getArgs
  let destination = case args of
        [] -> Nothing
        ["--emit", directory] -> Just directory
        _ -> Nothing
  if args /= [] && destination == Nothing
    then putStrLn "usage: Phase1FSEM01Corr5ReplayMain [--emit DIR]" >> exitFailure
    else do
      rows <- mapM (\specimen -> do
          source <- TextIO.readFile (specSource specimen)
          pure (specimen,source)) cases
      let result = mapM (\(specimen,source) -> do
            trace <- checkedSource source
            checkTrace specimen trace
            let artifact = mkTrace specimen source trace
            checkWireControls artifact
            pure (specName specimen,encode artifact)) rows
      case result of
        Left err -> putStrLn ("FAIL CORR-5: " ++ err) >> exitFailure
        Right generated -> do
          case destination of
            Nothing -> pure ()
            Just directory -> do
              createDirectoryIfMissing True directory
              mapM_ (\(name,wire) ->
                TextIO.writeFile (directory </> name ++ ".trace") wire) generated
          putStrLn "PASS CORR-5: seven source-derived exact-resource transcripts, checked outcomes and strict wire refusal"
