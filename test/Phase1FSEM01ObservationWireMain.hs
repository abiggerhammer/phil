{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Char (isAsciiLower, isDigit)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import qualified Data.Text.IO as TextIO
import Numeric (showHex)
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (Return), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine (BorrowTraceCheckpoint (..), BorrowTracePhase (..))
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1DecodeBinderCoreName
  )
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..)
  , GrammarV1BorrowResourceTrace (..)
  , grammarV1CheckedBorrowResourceFunction
  , grammarV1CheckedBorrowResourceFunctionTrace
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Read (readMaybe)

-- ASCII v1 wire, not JSON: literal version and 8 consecutive length-framed
-- fields. UTF-8 source/root/Core-name bytes are hashed/hex-encoded before
-- framing. All production values come from the real checker or real source.
version :: Text
version = "PHIL-FSEM01-OBS-V1|"

data Observation = Observation
  { obsSourceSHA256 :: Text
  , obsRootHex :: Text
  , obsOwnerHex :: Text
  , obsViewHex :: Text
  , obsOwnerOrdinal :: Text
  , obsViewOrdinal :: Text
  , obsTrace :: Text
  , obsOutcome :: Text
  }
  deriving (Eq, Show)

observationFields :: Observation -> [Text]
observationFields a =
  [ obsSourceSHA256 a, obsRootHex a, obsOwnerHex a, obsViewHex a
  , obsOwnerOrdinal a, obsViewOrdinal a, obsTrace a, obsOutcome a ]

toObservation :: [Text] -> Maybe Observation
toObservation [digest, root, owner, view, ownerOrd, viewOrd, trace, outcome] =
  Just Observation
    { obsSourceSHA256 = digest, obsRootHex = root
    , obsOwnerHex = owner, obsViewHex = view
    , obsOwnerOrdinal = ownerOrd, obsViewOrdinal = viewOrd
    , obsTrace = trace, obsOutcome = outcome }
toObservation _ = Nothing

frame :: Text -> Text
frame field = Text.pack (show (Text.length field)) <> ":" <> field

encodeObservation :: Observation -> Text
encodeObservation = (version <>) . Text.concat . map frame . observationFields

readCanonicalNat :: Text -> Maybe Integer
readCanonicalNat value
  | Text.null value = Nothing
  | not (Text.all (\c -> c >= '0' && c <= '9') value) = Nothing
  | otherwise = do
      n <- readMaybe (Text.unpack value)
      if n >= 0 && Text.pack (show (n :: Integer)) == value
        then Just n else Nothing

parseFrame :: Text -> Maybe (Text, Text)
parseFrame raw = do
  let (token, afterToken) = Text.breakOn ":" raw
  declaredLength <- readCanonicalNat token
  rest <- Text.stripPrefix ":" afterToken
  if declaredLength > toInteger (Text.length rest)
    then Nothing else do
      let (field, suffix) = Text.splitAt (fromInteger declaredLength) rest
      Just (field, suffix)

parseFrames :: Int -> Text -> Maybe ([Text], Text)
parseFrames 0 raw = Just ([], raw)
parseFrames n raw
  | n < 0 = Nothing
  | otherwise = do
      (field, remaining) <- parseFrame raw
      (other, suffix) <- parseFrames (n - 1) remaining
      Just (field : other, suffix)

isLowerHex :: Text -> Bool
isLowerHex = Text.all (\c -> (c >= '0' && c <= '9') ||
                             (isAsciiLower c && c <= 'f'))

canonicalHex :: Text -> Bool
canonicalHex s = even (Text.length s) && isLowerHex s

positiveCuts, escapeCuts, positiveOutcome, escapeOutcome :: Text
positiveCuts = "B10,S11,N11,C10,R00"
escapeCuts = "B10,S11,E11,X11"
positiveOutcome = "OK:Bytes8"
escapeOutcome = "ERR:BorrowEscape:shared view escapes its lexical scope"

validObservation :: Observation -> Bool
validObservation o =
  Text.length (obsSourceSHA256 o) == 64 &&
  isLowerHex (obsSourceSHA256 o) &&
  canonicalHex (obsRootHex o) &&
  canonicalHex (obsOwnerHex o) &&
  canonicalHex (obsViewHex o) &&
  case (readCanonicalNat (obsOwnerOrdinal o),
        readCanonicalNat (obsViewOrdinal o)) of
    (Just ownerOrdinal, Just viewOrdinal) ->
      ownerOrdinal < viewOrdinal &&
      ((obsTrace o == positiveCuts && obsOutcome o == positiveOutcome) ||
       (obsTrace o == escapeCuts && obsOutcome o == escapeOutcome))
    _ -> False

decodeObservation :: Text -> Maybe Observation
decodeObservation raw = do
  payload <- Text.stripPrefix version raw
  (fields, suffix) <- parseFrames 8 payload
  if not (Text.null suffix) then Nothing else do
    observation <- toObservation fields
    if validObservation observation &&
       encodeObservation observation == raw
      then Just observation else Nothing

hexBytes :: BS.ByteString -> Text
hexBytes = Text.pack . concatMap encodeByte . BS.unpack
  where
    encodeByte n =
      let encoded = showHex n ""
      in if length encoded == 1 then '0' : encoded else encoded

utf8Hex :: Text -> Text
utf8Hex = hexBytes . TextEncoding.encodeUtf8

digestSource :: Text -> Text
digestSource = hexBytes . SHA256.hash . TextEncoding.encodeUtf8

expectedTy :: Ty
expectedTy = TyBytes (RefNat 8)

phaseCode :: BorrowTracePhase -> Text
phaseCode TraceBeforeLoan = "B"
phaseCode TraceLoanStarted = "S"
phaseCode (TraceBodyResult False) = "N"
phaseCode (TraceBodyResult True) = "E"
phaseCode TraceLoanClosed = "C"
phaseCode TraceOwnerReturned = "R"
phaseCode TraceEscapeRejected = "X"

showBit :: Bool -> Text
showBit True = "1"
showBit False = "0"

failWith :: String -> Either String a
failWith = Left

ensure :: Bool -> String -> Either String ()
ensure ok detail = if ok then Right () else Left detail

parseFunction :: Text -> Either String GrammarV1FunctionDecl
parseFunction source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem01-artifact-v1" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1FunctionDeclaration function -> Right function
        _ -> failWith "fixture is not a function declaration"
    _ -> failWith "fixture did not have exactly one declaration"

checkpointCode :: GrammarV1ResolvedBinder -> BorrowTraceCheckpoint
  -> Either String Text
checkpointCode owner cut = do
  let ownerName = grammarV1ResolvedBinderCoreName owner
      binding = Map.lookup ownerName (traceLinearOwners cut)
      loan = Set.member ownerName (traceActiveLoans cut)
  ensure (traceOwnerName cut == ownerName)
    "checkpoint changed exact owner name"
  ensure (binding == Nothing || binding == Just expectedTy)
    "checkpoint used unexpected linear owner type"
  ensure (Map.size (traceLinearOwners cut) == if binding == Nothing then 0 else 1)
    "checkpoint has extra linear owners"
  ensure (Set.size (traceActiveLoans cut) == if loan then 1 else 0)
    "checkpoint has extra shared loans"
  Right (phaseCode (tracePhase cut) <>
    showBit (binding /= Nothing) <> showBit loan)

observedOutcome
  :: Either GrammarV1BorrowResourceError SurfaceCheckResult
  -> Either String Text
observedOutcome (Right checked) = do
  ensure (checkedTerminalControls checked == [Return expectedTy])
    "normal exit lacks required terminal Bytes[8] return"
  Right positiveOutcome
observedOutcome (Left (GrammarV1BorrowResourceProductionError err)) = do
  ensure (surfaceErrorClass err == BorrowEscape &&
          surfaceErrorDetail err == "shared view escapes its lexical scope")
    "unexpected rejection classification or detail"
  Right escapeOutcome
observedOutcome outcome =
  failWith ("unadmitted checker outcome: " <> show outcome)

-- Only the actual, source-derived Grammar-v1 checker may mint a specimen.
observeSource :: DeclarationKey -> Text -> Either String Observation
observeSource root source = do
  parsed <- parseFunction source
  let ordinary = grammarV1CheckedBorrowResourceFunction
        emptyStaticContext root parsed
      traced = grammarV1CheckedBorrowResourceFunctionTrace
        emptyStaticContext root parsed
  trace <- case traced of
    Just (Right actual) -> Right actual
    other -> failWith ("source not admitted to traced fragment: " <> show other)
  ensure (ordinary == Just (grammarV1TraceOutcome trace))
    "traced and regular production checker disagree"
  let owner = grammarV1TraceOwnerBinder trace
      view = grammarV1TraceViewBinder trace
      ownerName = grammarV1ResolvedBinderCoreName owner
      viewName = grammarV1ResolvedBinderCoreName view
      ownerKey = grammarV1ResolvedBinderKey owner
      viewKey = grammarV1ResolvedBinderKey view
  ensure (grammarV1BinderDeclarationRoot ownerKey == root &&
          grammarV1BinderDeclarationRoot viewKey == root &&
          ownerKey /= viewKey &&
          ownerName /= viewName &&
          grammarV1BinderOrdinal ownerKey >= 0 &&
          grammarV1BinderOrdinal viewKey > grammarV1BinderOrdinal ownerKey)
    "source roots or ordinal order violate exact binder identity"
  ensure (grammarV1DecodeBinderCoreName ownerName == Just ownerKey &&
          grammarV1DecodeBinderCoreName viewName == Just viewKey)
    "source generated noncanonical Core name"
  ensure (all (\cut -> traceOwnerName cut == ownerName &&
                        traceViewName cut == viewName)
           (grammarV1TraceCheckpoints trace))
    "trace lost exact owner or view name"
  codes <- mapM (checkpointCode owner) (grammarV1TraceCheckpoints trace)
  outcome <- observedOutcome (grammarV1TraceOutcome trace)
  let o = Observation
        { obsSourceSHA256 = digestSource source
        , obsRootHex = utf8Hex (unDeclarationKey root)
        , obsOwnerHex = utf8Hex (unName ownerName)
        , obsViewHex = utf8Hex (unName viewName)
        , obsOwnerOrdinal = Text.pack (show (grammarV1BinderOrdinal ownerKey))
        , obsViewOrdinal = Text.pack (show (grammarV1BinderOrdinal viewKey))
        , obsTrace = Text.intercalate "," codes
        , obsOutcome = outcome
        }
  ensure (validObservation o)
    ("production emitted observation outside v1 schema: " <> show o)
  Right o

-- The source hashes bind the exact UTF-8 bytes read from the fixture. A
-- portable CI consumer also checks the hash independently with Python.
data Specimen = Specimen
  { specimenName :: FilePath
  , specimenSource :: FilePath
  , specimenRoot :: DeclarationKey
  }

specimens :: [Specimen]
specimens =
  [ Specimen "positive-ascii.obs" "test/fixtures/fsem01-observation-v1/positive.phil"
      (DeclarationKey "decl.FSEM01ObservationV1")
  , Specimen "escape-ascii.obs" "test/fixtures/fsem01-observation-v1/escape.phil"
      (DeclarationKey "decl.FSEM01ObservationV1")
  , Specimen "positive-unicode.obs" "test/fixtures/fsem01-observation-v1/positive.phil"
      (DeclarationKey "decl.é:猫")
  , Specimen "escape-unicode.obs" "test/fixtures/fsem01-observation-v1/escape.phil"
      (DeclarationKey "decl.é:猫")
  ]

makeSpecimen :: Specimen -> IO (Either String (FilePath, Text, Observation))
makeSpecimen sample = do
  source <- TextIO.readFile (specimenSource sample)
  pure $ do
    observation <- observeSource (specimenRoot sample) source
    Right (specimenName sample, source, observation)

checkOne :: (FilePath, Text, Observation) -> Either String ()
checkOne (_, source, actual) = do
  let wire = encodeObservation actual
  ensure (decodeObservation wire == Just actual)
    "v1 frame decoder failed to roundtrip a real production observation"
  ensure (obsSourceSHA256 actual == digestSource source)
    "source identity digest does not match exact source"
  let forgedTrace = actual { obsTrace = obsTrace actual <> ",C10" }
      forgedOutcome = actual { obsOutcome =
        if obsOutcome actual == positiveOutcome then escapeOutcome
        else positiveOutcome }
      forgedHash = actual { obsSourceSHA256 = Text.replicate 64 "0" }
      forgedRoot = actual { obsRootHex = "deadbeef" }
      malformed =
        [ Text.drop 1 wire
        , wire <> "x"
        , Text.dropEnd 1 wire
        , Text.replace version "PHIL-FSEM01-OBS-V2|" wire
        , Text.replace ("64:" <> obsSourceSHA256 actual)
                       ("064:" <> obsSourceSHA256 actual) wire
        , encodeObservation forgedTrace
        , encodeObservation forgedOutcome
        ]
  ensure (all ((== Nothing) . decodeObservation) malformed)
    "malformed framing or invalid control/outcome was accepted"
  -- Syntactically valid but forged provenance must fail a *binding* check,
  -- not be mistaken for a decoder's format error.
  ensure (decodeObservation (encodeObservation forgedHash) == Just forgedHash &&
          obsSourceSHA256 forgedHash /= digestSource source)
    "source-binding check failed to distinguish forged digest"
  ensure (decodeObservation (encodeObservation forgedRoot) == Just forgedRoot &&
          obsRootHex forgedRoot /= utf8Hex (unDeclarationKey (specimenRoot
            (head specimens))))
    "root-binding check failed to distinguish forged root"
  Right ()

emit :: FilePath -> [(FilePath, Text, Observation)] -> IO ()
emit directory observations = do
  createDirectoryIfMissing True directory
  mapM_ (\(name, _, artifact) -> TextIO.writeFile
      (directory <> "/" <> name) (encodeObservation artifact)) observations

main :: IO ()
main = do
  args <- getArgs
  generated <- mapM makeSpecimen specimens
  case sequence generated of
    Left reason -> putStrLn ("FAIL: " <> reason) >> exitFailure
    Right observations ->
      case traverse checkOne observations of
        Left reason -> putStrLn ("FAIL: " <> reason) >> exitFailure
        Right _ -> case args of
          [] -> putStrLn "PASS: four source-derived v1 artifacts and fail-closed decoder/tamper checks"
          ["--emit", directory] -> do
            emit directory observations
            putStrLn ("PASS: emitted four source-derived v1 artifacts in " <> directory)
          _ -> putStrLn "Usage: no args, or --emit DIR" >> exitFailure

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
