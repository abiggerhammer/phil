{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Phil.Core.Context as CoreContext
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import qualified Data.Text.IO as TextIO
import Numeric (showHex)
import Phil.Core.Static
  ( DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  , emptyStaticContext
  )
import Phil.Core.Syntax (Control (Return), Mode (Unrestricted), Name (..), RefSort (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..)
  , BorrowTracePhase (..)
  , BorrowTraceResourceObservation (..)
  , observeBorrowTraceResource
  )
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
                             (c >= 'a' && c <= 'f'))

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

-- Use the actual Engine observer, whose input is the recorded
-- ResourceContext projection, rather than inferring flags from phase tags.
checkpointCode
  :: GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder
  -> BorrowTraceCheckpoint -> Either String Text
checkpointCode owner view cut = do
  let ownerName = grammarV1ResolvedBinderCoreName owner
      viewName = grammarV1ResolvedBinderCoreName view
  observation <- maybe (failWith "source checkpoint has foreign owner, view, type, or loan")
    Right (observeBorrowTraceResource ownerName viewName expectedTy cut)
  Right (phaseCode (borrowObservedPhase observation) <>
    showBit (borrowObservedOwnerPresent observation) <>
    showBit (borrowObservedLoanActive observation))

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
  codes <- mapM (checkpointCode owner view) (grammarV1TraceCheckpoints trace)
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

deriveRoot :: Text -> DeclarationKey
deriveRoot root =
  identityDeclarationKey (deriveDeclarationIdentity DeclarationDescriptor
    { declarationPresentation =
        DeclarationPresentation "observed-borrow" ["fsem", "wire-v1"]
    , declarationKey = DeclarationKey root
    , declarationInterfaceSemantics = SemanticAtom "bytes8-interface"
    , declarationDefinitionSemantics = SemanticAtom "loan-v1"
    })

specimens :: [Specimen]
specimens =
  [ Specimen "positive-ascii.obs" "test/fixtures/fsem01-observation-v1/positive.phil"
      (deriveRoot "decl.FSEM01ObservationV1")
  , Specimen "escape-ascii.obs" "test/fixtures/fsem01-observation-v1/escape.phil"
      (deriveRoot "decl.FSEM01ObservationV1")
  , Specimen "positive-unicode.obs" "test/fixtures/fsem01-observation-v1/positive.phil"
      (deriveRoot "decl.é:猫")
  , Specimen "escape-unicode.obs" "test/fixtures/fsem01-observation-v1/escape.phil"
      (deriveRoot "decl.é:猫")
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
          obsRootHex forgedRoot /= obsRootHex actual)
    "root-binding check failed to distinguish forged root"
  Right ()

-- | Independently reconstruct the projection from ACTUAL checker snapshots.
-- The producer is required to preserve every observed phase, owner name and
-- membership bit. Forged Map/Set contents must fail before serialization.
checkProducerProjection :: (FilePath, Text, Observation) -> Either String ()
checkProducerProjection (filename, source, artifact) = do
  sample <- case filter ((== filename) . specimenName) specimens of
    [match] -> Right match
    _ -> Left ("unknown specimen identity: " <> filename)
  parsed <- parseFunction source
  traced <- case grammarV1CheckedBorrowResourceFunctionTrace
      emptyStaticContext (specimenRoot sample) parsed of
    Just (Right actual) -> Right actual
    other -> Left ("source-derived trace unavailable: " <> show other)
  let owner = grammarV1TraceOwnerBinder traced
      view = grammarV1TraceViewBinder traced
      ownerName = grammarV1ResolvedBinderCoreName owner
      viewName = grammarV1ResolvedBinderCoreName view
      cuts = grammarV1TraceCheckpoints traced
      ordinary = grammarV1CheckedBorrowResourceFunction
        emptyStaticContext (specimenRoot sample) parsed
  ensure (ordinary == Just (grammarV1TraceOutcome traced))
    "ordinary checker outcome diverged from raw trace outcome"
  ensure (not (null cuts)) "producer has no state snapshots to encode"
  ensure (all (\cut -> traceOwnerName cut == ownerName &&
                       traceViewName cut == viewName) cuts)
    "real source checkpoint changed exact identity"
  -- Check the production observer independently against the raw Haskell
  -- Map/Set snapshot, including the *whole* admitted single-owner domain.
  mapM_ (\cut -> do
    observed <- maybe (Left "real resource snapshot was rejected") Right
      (observeBorrowTraceResource ownerName viewName expectedTy cut)
    let binding = Map.lookup ownerName (traceLinearOwners cut)
        loan = Set.member ownerName (traceActiveLoans cut)
    ensure (borrowObservedPhase observed == tracePhase cut &&
            borrowObservedOwnerPresent observed == (binding /= Nothing) &&
            borrowObservedLoanActive observed == loan &&
            Map.size (traceLinearOwners cut) == if binding == Nothing then 0 else 1)
      "observer mismatches actual checker-state owner map"
    ensure (Set.size (traceActiveLoans cut) == if loan then 1 else 0)
      "observer mismatches actual checker-state shared-loan set") cuts
  codes <- mapM (checkpointCode owner view) cuts
  outcome <- observedOutcome (grammarV1TraceOutcome traced)
  let projected =
        [ digestSource source
        , utf8Hex (unDeclarationKey (specimenRoot sample))
        , utf8Hex (unName ownerName)
        , utf8Hex (unName viewName)
        , Text.pack (show (grammarV1BinderOrdinal
            (grammarV1ResolvedBinderKey owner)))
        , Text.pack (show (grammarV1BinderOrdinal
            (grammarV1ResolvedBinderKey view)))
        , Text.intercalate "," codes
        , outcome
        ]
  ensure (observationFields artifact == projected)
    "producer changed at least one original source, identity, state or outcome field"
  let first = head cuts
      other = Name "unauthorized-owner"
      badOwnerName = first { traceOwnerName = other }
      badViewName = first { traceViewName = other }
      extraUnrestricted = first
        { traceUnrestrictedOwners = Map.insert other expectedTy
            (traceUnrestrictedOwners first) }
      extraAffine = first
        { traceAffineOwners = Map.insert other expectedTy
            (traceAffineOwners first) }
      badOwnerType = first
        { traceLinearOwners = Map.insert ownerName
            (TyBytes (RefNat 9)) (traceLinearOwners first) }
      extraOwner = first
        { traceLinearOwners = Map.insert other expectedTy
            (traceLinearOwners first) }
      extraLoan = first
        { traceActiveLoans = Set.insert other (traceActiveLoans first) }
  ensure (all (\cut -> case checkpointCode owner view cut of
            Left _ -> True
            Right _ -> False)
            [badOwnerName, badViewName, extraUnrestricted, extraAffine,
             badOwnerType, extraOwner, extraLoan])
    "mutated production checkpoint silently passed the field projection"
  let wrongPhase = first { tracePhase = TraceEscapeRejected }
  wrongCode <- checkpointCode owner view wrongPhase
  ensure (not (validObservation (artifact
    { obsTrace = Text.intercalate "," (wrongCode : drop 1 codes) })))
    "fabricated error phase was accepted as a valid full trace"
  Right ()


-- FSEM-01 CONTEXT-V1 is a separate full admitted-resource-state carrier.
-- Unlike OBS-V1, its words contain the actual finite map entries, type tags,
-- and set members read at *every* recorded production checkpoint.
-- Only the strictly bounded Bytes[8] single-linear-owner fragment is valid.
contextVersion :: Text
contextVersion = "PHIL-FSEM01-CONTEXT-V1|"

viewTy :: Ty
viewTy = TyOpaqueSorted "SharedBytes" (SortFiniteSeq (SortUInt 8))

renderContextMap :: Map.Map Name Ty -> Either String Text
renderContextMap entries =
  case Map.toAscList entries of
    [] -> Right "-"
    pairs -> do
      encoded <- mapM (\(name, ty) -> do
        tag <- if ty == expectedTy then Right "Bytes8"
          else if ty == viewTy then Right "SharedBytes"
          else Left "unsupported resource binding type in CONTEXT-V1"
        Right (utf8Hex (unName name) <> "=" <> tag)) pairs
      Right (Text.intercalate "," encoded)

renderContextSet :: Set.Set Name -> Text
renderContextSet members =
  case Set.toAscList members of
    [] -> "-"
    names -> Text.intercalate "," (map (utf8Hex . unName) names)

renderRawContextState
  :: Name -> Name -> BorrowTraceCheckpoint -> Either String Text
renderRawContextState owner view cut = do
  ensure (traceOwnerName cut == owner && traceViewName cut == view)
    "context-wire checkpoint changed binder identity"
  unrestricted <- renderContextMap (traceUnrestrictedOwners cut)
  affine <- renderContextMap (traceAffineOwners cut)
  linear <- renderContextMap (traceLinearOwners cut)
  let loans = renderContextSet (traceActiveLoans cut)
  Right (Text.intercalate "/" [phaseCode (tracePhase cut),
    unrestricted, affine, linear, loans])

-- Canonical model words are used by the *validator*, never to produce
-- state. The producer above enumerates the real four ResourceContext fields.
modelContextWord :: Text -> Text -> Text -> Text
modelContextWord phase ownerPresent loan =
  Text.intercalate "/" [phase, "-", "-", ownerPresent, loan]

canonicalContextStates :: Observation -> Text
canonicalContextStates observation =
  let owner = obsOwnerHex observation
      present = owner <> "=Bytes8"
      state = \phase lin loan -> modelContextWord phase
        (if lin then present else "-") (if loan then owner else "-")
  in if obsOutcome observation == positiveOutcome
       then Text.intercalate "," [
         state "B" True False, state "S" True True,
         state "N" True True, state "C" True False,
         state "R" False False]
       else Text.intercalate "," [
         state "B" True False, state "S" True True,
         state "E" True True, state "X" True True]

contextFields :: Observation -> Text -> [Text]
contextFields observation states =
  [obsSourceSHA256 observation, obsRootHex observation,
   obsOwnerHex observation, obsViewHex observation,
   states, obsOutcome observation]

-- Keep source names as Haskell Name values; no unverified hex -> Text decoding.
encodeContextEvidence
  :: Observation -> Name -> Name -> [BorrowTraceCheckpoint]
  -> Either String Text
encodeContextEvidence observation owner view cuts = do
  states <- mapM (renderRawContextState owner view) cuts
  Right (contextVersion <> Text.concat (map frame
    (contextFields observation (Text.intercalate "," states))))

validContextEvidence :: Observation -> Text -> Bool
validContextEvidence observation wire =
  case Text.stripPrefix contextVersion wire >>= parseFrames 6 of
    Just (fields, suffix) ->
      Text.null suffix &&
      fields == contextFields observation (canonicalContextStates observation) &&
      wire == contextVersion <> Text.concat (map frame fields)
    Nothing -> False

contextOfCheckpoint :: BorrowTraceCheckpoint -> CoreContext.ResourceContext
contextOfCheckpoint cut = CoreContext.ResourceContext
  { CoreContext.unrestrictedBindings = traceUnrestrictedOwners cut
  , CoreContext.affineBindings = traceAffineOwners cut
  , CoreContext.linearBindings = traceLinearOwners cut
  , CoreContext.sharedLoans = traceActiveLoans cut
  }

-- Independently replay the *real* Core.Context operations against successive
-- production snapshots. No phase label is used to synthesize a successor.
checkCoreContextTransitions
  :: Name -> Name -> [BorrowTraceCheckpoint] -> Either String ()
checkCoreContextTransitions owner view cuts =
  case cuts of
    [before, started, body, closed, returned] -> do
      ensure (map tracePhase cuts ==
        [TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False,
         TraceLoanClosed, TraceOwnerReturned])
        "unexpected positive resource transition phases"
      ensure (CoreContext.startSharedLoan owner (contextOfCheckpoint before) ==
        Right (contextOfCheckpoint started))
        "real Core.Context loan start differs from source snapshot"
      -- The production body checkpoint is recorded *after*
      -- checkScopedValueBlock prunes the temporary SharedBytes binding.
      ensure (contextOfCheckpoint started == contextOfCheckpoint body)
        "safe body changed resources after scoped-view cleanup"
      temporary <- case CoreContext.insertBinding Unrestricted view viewTy
          (contextOfCheckpoint started) of
        Left err -> Left ("synthetic view insertion failed: " <> show err)
        Right context -> Right context
      ensure (Map.lookup view (CoreContext.unrestrictedBindings temporary) ==
                Just viewTy &&
              temporary { CoreContext.unrestrictedBindings =
                Map.delete view (CoreContext.unrestrictedBindings temporary) } ==
                contextOfCheckpoint body)
        "scoped SharedBytes insert/remove roundtrip disagrees with body cut"
      ensure (CoreContext.endSharedLoan owner (contextOfCheckpoint body) ==
        Right (contextOfCheckpoint closed))
        "real Core.Context loan end differs after scoped cleanup"
      ensure (CoreContext.consumeLinear owner (contextOfCheckpoint closed) ==
        Right (expectedTy, contextOfCheckpoint returned))
        "real Core.Context terminal consume differs from source snapshot"
    [before, started, escaping, rejected] -> do
      ensure (map tracePhase cuts ==
        [TraceBeforeLoan, TraceLoanStarted, TraceBodyResult True,
         TraceEscapeRejected])
        "unexpected escape-prefix resource phases"
      ensure (CoreContext.startSharedLoan owner (contextOfCheckpoint before) ==
        Right (contextOfCheckpoint started))
        "real Core.Context escape-path loan start differs from source snapshot"
      ensure (contextOfCheckpoint started == contextOfCheckpoint escaping &&
              contextOfCheckpoint escaping == contextOfCheckpoint rejected)
        "BorrowEscape prefix invented resource changes after scoped cleanup"
      temporary <- case CoreContext.insertBinding Unrestricted view viewTy
          (contextOfCheckpoint started) of
        Left err -> Left ("synthetic escape view insertion failed: " <> show err)
        Right context -> Right context
      ensure (Map.lookup view (CoreContext.unrestrictedBindings temporary) ==
                Just viewTy &&
              temporary { CoreContext.unrestrictedBindings =
                Map.delete view (CoreContext.unrestrictedBindings temporary) } ==
                contextOfCheckpoint escaping)
        "escape scoped SharedBytes insert/remove roundtrip disagrees with cut"
      ensure (CoreContext.consumeLinear owner (contextOfCheckpoint rejected) ==
        Left (CoreContext.OwnerBorrowed owner))
        "BorrowEscape resource incorrectly permitted terminal consumption"
    _ -> Left "unadmitted resource context trace shape"

contextSpecimen :: (FilePath, Text, Observation)
  -> Either String (FilePath, Text)
contextSpecimen (filename, source, artifact) = do
  sample <- case filter ((== filename) . specimenName) specimens of
    [match] -> Right match
    _ -> Left "unknown resource-context source specimen"
  parsed <- parseFunction source
  traced <- case grammarV1CheckedBorrowResourceFunctionTrace
      emptyStaticContext (specimenRoot sample) parsed of
    Just (Right actual) -> Right actual
    other -> Left ("resource-context trace unavailable: " <> show other)
  let owner = grammarV1ResolvedBinderCoreName (grammarV1TraceOwnerBinder traced)
      view = grammarV1ResolvedBinderCoreName (grammarV1TraceViewBinder traced)
      cuts = grammarV1TraceCheckpoints traced
  checkCoreContextTransitions owner view cuts
  wire <- encodeContextEvidence artifact owner view cuts
  ensure (validContextEvidence artifact wire)
    "actual full Map/Set representation failed strict CONTEXT-V1 validator"
  let first = head cuts
      other = Name "foreign-resource-owner"
      foreignUnrestricted = first
        { traceUnrestrictedOwners = Map.insert other expectedTy
            (traceUnrestrictedOwners first) }
      foreignAffine = first
        { traceAffineOwners = Map.insert other expectedTy
            (traceAffineOwners first) }
      foreignLinear = first
        { traceLinearOwners = Map.insert other expectedTy
            (traceLinearOwners first) }
      foreignLoan = first
        { traceActiveLoans = Set.insert other (traceActiveLoans first) }
      wrongType = first
        { traceLinearOwners = Map.insert owner (TyBytes (RefNat 9))
            (traceLinearOwners first) }
      changedIdentity = first { traceOwnerName = other }
      badRawStates = [foreignUnrestricted, foreignAffine, foreignLinear,
                      foreignLoan, wrongType, changedIdentity]
  mapM_ (\bad -> case encodeContextEvidence artifact owner view
                   (bad : drop 1 cuts) of
      Left _ -> Right ()
      Right forged -> ensure (not (validContextEvidence artifact forged))
        "tampered context map, loan or identity gained wire authority")
    badRawStates
  let contextFile = Text.unpack (Text.replace ".obs" ".ctx" (Text.pack filename))
  Right (contextFile, wire)

emit :: FilePath -> [(FilePath, Text, Observation)] -> IO ()
emit directory observations = do
  createDirectoryIfMissing True directory
  mapM_ (\(name, _, artifact) -> TextIO.writeFile
      (directory <> "/" <> name) (encodeObservation artifact)) observations

-- Backwards compatibility: --emit remains OBS-V1-only. The new mode
-- deliberately adds CONTEXT-V1 sidecars for independent state witnesses.
emitWithContexts :: FilePath -> [(FilePath, Text, Observation)] -> IO ()
emitWithContexts directory observations = do
  emit directory observations
  case traverse contextSpecimen observations of
    Left reason -> fail reason
    Right contexts -> mapM_ (\(name, wire) ->
      TextIO.writeFile (directory <> "/" <> name) wire) contexts

main :: IO ()
main = do
  args <- getArgs
  generated <- mapM makeSpecimen specimens
  case sequence generated of
    Left reason -> putStrLn ("FAIL: " <> reason) >> exitFailure
    Right observations ->
      case traverse (\observation -> do
              checkOne observation
              checkProducerProjection observation
              _ <- contextSpecimen observation
              Right ()) observations of
        Left reason -> putStrLn ("FAIL: " <> reason) >> exitFailure
        Right _ -> case args of
          [] -> putStrLn "PASS: four source-derived v1 artifacts and fail-closed decoder/tamper checks"
          ["--emit", directory] -> do
            emit directory observations
            putStrLn ("PASS: emitted four source-derived v1 artifacts in " <> directory)
          ["--emit-context", directory] -> do
            emitWithContexts directory observations
            putStrLn ("PASS: emitted four OBS-V1 and four CONTEXT-V1 artifacts in " <> directory)
          _ -> putStrLn "Usage: no args, --emit DIR, or --emit-context DIR" >> exitFailure

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
