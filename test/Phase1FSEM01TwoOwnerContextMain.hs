{-# LANGUAGE OverloadedStrings #-}

-- Bounded two-owner Core resource frame test. Both identities are resolved
-- independently from actual Grammar-v1 source fragments; the resulting
-- two-owner context is a deliberate Core.Context composition, NOT a claim
-- that the surface source checker accepts an arbitrary two-owner function.
module Main (main) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Encoding
import qualified Data.Text.IO as TextIO
import Numeric (showHex)
import qualified Phil.Core.Context as Core
import Phil.Core.Static
  ( DeclarationDescriptor (..), DeclarationIdentity (..)
  , DeclarationKey (..), DeclarationPresentation (..)
  , SemanticForm (..), deriveDeclarationIdentity, emptyStaticContext
  )
import Phil.Core.Syntax (Control (Return), Mode (Linear), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine (BorrowTraceCheckpoint (..), BorrowTracePhase (..))
import Phil.Surface.Check.Types
  ( RejectionClass (BorrowEscape), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..), GrammarV1BorrowResourceTrace (..)
  , grammarV1CheckedBorrowResourceFunction
  , grammarV1CheckedBorrowResourceFunctionTrace
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..), GrammarV1TopLevelDecl (..)
  , GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.Syntax (Located (..))
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)

version :: Text
version = "PHIL-FSEM01-CONTEXT2-V1|"

expectedTy :: Ty
expectedTy = TyBytes (RefNat 8)

positiveOutcome, escapeOutcome :: Text
positiveOutcome = "OK:Bytes8"
escapeOutcome = "ERR:BorrowEscape:shared view escapes its lexical scope"

positiveSource, escapeSource :: FilePath
positiveSource = "test/fixtures/fsem01-observation-v1/positive.phil"
escapeSource = "test/fixtures/fsem01-observation-v1/escape.phil"

asciiRoot, unicodeRoot :: DeclarationKey
asciiRoot = deriveRoot "decl.FSEM01ObservationV1"
unicodeRoot = deriveRoot "decl.é:猫"

deriveRoot :: Text -> DeclarationKey
deriveRoot root =
  identityDeclarationKey (deriveDeclarationIdentity DeclarationDescriptor
    { declarationPresentation =
        DeclarationPresentation "observed-borrow" ["fsem", "wire-v1"]
    , declarationKey = DeclarationKey root
    , declarationInterfaceSemantics = SemanticAtom "bytes8-interface"
    , declarationDefinitionSemantics = SemanticAtom "loan-v1"
    })

hexBytes :: BS.ByteString -> Text
hexBytes = Text.pack . concatMap one . BS.unpack
  where
    one byte = let encoded = showHex byte ""
               in if length encoded == 1 then '0' : encoded else encoded

utf8Hex :: Text -> Text
utf8Hex = hexBytes . Encoding.encodeUtf8

sourceHash :: Text -> Text
sourceHash = hexBytes . SHA256.hash . Encoding.encodeUtf8

assert :: Bool -> String -> Either String ()
assert yes why = if yes then Right () else Left why

parseFunction :: Text -> Either String GrammarV1FunctionDecl
parseFunction source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-context2-v1" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ decl] -> case locatedValue (grammarV1Declaration decl) of
      GrammarV1FunctionDeclaration f -> Right f
      _ -> Left "fixture is not a function"
    _ -> Left "fixture must contain one function"

traced :: DeclarationKey -> Text -> Either String GrammarV1BorrowResourceTrace
traced root source = do
  parsed <- parseFunction source
  result <- case grammarV1CheckedBorrowResourceFunctionTrace
    emptyStaticContext root parsed of
    Just (Right check) -> Right check
    other -> Left ("source outside bounded checker fragment: " <> show other)
  assert
    (grammarV1CheckedBorrowResourceFunction emptyStaticContext root parsed ==
      Just (grammarV1TraceOutcome result))
    "ordinary and traced production checker outcomes differ"
  Right result

ownerOf :: GrammarV1BorrowResourceTrace -> Name
ownerOf = grammarV1ResolvedBinderCoreName . grammarV1TraceOwnerBinder

fromCheckpoint :: BorrowTraceCheckpoint -> Core.ResourceContext
fromCheckpoint cut = Core.ResourceContext
  { Core.unrestrictedBindings = traceUnrestrictedOwners cut
  , Core.affineBindings = traceAffineOwners cut
  , Core.linearBindings = traceLinearOwners cut
  , Core.sharedLoans = traceActiveLoans cut
  }

-- Add the *second independently source-resolved* linear owner to the actual
-- captured Core context. This calls the production Core insertion operation.
-- The original source checker was not run on a combined two-owner source.
augment :: Name -> BorrowTraceCheckpoint -> Either String Core.ResourceContext
augment spectator cut =
  either (Left . ("Core insert failed: " <>) . show) Right
    (Core.insertBinding Linear spectator expectedTy (fromCheckpoint cut))

phaseCode :: BorrowTracePhase -> Text
phaseCode TraceBeforeLoan = "B"
phaseCode TraceLoanStarted = "S"
phaseCode (TraceBodyResult False) = "N"
phaseCode (TraceBodyResult True) = "E"
phaseCode TraceLoanClosed = "C"
phaseCode TraceOwnerReturned = "R"
phaseCode TraceEscapeRejected = "X"

-- Role-ordered full finite-map representation, checked against the *whole*
-- Map/Set domains before emitting. Never silently drop foreign keys.
stateWord :: Name -> Name -> BorrowTracePhase
  -> Core.ResourceContext -> Either String Text
stateWord owner spectator phase ctx = do
  let unrestricted = Core.unrestrictedBindings ctx
      affine = Core.affineBindings ctx
      linear = Core.linearBindings ctx
      loans = Core.sharedLoans ctx
      ownerType = Map.lookup owner linear
      spectatorType = Map.lookup spectator linear
      expectedKeys = Set.fromList
        ([owner | ownerType /= Nothing] ++
         [spectator | spectatorType /= Nothing])
  assert (owner /= spectator) "owners are not distinct"
  assert (Map.null unrestricted && Map.null affine)
    "out-of-fragment unrestricted or affine binding"
  assert (Map.keysSet linear == expectedKeys &&
          (ownerType == Nothing || ownerType == Just expectedTy) &&
          spectatorType == Just expectedTy)
    "foreign/missing/wrong-type linear owner"
  assert (Set.isSubsetOf loans (Set.singleton owner))
    "foreign loan entered resource context"
  let linearCodes =
        [ utf8Hex (unName owner) <> "=Bytes8" | ownerType /= Nothing ] ++
        [ utf8Hex (unName spectator) <> "=Bytes8" ]
      loanCode =
        if Set.member owner loans then utf8Hex (unName owner) else "-"
  Right (Text.intercalate "/"
    [phaseCode phase, "-", "-", Text.intercalate ";" linearCodes, loanCode])

data Evidence = Evidence
  { ePrimaryHash :: Text
  , eSpectatorHash :: Text
  , ePrimaryRoot :: Text
  , eSpectatorRoot :: Text
  , ePrimaryName :: Text
  , eSpectatorName :: Text
  , eStates :: Text
  , eTerminal :: Text
  } deriving (Eq, Show)

fields :: Evidence -> [Text]
fields a =
  [ePrimaryHash a, eSpectatorHash a, ePrimaryRoot a, eSpectatorRoot a,
   ePrimaryName a, eSpectatorName a, eStates a, eTerminal a]

frame :: Text -> Text
frame field = Text.pack (show (Text.length field)) <> ":" <> field

encode :: Evidence -> Text
encode a = version <> Text.concat (map frame (fields a))

-- Independent of stateWord: expected endpoint membership for the admitted
-- two-owner Core.Context trajectory, with the spectator always preserved.
expectedWords :: Name -> Name -> Text -> Text
expectedWords owner spectator terminal =
  let own = utf8Hex (unName owner) <> "=Bytes8"
      other = utf8Hex (unName spectator) <> "=Bytes8"
      both = own <> ";" <> other
      loan = utf8Hex (unName owner)
      word phase pair active =
        Text.intercalate "/" [phase, "-", "-", pair, if active then loan else "-"]
  in if terminal == positiveOutcome
       then Text.intercalate ","
         [ word "B" both False, word "S" both True,
           word "N" both True, word "C" both False,
           word "R" other False ]
       else Text.intercalate ","
         [ word "B" both False, word "S" both True,
           word "E" both True, word "X" both True ]

-- Real Core operations are re-executed against the two-owner checkpoints,
-- not against phase-inferred snapshots. The spectator is independently
-- consumable during the primary loan, without ending or corrupting it.
checkTransitions :: Name -> Name -> [BorrowTracePhase]
  -> [Core.ResourceContext] -> Either String ()
checkTransitions owner spectator phases contexts = do
  assert (all (\ctx ->
    Map.lookup spectator (Core.linearBindings ctx) == Just expectedTy &&
    not (Set.member spectator (Core.sharedLoans ctx))) contexts)
    "spectator was lost, mistyped or unexpectedly borrowed"
  case (phases, contexts) of
    ([TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False,
      TraceLoanClosed, TraceOwnerReturned],
     [before, started, body, closed, returned]) -> do
      assert (Core.startSharedLoan owner before == Right started)
        "two-owner loan start changed unrelated context"
      assert (started == body)
        "safe source-body post-prune checkpoint changed resources"
      assert (Core.endSharedLoan owner body == Right closed)
        "two-owner loan end changed unrelated context"
      assert (Core.consumeLinear owner closed ==
        Right (expectedTy, returned))
        "two-owner terminal consumption changed unrelated context"
      assert (Map.lookup owner (Core.linearBindings returned) == Nothing)
        "terminal failed to consume exact primary owner"
      independentConsume owner spectator started
    ([TraceBeforeLoan, TraceLoanStarted, TraceBodyResult True,
      TraceEscapeRejected], [before, started, escaping, rejected]) -> do
      assert (Core.startSharedLoan owner before == Right started)
        "two-owner rejected prefix start differs from Core"
      assert (started == escaping && escaping == rejected)
        "BorrowEscape prefix fabricated an after-error successor"
      assert (Core.consumeLinear owner rejected ==
        Left (Core.OwnerBorrowed owner))
        "borrowed primary owner erroneously consumable"
      independentConsume owner spectator rejected
    _ -> Left "unadmitted two-owner source-observation phase sequence"

independentConsume :: Name -> Name -> Core.ResourceContext -> Either String ()
independentConsume owner spectator ctx = do
  (ty, remaining) <- either (Left . show) Right
    (Core.consumeLinear spectator ctx)
  assert (ty == expectedTy &&
          Map.lookup spectator (Core.linearBindings remaining) == Nothing &&
          Map.lookup owner (Core.linearBindings remaining) == Just expectedTy &&
          Set.member owner (Core.sharedLoans remaining))
    "independent spectator consumption damaged active owner loan"

sourceTerminal :: GrammarV1BorrowResourceTrace -> Either String Text
sourceTerminal t = case grammarV1TraceOutcome t of
  Right result -> do
    assert (checkedTerminalControls result == [Return expectedTy])
      "accepted source returned wrong value"
    Right positiveOutcome
  Left (GrammarV1BorrowResourceProductionError err) -> do
    assert (surfaceErrorClass err == BorrowEscape &&
            surfaceErrorDetail err == "shared view escapes its lexical scope")
      "source rejected for a reason other than BorrowEscape"
    Right escapeOutcome
  other -> Left ("unexpected source checker outcome: " <> show other)

makeEvidence :: Text -> Text -> Text -> Either String Evidence
makeEvidence primary spectatorSource expected = do
  first <- traced asciiRoot primary
  second <- traced unicodeRoot spectatorSource
  terminal <- sourceTerminal first
  otherTerminal <- sourceTerminal second
  assert (terminal == expected && otherTerminal == positiveOutcome)
    "source-derived owner or spectator did not pass expected checker result"
  let owner = ownerOf first
      spectator = ownerOf second
      cuts = grammarV1TraceCheckpoints first
      phases = map tracePhase cuts
  assert (owner /= spectator && not (null cuts))
    "source-derived owner names must be distinct and nonempty"
  contexts <- mapM (augment spectator) cuts
  checkTransitions owner spectator phases contexts
  words' <- sequence
    [ stateWord owner spectator phase ctx
    | (phase, ctx) <- zip phases contexts ]
  let evidence = Evidence
        (sourceHash primary)
        (sourceHash spectatorSource)
        (utf8Hex (unDeclarationKey asciiRoot))
        (utf8Hex (unDeclarationKey unicodeRoot))
        (utf8Hex (unName owner))
        (utf8Hex (unName spectator))
        (Text.intercalate "," words')
        terminal
  assert (eStates evidence == expectedWords owner spectator terminal)
    "source-derived two-owner states diverged from independent trajectory"
  -- Tampering must fail closed, not be silently projected away.
  let before = head cuts
      initial = head contexts
      thirdOwner = Name "unadmitted-third-owner"
      badContexts =
        [ initial { Core.linearBindings =
            Map.insert thirdOwner expectedTy (Core.linearBindings initial) }
        , initial { Core.affineBindings =
            Map.insert thirdOwner expectedTy Map.empty }
        , initial { Core.unrestrictedBindings =
            Map.insert thirdOwner expectedTy Map.empty }
        , initial { Core.sharedLoans = Set.singleton thirdOwner }
        , initial { Core.linearBindings =
            Map.delete spectator (Core.linearBindings initial) }
        , initial { Core.linearBindings =
            Map.insert spectator (TyBytes (RefNat 9))
              (Core.linearBindings initial) }
        ]
  assert (all (either (const True) (const False) .
        stateWord owner spectator (tracePhase before)) badContexts)
    "extra/missing/wrong-type resource maps escaped field validation"
  Right evidence

main :: IO ()
main = do
  args <- getArgs
  positive <- TextIO.readFile positiveSource
  escape <- TextIO.readFile escapeSource
  let produced = do
        accept <- makeEvidence positive positive positiveOutcome
        reject <- makeEvidence escape positive escapeOutcome
        assert (ePrimaryName accept == ePrimaryName reject &&
                eSpectatorName accept == eSpectatorName reject &&
                eSpectatorRoot accept == eSpectatorRoot reject)
          "owner/spectator identity shifted across two source specimens"
        Right [("positive.ctx2", encode accept), ("escape.ctx2", encode reject)]
  case produced of
    Left err -> putStrLn ("FAIL: " <> err) >> exitFailure
    Right evidence -> case args of
      [] -> putStrLn "PASS: two source-resolved owners; real Core frame/consume/error tests"
      ["--emit", directory] -> do
        createDirectoryIfMissing True directory
        mapM_ (\(name, bytes) ->
          TextIO.writeFile (directory <> "/" <> name) bytes) evidence
        putStrLn ("PASS: emitted two bounded CONTEXT2-V1 artifacts in " <> directory)
      _ -> putStrLn "Usage: no args or --emit DIR" >> exitFailure
