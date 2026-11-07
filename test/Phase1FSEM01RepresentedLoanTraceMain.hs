{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static
  ( DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  , emptyStaticContext
  )
import Phil.Core.Syntax (Control (Return), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine (BorrowTraceCheckpoint (..), BorrowTracePhase (..))
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1BinderCoreName
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
import System.Exit (exitFailure)

-- This catalog is test-only: indices are observation IDs, not persistent
-- identifiers, and reordering changes those IDs. The production root remains
-- the exact DeclarationKey carried through the actual traced evaluator.
type Catalog = Map.Map DeclarationKey Integer
type ModelKey = (Integer, Int)

data ModelPhase
  = Before | Started | BodyResult Bool | Closed | Returned | Rejected
  deriving (Eq, Show)

data ModelCut = ModelCut
  { modelKey :: ModelKey
  , modelPhase :: ModelPhase
  , modelLinear :: Bool
  , modelLoan :: Bool
  }
  deriving (Eq, Show)

data ModelStep = BeginLoan | CheckBody Bool | EndLoan | ReturnOwner | RejectEscape
  deriving (Eq, Show)

expectedTy :: Ty
expectedTy = TyBytes (RefNat 8)

data ModelState = ModelState
  { currentPhase :: ModelPhase
  , currentLinear :: Bool
  , currentLoan :: Bool
  }
  deriving (Eq, Show)

initialState :: ModelState
initialState = ModelState Before True False

-- An independent finite model for the admitted single-linear-owner path.
-- Invalid transitions fail rather than inventing an observation. In particular,
-- an escaped view has NO EndLoan or ReturnOwner successor.
applyStep :: ModelState -> ModelStep -> Either String ModelState
applyStep (ModelState Before True False) BeginLoan =
  Right (ModelState Started True True)
applyStep (ModelState Started True True) (CheckBody escapes) =
  Right (ModelState (BodyResult escapes) True True)
applyStep (ModelState (BodyResult False) True True) EndLoan =
  Right (ModelState Closed True False)
applyStep (ModelState Closed True False) ReturnOwner =
  Right (ModelState Returned False False)
applyStep (ModelState (BodyResult True) True True) RejectEscape =
  Right (ModelState Rejected True True)
applyStep state step =
  Left ("invalid model transition: " <> show state <> " / " <> show step)

runModel :: ModelKey -> [ModelStep] -> Either String [ModelCut]
runModel owner steps = fmap reverse (snd <$> foldM apply
  (initialState, [snapshot initialState]) steps)
  where
    snapshot state = ModelCut owner (currentPhase state)
      (currentLinear state) (currentLoan state)
    apply (state, snapshots) step = do
      next <- applyStep state step
      Right (next, snapshot next : snapshots)

modelSteps :: Bool -> [ModelStep]
modelSteps False = [BeginLoan, CheckBody False, EndLoan, ReturnOwner]
modelSteps True = [BeginLoan, CheckBody True, RejectEscape]

phaseOf :: BorrowTracePhase -> ModelPhase
phaseOf TraceBeforeLoan = Before
phaseOf TraceLoanStarted = Started
phaseOf (TraceBodyResult escapes) = BodyResult escapes
phaseOf TraceLoanClosed = Closed
phaseOf TraceOwnerReturned = Returned
phaseOf TraceEscapeRejected = Rejected

catalogFrom :: [DeclarationKey] -> Either String Catalog
catalogFrom = go 0 Map.empty
  where
    go _ catalog [] = Right catalog
    go index catalog (root : rest)
      | Map.member root catalog =
          Left ("duplicate declaration root: " <> show root)
      | otherwise = go (index + 1) (Map.insert root index catalog) rest

deriveRoot :: Text -> DeclarationKey
deriveRoot root =
  identityDeclarationKey (deriveDeclarationIdentity DeclarationDescriptor
    { declarationPresentation =
        DeclarationPresentation "observed-borrow" ["fsem", "trace"]
    , declarationKey = DeclarationKey root
    , declarationInterfaceSemantics = SemanticAtom "bytes8-interface"
    , declarationDefinitionSemantics = SemanticAtom "borrow-body"
    })

roots :: [DeclarationKey]
roots = map deriveRoot
  [ "decl.FSEM01LoanTrace"
  , "decl:a:0"
  , ""
  , "é:猫"
  , "$phil.local:3:a:b:10"
  ]

parseFun :: Text -> Text -> Either String GrammarV1FunctionDecl
parseFun label source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls parsed of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1FunctionDeclaration fun -> Right fun
        other -> Left ("not a function: " <> show other)
    xs -> Left ("expected one declaration, got " <> show (length xs))

-- The parser and the *production* checker trace are used here; the name
-- encoder is checked against both the binder record and every checkpoint.
observeProductionCut
  :: Catalog
  -> GrammarV1ResolvedBinder
  -> GrammarV1ResolvedBinder
  -> BorrowTraceCheckpoint
  -> Either String ModelCut
observeProductionCut catalog owner view cut = do
  let originalKey = grammarV1ResolvedBinderKey owner
      viewKey = grammarV1ResolvedBinderKey view
      originalName = grammarV1ResolvedBinderCoreName owner
      originalView = grammarV1ResolvedBinderCoreName view
  decoded <- maybe (Left "trace owner does not decode canonically") Right
    (grammarV1DecodeBinderCoreName (traceOwnerName cut))
  viewDecoded <- maybe (Left "trace view does not decode canonically") Right
    (grammarV1DecodeBinderCoreName (traceViewName cut))
  assert (decoded == originalKey && viewDecoded == viewKey)
    "trace checkpoints disagree with resolved exact binder identities"
  assert (decoded /= viewDecoded
    && grammarV1BinderCoreName decoded /= grammarV1BinderCoreName viewDecoded)
    "owner and borrowed-view identities were aliased"
  assert (traceOwnerName cut == originalName && traceViewName cut == originalView)
    "traced owner/view Core names differ from actual binder names"
  abstractId <- maybe (Left "unrepresented declaration root") Right
    (Map.lookup (grammarV1BinderDeclarationRoot decoded) catalog)
  let ownerBinding = Map.lookup originalName (traceLinearOwners cut)
      present = ownerBinding /= Nothing
      loaned = Set.member originalName (traceActiveLoans cut)
  assert (ownerBinding == Nothing || ownerBinding == Just expectedTy)
    ("unexpected owner type in production snapshot: " <> show ownerBinding)
  assert (Map.size (traceLinearOwners cut) == if present then 1 else 0)
    "extra linear owner outside admitted one-owner fragment"
  assert (Set.size (traceActiveLoans cut) == if loaned then 1 else 0)
    "extra active loan outside admitted one-owner fragment"
  Right ModelCut
    { modelKey = (abstractId, grammarV1BinderOrdinal decoded)
    , modelPhase = phaseOf (tracePhase cut)
    , modelLinear = present
    , modelLoan = loaned
    }

-- | An independently checked relation on every pair of ACTUAL production
-- checkpoints. A rejection or terminal return has no outgoing rule.
observedStep :: ModelCut -> ModelCut -> Either String ()
observedStep prior next = do
  assert (modelKey next == modelKey prior)
    "step silently changed the represented owner identity"
  event <- case (modelPhase prior, modelPhase next) of
    (Before, Started) -> Right BeginLoan
    (Started, BodyResult False) -> Right (CheckBody False)
    (Started, BodyResult True) -> Right (CheckBody True)
    (BodyResult False, Closed) -> Right EndLoan
    (Closed, Returned) -> Right ReturnOwner
    (BodyResult True, Rejected) -> Right RejectEscape
    _ -> Left ("illegal loan step: " <> show prior <> " -> " <> show next)
  let priorState = ModelState
        (modelPhase prior) (modelLinear prior) (modelLoan prior)
      expectedState = ModelState
        (modelPhase next) (modelLinear next) (modelLoan next)
  actualState <- applyStep priorState event
  assert (actualState == expectedState)
    ("step changed linear/loan membership unexpectedly: " <> show prior
      <> " -> " <> show next)

validateObservedSteps :: [ModelCut] -> Either String ()
validateObservedSteps [] = Left "empty production trace cannot certify a path"
validateObservedSteps (first : rest) = do
  assert (first == ModelCut (modelKey first) Before True False)
    "production trace does not start with an unloaned linear owner"
  _ <- foldM (\previous current -> do
      observedStep previous current
      Right current) first rest
  Right ()

-- | Outcome classification is checked against the ACTUAL production result.
-- A prefix, a wrong error class or a post-error continuation fails closed.
validateTraceCertificate
  :: [ModelCut]
  -> Either GrammarV1BorrowResourceError SurfaceCheckResult
  -> Either String ()
validateTraceCertificate cuts outcome = do
  validateObservedSteps cuts
  case (last cuts, outcome) of
    (ModelCut _ Returned False False, Right checked) ->
      assert (checkedTerminalControls checked == [Return expectedTy])
        "terminal model path disagrees with production Bytes[8] return"
    (ModelCut _ Rejected True True,
      Left (GrammarV1BorrowResourceProductionError err)) ->
        assert (surfaceErrorClass err == BorrowEscape
          && surfaceErrorDetail err == "shared view escapes its lexical scope")
          "rejection certificate lacked the exact production BorrowEscape result"
    _ -> Left "trace end state and actual production outcome disagree"

isRejected :: Either String a -> Bool
isRejected (Left _) = True
isRejected (Right _) = False

checkTrace :: Catalog -> DeclarationKey -> Bool -> Text -> Either String ()
checkTrace catalog root escapes label = do
  parsed <- parseFun label (if escapes then escapingBody else safeBody)
  let ordinary = grammarV1CheckedBorrowResourceFunction
        emptyStaticContext root parsed
      traced = grammarV1CheckedBorrowResourceFunctionTrace
        emptyStaticContext root parsed
  trace <- case traced of
    Just (Right result) -> Right result
    other -> Left ("production trace not admitted: " <> show other)
  assert (ordinary == Just (grammarV1TraceOutcome trace))
    "traced and ordinary production checker outcomes disagree"
  let owner = grammarV1TraceOwnerBinder trace
      view = grammarV1TraceViewBinder trace
      ownerKey = grammarV1ResolvedBinderKey owner
      viewKey = grammarV1ResolvedBinderKey view
  assert (grammarV1BinderDeclarationRoot ownerKey == root
    && grammarV1BinderDeclarationRoot viewKey == root)
    "owner/view binder roots changed during lexical allocation"
  abstractId <- maybe (Left "root was not admitted in catalog") Right
    (Map.lookup root catalog)
  let key = (abstractId, grammarV1BinderOrdinal ownerKey)
  expected <- runModel key (modelSteps escapes)
  observed <- mapM (observeProductionCut catalog owner view)
    (grammarV1TraceCheckpoints trace)
  assert (observed == expected)
    ("production loan-state trace does not commute with represented model"
      <> "\nactual = " <> show observed
      <> "\nmodel = " <> show expected)
  validateTraceCertificate observed (grammarV1TraceOutcome trace)
  if escapes
    then case grammarV1TraceOutcome trace of
      Left (GrammarV1BorrowResourceProductionError err) -> do
        assert (surfaceErrorClass err == BorrowEscape
          && surfaceErrorDetail err == "shared view escapes its lexical scope")
          ("rejected path used wrong production error: " <> show err)
        assert (last observed == ModelCut key Rejected True True)
          "rejection manufactured loan closure or owner consumption"
      other -> Left ("escape was not rejected by checker: " <> show other)
    else case grammarV1TraceOutcome trace of
      Right checked -> assert
        (checkedTerminalControls checked == [Return expectedTy])
        "accepted path did not terminate with exact Bytes[8] owner return"
      other -> Left ("safe borrow was rejected: " <> show other)

safeBody, escapingBody :: Text
safeBody = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { view; unit; };"
  , "  return owner;"
  , "}"
  ]
escapingBody = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { view; };"
  , "  return owner;"
  , "}"
  ]

testRealTraces :: Either String ()
testRealTraces = do
  catalog <- catalogFrom roots
  mapM_ (\(index, root) -> do
    assert (Map.lookup root catalog == Just index)
      ("catalog lost exact root: " <> show root)
    checkTrace catalog root False (Text.pack ("represented-positive-" <> show index))
    checkTrace catalog root True (Text.pack ("represented-escape-" <> show index)))
    (zip [0 ..] roots)

testCatalogAuthority :: Either String ()
testCatalogAuthority = do
  catalog <- catalogFrom roots
  let other = deriveRoot "unlisted.declaration"
  assert (Map.notMember other catalog) "unknown root was added implicitly"
  parsed <- parseFun "unrepresented" safeBody
  trace <- case grammarV1CheckedBorrowResourceFunctionTrace
    emptyStaticContext other parsed of
      Just (Right result) -> Right result
      value -> Left ("unexpected trace competence: " <> show value)
  case grammarV1TraceCheckpoints trace of
    [] -> Left "production trace unexpectedly empty"
    first : _ -> case observeProductionCut catalog
      (grammarV1TraceOwnerBinder trace)
      (grammarV1TraceViewBinder trace) first of
        Left _ -> Right ()
        Right _ -> Left "unlisted root gained a made-up model identity"

testDistinctCatalogOrdering :: Either String ()
testDistinctCatalogOrdering = do
  original <- catalogFrom roots
  reordered <- catalogFrom (reverse roots)
  parsed <- parseFun "reordered" safeBody
  let root = head roots
  trace <- case grammarV1CheckedBorrowResourceFunctionTrace
    emptyStaticContext root parsed of
    Just (Right result) -> Right result
    value -> Left ("unexpected trace after catalog reorder: " <> show value)
  let ownerName = grammarV1ResolvedBinderCoreName (grammarV1TraceOwnerBinder trace)
      decoded = grammarV1DecodeBinderCoreName ownerName
  assert (Map.lookup root original /= Map.lookup root reordered)
    "model catalog order was wrongly treated as persistent ID"
  assert (decoded == Just (grammarV1ResolvedBinderKey (grammarV1TraceOwnerBinder trace)))
    "production Core name depended on model catalog ordering"

-- | Tamper with real source-derived checkpoints and outcomes. The bounded
-- observer must reject every forged continuation and corrupted error prefix.
testTamperRejection :: Either String ()
testTamperRejection = do
  catalog <- catalogFrom roots
  let root = head roots
  parsed <- parseFun "tamper-negative" escapingBody
  rejectedTrace <- case grammarV1CheckedBorrowResourceFunctionTrace
      emptyStaticContext root parsed of
    Just (Right trace) -> Right trace
    other -> Left ("negative source not admitted: " <> show other)
  cuts <- mapM (observeProductionCut catalog
    (grammarV1TraceOwnerBinder rejectedTrace)
    (grammarV1TraceViewBinder rejectedTrace))
    (grammarV1TraceCheckpoints rejectedTrace)
  let negativeOutcome = grammarV1TraceOutcome rejectedTrace
  validateTraceCertificate cuts negativeOutcome
  safeParsed <- parseFun "tamper-positive" safeBody
  safeTrace <- case grammarV1CheckedBorrowResourceFunctionTrace
      emptyStaticContext root safeParsed of
    Just (Right trace) -> Right trace
    other -> Left ("positive source not admitted: " <> show other)
  let acceptedOutcome = grammarV1TraceOutcome safeTrace
      key = modelKey (head cuts)
      inventedClose = ModelCut key Closed True False
      inventedReturn = ModelCut key Returned False False
      wrongOwner = case cuts of
        first : second : rest ->
          first : second { modelKey = (-1, 777) } : rest
        _ -> []
      wrongMembership = case cuts of
        first : second : rest ->
          first : second { modelLoan = False } : rest
        _ -> []
      skippedLoanStart = case cuts of
        first : _ : third : rest -> first : third : rest
        _ -> []
      truncated = take 3 cuts
      mutations =
        [ validateTraceCertificate (cuts ++ [inventedClose]) negativeOutcome
        , validateTraceCertificate (cuts ++ [inventedReturn]) negativeOutcome
        , validateTraceCertificate wrongOwner negativeOutcome
        , validateTraceCertificate wrongMembership negativeOutcome
        , validateTraceCertificate skippedLoanStart negativeOutcome
        , validateTraceCertificate truncated negativeOutcome
        , validateTraceCertificate cuts acceptedOutcome
        ]
  assert (all isRejected mutations)
    "forged transition, incomplete negative trace or mismatch was certified"

test :: String -> Either String () -> IO Bool
test label outcome = case outcome of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail)
    >> pure False

main :: IO ()
main = do
  results <- sequence
    [ test "FSEM-01 represented production loan steps: accept and exact escape"
        testRealTraces
    , test "FSEM-01 absent catalog root cannot fabricate a modeled checkpoint"
        testCatalogAuthority
    , test "FSEM-01 catalog positions never rewrite production Core names"
        testDistinctCatalogOrdering
    , test "FSEM-01 production BorrowEscape rejects forged trace extensions"
        testTamperRejection
    ]
  if and results then pure () else exitFailure

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
