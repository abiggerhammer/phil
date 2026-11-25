{-# LANGUAGE OverloadedStrings #-}

-- Standalone actual-object and private joint execution adversarial controls.
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Internal as Internal
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified FSEM06SteveGetNativeKernel as K
import Phil.Compiler.SelectedSteveGetCoreExecution
import qualified Phil.Compiler.RuntimeChoicePayload as P
import Phil.Core.Static (InterfaceRevision (..), DefinitionRevision (..))
import Phil.Examples.Phase1.SystemsWitnesses (steveCoreProgram)
import qualified Phil.Surface.SelectedSteveGetExecution as S
import qualified Phil.Systems.GenericLowering as C
import System.Exit (exitFailure)

require :: String -> Bool -> IO ()
require label ok = do
  unless ok (putStrLn ("FAIL: " ++ label) >> exitFailure)
  putStrLn ("PASS: " ++ label)

orDie :: Show e => String -> Either e a -> IO a
orDie label result = case result of
  Left problem -> putStrLn ("FAIL: " ++ label ++ ": " ++ show problem) >> exitFailure
  Right value -> pure value

rejectedAdmission :: String -> Either Text SelectedSteveGetCore -> IO ()
rejectedAdmission label result = require label $ case result of
  Left _ -> True
  Right _ -> False

kernelRejected :: String -> Either Text SelectedSteveGetCore -> IO ()
kernelRejected label result = require label $ case result of
  Left "proof-extracted full typed selector rejected" -> True
  _ -> False

complete :: String -> IO CoreRunResult -> IO CoreReceipt
complete label action = do
  result <- action
  case result of
    CoreCompleted receipt -> putStrLn ("PASS: " ++ label) >> pure receipt
    CoreRejected problem -> putStrLn ("FAIL: " ++ label ++ ": " ++ Text.unpack problem) >> exitFailure
    CoreWaiting _ -> putStrLn ("FAIL: " ++ label ++ ": unexpected wait") >> exitFailure

waiting :: String -> IO CoreRunResult -> IO CoreReceipt
waiting label action = do
  result <- action
  case result of
    CoreWaiting receipt -> putStrLn ("PASS: " ++ label) >> pure receipt
    _ -> putStrLn ("FAIL: " ++ label ++ ": expected finite wait") >> exitFailure

rejectedRun :: String -> IO CoreRunResult -> IO ()
rejectedRun label action = do
  result <- action
  require label $ case result of
    CoreRejected _ -> True
    _ -> False

-- Independently reconstructed exact existing INT-006 fixture plan;
-- not imported from the new selector's expected plan or Rocq model.
payloadSpecs :: [P.RuntimeChoicePayloadSpec]
payloadSpecs =
  [ spec "StevePut" "put.entry" [arm "computed" "put.install" (Just "put.id")]
  , spec "StevePut" "put.install"
      [arm "installed" "put.ok" Nothing, arm "already-exists" "put.ok" Nothing,
       arm "storage-failure" "put.failure" Nothing]
  , spec "SteveGet" "get.entry"
      [arm "found" "get.check" (Just "get.bytes"), arm "not-found" "get.not-found" Nothing,
       arm "storage-failure" "get.failure" Nothing]
  , spec "SteveGet" "get.check"
      [arm "accepted" "get.ok" Nothing, arm "rejected" "get.integrity-failure" Nothing]
  ]
  where
    spec fn block arms = P.RuntimeChoicePayloadSpec (P.RuntimeChoiceSite fn block)
      (Map.fromList arms)
    arm label target value = (label, P.RuntimeChoicePayloadArm target value)

changePlanArm :: Text -> Text -> Maybe Text -> [P.RuntimeChoicePayloadSpec]
changePlanArm block label replacement = map change payloadSpecs
  where
    change spec
      | P.runtimeChoicePayloadSite spec == P.RuntimeChoiceSite "SteveGet" block =
          spec { P.runtimeChoicePayloadArms = Map.adjust
            (\arm -> arm { P.runtimeChoicePayloadValue = replacement })
            label (P.runtimeChoicePayloadArms spec) }
      | otherwise = spec

changeGet :: (C.CoreSystemsFunction -> C.CoreSystemsFunction) -> C.CoreSystemsProgram
changeGet f = steveCoreProgram
  { C.coreProgramFunctions = Map.adjust f "SteveGet"
      (C.coreProgramFunctions steveCoreProgram) }

changeValue :: Text -> (C.CoreSystemsValue -> C.CoreSystemsValue) -> C.CoreSystemsProgram
changeValue key f = changeGet $ \fn -> fn
  { C.coreFunctionValues = Map.adjust f key (C.coreFunctionValues fn) }

changeBlock :: Text -> (C.CoreSystemsBlock -> C.CoreSystemsBlock) -> C.CoreSystemsProgram
changeBlock key f = changeGet $ \fn -> fn
  { C.coreFunctionBlocks = Map.adjust f key (C.coreFunctionBlocks fn) }

changeChoice :: Text -> (Text -> [Text] -> Maybe Text -> (Text, [Text], Maybe Text))
  -> C.CoreSystemsProgram
changeChoice key f = changeBlock key $ \block ->
  case C.coreBlockTerminator block of
    C.CoreSystemsRuntimeChoice op operands site arms ->
      let (op', operands', site') = f op operands site
      in block { C.coreBlockTerminator = C.CoreSystemsRuntimeChoice op' operands' site' arms }
    _ -> block

coreMutations :: [(String, C.CoreSystemsProgram)]
coreMutations =
  [ ("wrong retained owned-buffer role", changeValue "get.bytes" $ \v ->
      v { C.coreValueRole = C.CoreRuntimeScalar "ContentId[SHA256]" })
  , ("wrong retained storage identity", changeValue "get.bytes" $ \v ->
      v { C.coreValueStorageIdentity = Just "other.storage" })
  , ("wrong borrowed source owner", changeValue "get.bytes-view" $ \v ->
      v { C.coreValueRole = C.CoreBorrowedValue "get.id" })
  , ("wrong digest operand order", changeChoice "get.check" $ \op args site ->
      (op, reverse args, site))
  , ("wrong qualified Core read operation", changeChoice "get.entry" $ \_ args site ->
      ("OtherProvider.read", args, site))
  , ("erased runtime-site key mutation", changeChoice "get.entry" $ \op args _ ->
      (op, args, Just "other.site"))
  , ("erased cleanup-decision key mutation", changeBlock "get.ok" $ \block ->
      block { C.coreBlockOperations =
        [C.CoreReleaseOwner "other.cleanup" "get.bytes", C.CoreTrace "steve.get.commit"] })
  , ("extra reachable diagnostic/effect", changeBlock "get.ok" $ \block ->
      block { C.coreBlockOperations = C.coreBlockOperations block ++ [C.CoreTrace "extra"] })
  , ("extra unreachable block", changeGet $ \fn ->
      fn { C.coreFunctionBlocks = Map.insert "get.extra"
        (C.CoreSystemsBlock "get.extra" [C.CoreTrace "extra"] (C.CoreSystemsEnd "success"))
        (C.coreFunctionBlocks fn) })
  , ("wrong embedded value key", changeValue "get.id" $ \v ->
      v { C.coreValueKey = "get.other-id" })
  ]

main :: IO ()
main = do
  raw <- TextIO.readFile "examples/steve/get.phil"
  source <- orDie "actual source admission" (S.prepareSelectedSteveGet raw)
  plan <- orDie "actual complete plan certification"
    (P.certifyRuntimeChoicePayloadPlan steveCoreProgram payloadSpecs)
  selected <- orDie "actual joint source/Core/plan + extracted selector admission"
    (prepareSelectedSteveGetCore raw steveCoreProgram plan)

  mapM_ (\(label, program) -> do
    generic <- orDie ("generic recertification of " ++ label)
      (P.certifyRuntimeChoicePayloadPlan program payloadSpecs)
    kernelRejected label (prepareSelectedSteveGetCore raw program generic))
    coreMutations

  mapM_ (\(label, specs) -> do
    generic <- orDie ("generic certification accepts " ++ label)
      (P.certifyRuntimeChoicePayloadPlan steveCoreProgram specs)
    kernelRejected label (prepareSelectedSteveGetCore raw steveCoreProgram generic))
    [ ("found result wrongly assigned to declared get.id",
        changePlanArm "get.entry" "found" (Just "get.id"))
    , ("found result erased", changePlanArm "get.entry" "found" Nothing)
    , ("not-found result spuriously assigned", changePlanArm "get.entry" "not-found" (Just "get.bytes"))
    , ("storage failure spuriously assigned", changePlanArm "get.entry" "storage-failure" (Just "get.id"))
    , ("digest accepted spuriously assigned", changePlanArm "get.check" "accepted" (Just "get.id"))
    , ("missing entire digest plan site", filter
        ((/= P.RuntimeChoiceSite "SteveGet" "get.check") . P.runtimeChoicePayloadSite) payloadSpecs)
    ]

  -- Invalid native Map cached size must fail BEFORE projection/equality.
  let malformed = changeGet $ \fn -> fn { C.coreFunctionValues =
        Internal.Bin 999 "get.id" (C.CoreSystemsValue "get.id"
          (C.CoreRuntimeScalar "ContentId[SHA256]") Nothing) Internal.Tip Internal.Tip }
  rejectedAdmission "malformed original native Core container"
    (prepareSelectedSteveGetCore raw malformed plan)

  mapM_ (\(label, changed) -> rejectedAdmission label
    (prepareSelectedSteveGetCore changed steveCoreProgram plan))
    [ ("wrong actual source declaration", Text.replace "component SteveGet" "component Other" raw)
    , ("wrong original read operand", Text.replace "blob_read(contentId)" "blob_read(otherId)" raw)
    , ("wrong actual source digest order", Text.replace
        "digest_check(contentId, bytesView)" "digest_check(bytesView, contentId)" raw)
    , ("wrong original source release", Text.replace "release bytes" "release bytesView" raw)
    ]

  let ident = "sha256:equal-id"
      payload = "identical-payload-bytes"
      readAt = S.selectedReadOccurrence source
      digestAt = S.selectedDigestOccurrence source
      readProvider = S.selectedReadProvider source
      digestProvider = S.selectedDigestProvider source
      readFound = S.ReadResponse readAt readProvider ident (S.ReadFound payload)
      digestYes = S.DigestResponse digestAt digestProvider ident "bytesView" S.DigestAccepted
      digestNo = S.DigestResponse digestAt digestProvider ident "bytesView" (S.DigestRejected "reason")
      envYes = [readFound, digestYes]
      envNo = [readFound, digestNo]

  world <- newSelectedCoreWorld
  first <- complete "same fixed E accepted found execution"
    (runSelectedSteveGetCore world selected ident envYes)
  require "receipt bound to exact subject, ContentId and full E"
    (receiptMatchesContext first selected ident envYes
      && not (receiptMatchesContext first selected ident envNo)
      && not (receiptMatchesContext first selected "sha256:other" envYes)
      && receiptConsumedResponses first == envYes)
  require "exact found payload, same loan, cleanup, diagnostic and Unit"
    (acceptedTrace payload (receiptObservations first))
  firstPair <- maybe (putStrLn "FAIL: missing source owner/loan" >> exitFailure)
    pure (receiptOriginPair first)

  second <- complete "sequential equal-content found has fresh origins"
    (runSelectedSteveGetCore world selected ident envYes)
  secondPair <- maybe (putStrLn "FAIL: missing second source owner/loan" >> exitFailure)
    pure (receiptOriginPair second)
  require "paired valid B/B substitution fails for original A receipt"
    (uncurry (receiptMatchesOriginPair first) firstPair
      && uncurry (receiptMatchesOriginPair second) secondPair
      && not (uncurry (receiptMatchesOriginPair first) secondPair)
      && not (uncurry (receiptMatchesOriginPair second) firstPair)
      && fst firstPair /= fst secondPair && snd firstPair /= snd secondPair)

  otherWorld <- newSelectedCoreWorld
  other <- complete "separate world same bytes and abstract cursor"
    (runSelectedSteveGetCore otherWorld selected ident envYes)
  otherPair <- maybe (putStrLn "FAIL: missing separate-world source pair" >> exitFailure)
    pure (receiptOriginPair other)
  require "opaque world identity defeats equal-cursor A/B substitution"
    (uncurry (receiptMatchesOriginPair other) otherPair
      && not (uncurry (receiptMatchesOriginPair first) otherPair))

  rejected <- complete "same fixed E rejected digest execution"
    (runSelectedSteveGetCore world selected ident envNo)
  require "digest rejection cannot be projected as accepted"
    (rejectedTrace payload (receiptObservations rejected)
      && not (receiptMatchesContext rejected selected ident envYes))

  missing <- complete "nonfound returns Unit without owner/loan/digest"
    (runSelectedSteveGetCore world selected ident [S.ReadResponse readAt readProvider ident S.ReadNotFound])
  require "exact nonfound observations"
    (receiptObservations missing == [CoreReadNotFound, CoreReturnedUnit S.UnitNotFound]
      && receiptOriginPair missing == Nothing)
  failure <- complete "storage failure returns Unit without owner/loan/digest"
    (runSelectedSteveGetCore world selected ident
      [S.ReadResponse readAt readProvider ident (S.ReadStorageFailure "reason")])
  require "exact storage-failure observations"
    (receiptObservations failure == [CoreReadFailure, CoreReturnedUnit S.UnitStorageFailure]
      && receiptOriginPair failure == Nothing)

  emptyWorld <- newSelectedCoreWorld
  pendingRead <- waiting "unanswered read: repeated poll is not reissue"
    (runSelectedSteveGetCore emptyWorld selected ident [])
  require "empty fixed E has no completed observation or origin"
    (null (receiptObservations pendingRead) && null (receiptConsumedResponses pendingRead))
  rejectedRun "cannot reset pending read/world" (runSelectedSteveGetCore emptyWorld selected ident envYes)
  prefixWorld <- newSelectedCoreWorld
  pendingDigest <- waiting "found-only E prefix waits for digest, without closing loan"
    (runSelectedSteveGetCore prefixWorld selected ident [readFound])
  require "waiting digest retains the exact found event and live loan"
    (case receiptObservations pendingDigest of
      [CoreReadFound actual o, CoreBorrowOpened o' l] ->
        actual == payload && o == o' && o /= l && receiptOriginPair pendingDigest /= Nothing
      _ -> False)
  rejectedRun "cannot reset live loan/world" (runSelectedSteveGetCore prefixWorld selected ident envYes)

  dynamicKernelNegatives
  let wrongRead = readProvider { S.qualifiedProviderInterface = InterfaceRevision "forged" }
      wrongDigest = digestProvider { S.qualifiedProviderImplementation = DefinitionRevision "forged" }
  mapM_ (\(label, offered) -> do
    fresh <- newSelectedCoreWorld
    rejectedRun label (runSelectedSteveGetCore fresh selected ident offered))
    [ ("wrong original read site", [S.ReadResponse digestAt readProvider ident (S.ReadFound payload)])
    , ("wrong read qualification revision", [S.ReadResponse readAt wrongRead ident (S.ReadFound payload)])
    , ("wrong original read id", [S.ReadResponse readAt readProvider "other" (S.ReadFound payload)])
    , ("digest before read", [digestYes])
    , ("wrong original digest site", [readFound, S.DigestResponse readAt digestProvider ident "bytesView" S.DigestAccepted])
    , ("wrong digest qualification revision", [readFound, S.DigestResponse digestAt wrongDigest ident "bytesView" S.DigestAccepted])
    , ("wrong original digest id", [readFound, S.DigestResponse digestAt digestProvider "other" "bytesView" S.DigestAccepted])
    , ("wrong borrowed view", [readFound, S.DigestResponse digestAt digestProvider ident "otherView" S.DigestAccepted])
    , ("extra read after found", [readFound, readFound])
    , ("extra digest after terminal", [readFound, digestYes, digestNo])
    ]
  -- The full-field extracted guard itself must reject these actual bad E
  -- identities, rather than relying solely on the earlier Haskell guards.
  let badReadImpl = readProvider { S.qualifiedProviderImplementation = DefinitionRevision "wrong" }
      badReadOp = readProvider { S.qualifiedProviderOperation = "wrong" }
      badDigestIface = digestProvider { S.qualifiedProviderInterface = InterfaceRevision "wrong" }
      badDigestOp = digestProvider { S.qualifiedProviderOperation = "wrong" }
  mapM_ (\(label, offered) -> do
    fresh <- newSelectedCoreWorld
    result <- runSelectedSteveGetCore fresh selected ident offered
    require label $ case result of
      CoreRejected "proof-extracted qualified binding rejected" -> True
      _ -> False)
    [ ("bridge rejects read occurrence with correct K/I", [S.ReadResponse digestAt readProvider ident (S.ReadFound payload)])
    , ("bridge rejects read interface revision", [S.ReadResponse readAt wrongRead ident (S.ReadFound payload)])
    , ("bridge rejects read implementation revision", [S.ReadResponse readAt badReadImpl ident (S.ReadFound payload)])
    , ("bridge rejects read operation", [S.ReadResponse readAt badReadOp ident (S.ReadFound payload)])
    , ("bridge rejects actual invocation ContentId", [S.ReadResponse readAt readProvider "other" (S.ReadFound payload)])
    , ("bridge rejects digest occurrence", [readFound, S.DigestResponse readAt digestProvider ident "bytesView" S.DigestAccepted])
    , ("bridge rejects digest interface revision", [readFound, S.DigestResponse digestAt badDigestIface ident "bytesView" S.DigestAccepted])
    , ("bridge rejects digest implementation revision", [readFound, S.DigestResponse digestAt wrongDigest ident "bytesView" S.DigestAccepted])
    , ("bridge rejects digest operation", [readFound, S.DigestResponse digestAt badDigestOp ident "bytesView" S.DigestAccepted])
    , ("bridge rejects digest invocation ContentId", [readFound, S.DigestResponse digestAt digestProvider "other" "bytesView" S.DigestAccepted])
    ]
  putStrLn "PASS: actual selected source/Core/plan reference checks and extracted dynamic segment checks (not native ABI)"

-- Test the newly extracted DYNAMIC verifier directly, including a poisoned
-- representation that the old static selector could not detect.
dynamicKernelNegatives :: IO ()
dynamicKernelNegatives = case K.expected_native of
  subject@(K.NSubject dk ik blob digest _ _) -> do
    let zero = K.O
        one = K.S zero
        two = K.S one
        binding = K.Binding dk ik [[zero]] [[one]] blob [zero] [one]
          digest [one] [two] [zero]
        bad = K.Binding dk ik [[one]] [[one]] blob [zero] [one]
          digest [one] [two] [zero]
        start = K.TRead zero [] []
        finish payload = K.TDigest two [one, zero] [] payload zero one
        offered = [K.QFound binding zero]
        observations = [K.ObsFound zero zero, K.ObsBorrow zero one]
        labels = [K.ReadFound zero, K.NoInput]
        verify after sourceEvents = K.check_segment subject binding start offered after []
          observations offered labels sourceEvents
    require "dynamic checker positive realized found/borrow segment"
      (verify (finish zero) observations)
    require "dynamic checker rejects changed actual target payload representation"
      (not (verify (finish one) observations))
    require "dynamic checker rejects changed source payload representation"
      (not (verify (finish zero) [K.ObsFound one zero, K.ObsBorrow zero one]))
    require "dynamic checker rejects well-formed wrong owner/loan indices"
      (not (verify (finish zero) [K.ObsFound zero one, K.ObsBorrow one zero]))
    require "dynamic checker rejects wrong source occurrence with correct K/I"
      (not (K.check_segment subject binding start [K.QFound bad zero] (finish zero) []
        observations [K.QFound bad zero] labels observations))
    require "payload code uses exact bytes rather than length"
      (case (K.payload_index [[zero], [one]] [zero],
             K.payload_index [[zero], [one]] [one]) of
        (Just x, Just y) -> not (K.exact_pair_match (zero, x) (zero, x) (zero, y) (zero, y))
        _ -> False)
    require "origin equality table rejects zero or multiple exact matches"
      (case (K.unique_index [False,False], K.unique_index [True,True]) of
        (Nothing, Nothing) -> True
        _ -> False)

acceptedTrace :: Text -> [CoreObservation] -> Bool
acceptedTrace payload events = case events of
  [CoreReadFound actual owner, CoreBorrowOpened owner' loan,
   CoreDigest owner'' loan' S.DigestAccepted, CoreBorrowClosed loan'',
   CoreReleased owner''', CoreDiagnostic "steve.get.commit", CoreReturnedUnit S.UnitFoundAccepted] ->
    actual == payload && owner == owner' && owner == owner'' && owner == owner'''
      && loan == loan' && loan == loan'' && owner /= loan
  _ -> False

rejectedTrace :: Text -> [CoreObservation] -> Bool
rejectedTrace payload events = case events of
  [CoreReadFound actual owner, CoreBorrowOpened owner' loan,
   CoreDigest owner'' loan' (S.DigestRejected "reason"), CoreBorrowClosed loan'',
   CoreReleased owner''', CoreReturnedUnit S.UnitFoundRejected] ->
    actual == payload && owner == owner' && owner == owner'' && owner == owner'''
      && loan == loan' && loan == loan'' && owner /= loan
  _ -> False
