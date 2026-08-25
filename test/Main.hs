{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , CheckerError (..)
  , completeComponent
  , emitObligation
  , emptyCheckState
  )
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , consumeAffine
  , consumeLinear
  , emptyContext
  , endSharedLoan
  , ensureComplete
  , insertBinding
  , joinContinuing
  , startSharedLoan
  , useUnrestricted
  )
import Phil.Core.Session
  ( MessageSpec (..)
  , SessionAction (..)
  , SessionError (..)
  , SessionStep (..)
  , closeEndpoint
  , dualSession
  , exposeSessionHead
  , offerEndpoint
  , receiveEndpoint
  , selectEndpoint
  , sendEndpoint
  )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity (..)
  , ArchitectureRealizationDescriptor (..)
  , ArchitectureRealizationIdentity (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , InstanceKey (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  , deriveArchitectureInstanceIdentity
  , deriveArchitectureRealizationIdentity
  , deriveDeclarationIdentity
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Mode (..)
  , Name (Name)
  , Obligation (Obligation)
  , ObligationId (ObligationId)
  , Outcome (Outcome)
  , Proposition (Atom)
  , RefTerm (RefVar)
  , Session (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Γ values are reusable" testUnrestrictedReuse
    , test "A values are consumable at most once" testAffineAtMostOnce
    , test "shared loan blocks owner consumption" testSharedLoanBlocksConsumption
    , test "Δ mismatch rejects branch join" testLinearBranchMismatch
    , test "A join conservatively forgets consumed capability" testAffineJoinForgets
    , test "complete component rejects leftover Δ" testLinearResidueRejected
    , test "obligation IDs reject conflicting reuse" testObligationIdConflict
    , test "send consumes old endpoint and creates declared successor" testSendProgression
    , test "receive exposes message spec and declared successor" testReceiveProgression
    , test "wrong session polarity is rejected" testWrongPolarity
    , test "select exposes branch payload and continuation" testSelectProgression
    , test "offer exposes peer-selected branch payload and continuation" testOfferProgression
    , test "unknown session labels are rejected" testUnknownLabel
    , test "duplicate session labels invalidate the whole choice" testDuplicateLabel
    , test "offer cannot be used on internal choice" testOfferWrongPolarity
    , test "successor endpoint must have a fresh identity" testFreshSuccessor
    , test "close consumes endpoint only at matching outcome" testCloseProgression
    , test "guarded recursion exposes one communication head" testGuardedRecursion
    , test "unguarded recursion is rejected" testUnguardedRecursion
    , test "session duality is involutive" testDuality
    , test "canonical semantic records ignore insertion order" testCanonicalRecordOrder
    , test "canonical semantic sets ignore insertion order" testCanonicalSetOrder
    , test "declaration rename and module move preserve semantic identity" testPresentationDoesNotIdentify
    , test "public contract changes revise interface and definition" testInterfaceChangeRevises
    , test "definition replacement may preserve the public interface" testDefinitionChangePreservesInterface
    , test "equal-looking architecture occurrences remain distinct" testDistinctArchitectureOccurrences
    , test "unrelated sibling edits do not rekey an unaffected child" testSiblingEditDoesNotRekeyChild
    , test "realization replacement preserves instance identity" testRealizationReplacement
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

nty :: Text -> Ty
nty = TyOpaque

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testUnrestrictedReuse :: Either String ()
testUnrestrictedReuse = do
  context0 <- mapLeft show $ insertBinding Unrestricted (name "policy") (nty "Policy") emptyContext
  (_, context1) <- mapLeft show $ useUnrestricted (name "policy") context0
  (_, context2) <- mapLeft show $ useUnrestricted (name "policy") context1
  assert (context2 == context0) "unrestricted use changed Γ"

testAffineAtMostOnce :: Either String ()
testAffineAtMostOnce = do
  context0 <- mapLeft show $ insertBinding Affine (name "cap") (nty "Capability") emptyContext
  (_, context1) <- mapLeft show $ consumeAffine (name "cap") context0
  case consumeAffine (name "cap") context1 of
    Left (UnknownBinding _) -> Right ()
    other -> Left ("second affine consumption was not rejected as expected: " ++ show other)

testSharedLoanBlocksConsumption :: Either String ()
testSharedLoanBlocksConsumption = do
  context0 <- mapLeft show $ insertBinding Linear (name "payload") (nty "Bytes[4096]") emptyContext
  context1 <- mapLeft show $ startSharedLoan (name "payload") context0
  case consumeLinear (name "payload") context1 of
    Left (OwnerBorrowed _) -> pure ()
    other -> Left ("borrowed owner consumption was not rejected: " ++ show other)
  context2 <- mapLeft show $ endSharedLoan (name "payload") context1
  (_, context3) <- mapLeft show $ consumeLinear (name "payload") context2
  mapLeft show $ ensureComplete context3

testLinearBranchMismatch :: Either String ()
testLinearBranchMismatch = do
  incoming <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  (_, consumed) <- mapLeft show $ consumeLinear (name "endpoint") incoming
  case joinContinuing [incoming, consumed] of
    Left (LinearBranchMismatch _ _) -> Right ()
    other -> Left ("linear branch mismatch was not rejected: " ++ show other)

testAffineJoinForgets :: Either String ()
testAffineJoinForgets = do
  incoming <- mapLeft show $ insertBinding Affine (name "cap") (nty "Capability") emptyContext
  (_, consumed) <- mapLeft show $ consumeAffine (name "cap") incoming
  joined <- mapLeft show $ joinContinuing [incoming, consumed]
  assert (Map.null (affineBindings joined)) "affine capability survived a join where one branch consumed it"

testLinearResidueRejected :: Either String ()
testLinearResidueRejected = do
  context <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  let state = emptyCheckState { resourceContext = context }
  case completeComponent state of
    Left (ResourceError (UnconsumedLinearResources _)) -> Right ()
    other -> Left ("leftover linear resource was not rejected: " ++ show other)

testObligationIdConflict :: Either String ()
testObligationIdConflict = do
  let first = Obligation
        (ObligationId "upload.begin.policy")
        (Atom "BeginPolicy" [RefVar (name "κ1"), RefVar (name "begin")])
        "server.phil:begin"
        "upload-server"
        "before Accept"
      conflicting = Obligation
        (ObligationId "upload.begin.policy")
        (Atom "BeginPolicy" [RefVar (name "κ2"), RefVar (name "begin")])
        "server.phil:begin"
        "upload-server"
        "before Accept"
  state1 <- mapLeft show $ emitObligation first emptyCheckState
  _ <- mapLeft show $ emitObligation first state1
  case emitObligation conflicting state1 of
    Left (ConflictingObligationId _ _) -> Right ()
    other -> Left ("conflicting obligation identity was not rejected: " ++ show other)

testSendProgression :: Either String ()
testSendProgression = do
  let success = Outcome "success"
      session = Send (name "payload") (nty "Payload") (End success)
      e0 = name "e0"
      e1 = name "e1"
  context0 <- endpointContext e0 session
  step <- mapLeft show $ sendEndpoint e0 e1 context0
  assert
    (stepMessage step == Just (MessageSpec (name "payload") (nty "Payload")))
    "send did not expose its message binder/type"
  assert
    (Map.lookup e1 (linearBindings (stepContext step)) == Just (TyEndpoint (End success)))
    "send successor endpoint has the wrong continuation"
  case consumeLinear e0 (stepContext step) of
    Left (UnknownBinding _) -> Right ()
    other -> Left ("consumed endpoint remained usable after send: " ++ show other)

testReceiveProgression :: Either String ()
testReceiveProgression = do
  let cancelled = Outcome "cancelled"
      session = Receive (name "selected") (nty "U16") (End cancelled)
  context <- endpointContext (name "e0") session
  step <- mapLeft show $ receiveEndpoint (name "e0") (name "e1") context
  assert
    (stepMessage step == Just (MessageSpec (name "selected") (nty "U16")))
    "receive did not expose its message binder/type"
  assert
    (stepSuccessor step == Just (name "e1", End cancelled))
    "receive did not expose its declared continuation"

testWrongPolarity :: Either String ()
testWrongPolarity = do
  let session = Send (name "payload") (nty "Payload") (End (Outcome "success"))
  context <- endpointContext (name "e0") session
  case receiveEndpoint (name "e0") (name "e1") context of
    Left (UnexpectedSessionAction ReceiveAction _) -> Right ()
    other -> Left ("receive at a send head was not rejected: " ++ show other)

testSelectProgression :: Either String ()
testSelectProgression = do
  let success = Outcome "success"
      failure = Outcome "failure"
      session = Select
        [ Branch "version" (Just (name "selected", nty "U16")) (End success)
        , Branch "unsupported" Nothing (End failure)
        ]
  context <- endpointContext (name "e0") session
  step <- mapLeft show $ selectEndpoint (name "e0") (name "e1") "version" context
  assert
    (stepMessage step == Just (MessageSpec (name "selected") (nty "U16")))
    "selected branch payload was not exposed"
  assert
    (stepSuccessor step == Just (name "e1", End success))
    "selected branch did not produce its declared continuation"

testOfferProgression :: Either String ()
testOfferProgression = do
  let cancelled = Outcome "cancelled"
      success = Outcome "success"
      session = Offer
        [ Branch "cancel" Nothing (End cancelled)
        , Branch "payload" (Just (name "body", nty "Bytes[n]")) (End success)
        ]
  context <- endpointContext (name "e0") session
  step <- mapLeft show $ offerEndpoint (name "e0") (name "e1") "payload" context
  assert
    (stepMessage step == Just (MessageSpec (name "body") (nty "Bytes[n]")))
    "offered branch payload was not exposed"
  assert
    (stepSuccessor step == Just (name "e1", End success))
    "offered branch did not produce its declared continuation"

testUnknownLabel :: Either String ()
testUnknownLabel = do
  let session = Select
        [ Branch "accepted" Nothing (End (Outcome "success"))
        , Branch "rejected" Nothing (End (Outcome "failure"))
        ]
  context <- endpointContext (name "e0") session
  case selectEndpoint (name "e0") (name "e1") "bogus" context of
    Left (UnknownSessionLabel label labels) ->
      assert
        (label == "bogus" && labels == ["accepted", "rejected"])
        "unknown-label diagnostic lost the requested or declared labels"
    other -> Left ("unknown select label was not rejected: " ++ show other)

testDuplicateLabel :: Either String ()
testDuplicateLabel = do
  let session = Select
        [ Branch "safe" Nothing (End (Outcome "success"))
        , Branch "same" Nothing (End (Outcome "success"))
        , Branch "same" Nothing (End (Outcome "failure"))
        ]
  context <- endpointContext (name "e0") session
  case selectEndpoint (name "e0") (name "e1") "safe" context of
    Left (DuplicateSessionLabel label) -> assert (label == "same") "wrong duplicate label reported"
    other -> Left ("malformed choice with duplicate labels was allowed to progress: " ++ show other)

testOfferWrongPolarity :: Either String ()
testOfferWrongPolarity = do
  let session = Select [Branch "continue" Nothing (End (Outcome "success"))]
  context <- endpointContext (name "e0") session
  case offerEndpoint (name "e0") (name "e1") "continue" context of
    Left (UnexpectedSessionAction (OfferAction label) _) ->
      assert (label == "continue") "wrong offer label reported"
    other -> Left ("offer at an internal-choice head was not rejected: " ++ show other)

testFreshSuccessor :: Either String ()
testFreshSuccessor = do
  let e0 = name "e0"
      session = Send (name "payload") (nty "Payload") (End (Outcome "success"))
  context <- endpointContext e0 session
  case sendEndpoint e0 e0 context of
    Left (SuccessorReusesEndpointName endpoint) ->
      assert (endpoint == e0) "fresh-successor error reported the wrong endpoint"
    other -> Left ("endpoint progression allowed the consumed endpoint identity to be reused: " ++ show other)

testCloseProgression :: Either String ()
testCloseProgression = do
  let success = Outcome "success"
      failure = Outcome "failure"
      e0 = name "e0"
  context <- endpointContext e0 (End success)
  step <- mapLeft show $ closeEndpoint e0 success context
  assert (Map.null (linearBindings (stepContext step))) "close left a successor endpoint"
  contextAgain <- endpointContext e0 (End success)
  case closeEndpoint e0 failure contextAgain of
    Left (CloseOutcomeMismatch expected actual) ->
      assert (expected == success && actual == failure) "close mismatch reported the wrong outcomes"
    other -> Left ("mismatched close outcome was not rejected: " ++ show other)

testGuardedRecursion :: Either String ()
testGuardedRecursion = do
  let x = name "X"
      loop = Rec x (Receive (name "msg") (nty "Message") (SessionVar x))
  case exposeSessionHead loop of
    Right (Receive binder messageTy continuation) -> do
      assert (binder == name "msg") "guarded recursion exposed the wrong binder"
      assert (messageTy == nty "Message") "guarded recursion exposed the wrong message type"
      assert (continuation == loop) "guarded recursive continuation did not reclose the recursion"
    other -> Left ("guarded recursion did not expose a receive head: " ++ show other)

testUnguardedRecursion :: Either String ()
testUnguardedRecursion = do
  let x = name "X"
  case exposeSessionHead (Rec x (SessionVar x)) of
    Left (UnguardedRecursion variable) -> assert (variable == x) "wrong recursion variable reported"
    other -> Left ("unguarded recursion was not rejected: " ++ show other)

testDuality :: Either String ()
testDuality = do
  let session = Send
        (name "hello")
        (nty "Frame[Hello]")
        (Select
          [ Branch "unsupported" Nothing (End (Outcome "failure"))
          , Branch "version" (Just (name "selected", nty "U16")) (End (Outcome "success"))
          ])
  assert (dualSession (dualSession session) == session) "dual . dual changed the session type"

testCanonicalRecordOrder :: Either String ()
testCanonicalRecordOrder =
  let left = SemanticRecord (Map.fromList
        [ ("provider", SemanticAtom "BlobProvider")
        , ("authority", SemanticAtom "write")
        ])
      right = SemanticRecord (Map.fromList
        [ ("authority", SemanticAtom "write")
        , ("provider", SemanticAtom "BlobProvider")
        ])
  in assert
      (canonicalSemanticForm left == canonicalSemanticForm right)
      "record insertion order changed the canonical semantic form"

testCanonicalSetOrder :: Either String ()
testCanonicalSetOrder =
  let left = SemanticUnordered (Set.fromList
        [ SemanticAtom "read"
        , SemanticAtom "write"
        ])
      right = SemanticUnordered (Set.fromList
        [ SemanticAtom "write"
        , SemanticAtom "read"
        ])
  in assert
      (canonicalSemanticForm left == canonicalSemanticForm right)
      "set insertion order changed the canonical semantic form"

testPresentationDoesNotIdentify :: Either String ()
testPresentationDoesNotIdentify =
  let first = deriveDeclarationIdentity
        (baseDeclaration (DeclarationPresentation "blob" ["Steve"]))
      renamed = deriveDeclarationIdentity
        (baseDeclaration (DeclarationPresentation "object_store" ["Storage", "Steve"]))
  in assert
      (first == renamed)
      "human rename or module move changed declaration semantic identity"

testInterfaceChangeRevises :: Either String ()
testInterfaceChangeRevises =
  let original = deriveDeclarationIdentity
        (baseDeclaration (DeclarationPresentation "blob" ["Steve"]))
      changedDescriptor =
        (baseDeclaration (DeclarationPresentation "blob" ["Steve"]))
          { declarationInterfaceSemantics = SemanticRecord (Map.fromList
              [ ("provider", SemanticAtom "BlobProvider")
              , ("authority", SemanticAtom "read-write")
              , ("failure", SemanticAtom "explicit")
              ])
          }
      changed = deriveDeclarationIdentity changedDescriptor
  in do
    assert
      (identityDeclarationKey original == identityDeclarationKey changed)
      "public contract revision changed stable declaration lineage"
    assert
      (identityInterfaceRevision original /= identityInterfaceRevision changed)
      "public contract change did not revise InterfaceRevision"
    assert
      (identityDefinitionRevision original /= identityDefinitionRevision changed)
      "public contract change did not revise DefinitionRevision"

testDefinitionChangePreservesInterface :: Either String ()
testDefinitionChangePreservesInterface =
  let originalDescriptor = baseDeclaration (DeclarationPresentation "blob" ["Steve"])
      replacementDescriptor = originalDescriptor
        { declarationDefinitionSemantics = SemanticRecord (Map.fromList
            [ ("algorithm", SemanticAtom "install-if-absent-v2")
            , ("cleanup", SemanticAtom "release-on-all-failures")
            ])
        }
      original = deriveDeclarationIdentity originalDescriptor
      replacement = deriveDeclarationIdentity replacementDescriptor
  in do
    assert
      (identityInterfaceRevision original == identityInterfaceRevision replacement)
      "definition-only rewrite changed the public interface revision"
    assert
      (identityDefinitionRevision original /= identityDefinitionRevision replacement)
      "definition-only rewrite failed to change DefinitionRevision"

testDistinctArchitectureOccurrences :: Either String ()
testDistinctArchitectureOccurrences =
  let declarationIdentity = deriveDeclarationIdentity
        (baseDeclaration (DeclarationPresentation "blob" ["Steve"]))
      primary = deriveArchitectureInstanceIdentity
        (baseInstance declarationIdentity (InstanceKey "steve.primary-store"))
      backup = deriveArchitectureInstanceIdentity
        (baseInstance declarationIdentity (InstanceKey "steve.backup-store"))
  in do
    assert
      (identityInstanceKey primary /= identityInstanceKey backup)
      "equal-looking occurrences collapsed to one InstanceKey"
    assert
      (identityInstanceRevision primary /= identityInstanceRevision backup)
      "equal-looking occurrences collapsed to one InstanceRevision"

testSiblingEditDoesNotRekeyChild :: Either String ()
testSiblingEditDoesNotRekeyChild =
  let parentPresentation = DeclarationPresentation "steve" ["Steve"]
      parentBefore = deriveDeclarationIdentity DeclarationDescriptor
        { declarationPresentation = parentPresentation
        , declarationKey = DeclarationKey "architecture.steve"
        , declarationInterfaceSemantics = SemanticAtom "SteveArchitecture"
        , declarationDefinitionSemantics = SemanticRecord (Map.fromList
            [ ("store", SemanticAtom "v1")
            , ("metrics", SemanticAtom "v1")
            ])
        }
      parentAfter = deriveDeclarationIdentity DeclarationDescriptor
        { declarationPresentation = parentPresentation
        , declarationKey = DeclarationKey "architecture.steve"
        , declarationInterfaceSemantics = SemanticAtom "SteveArchitecture"
        , declarationDefinitionSemantics = SemanticRecord (Map.fromList
            [ ("store", SemanticAtom "v1")
            , ("metrics", SemanticAtom "v2")
            ])
        }
      childDeclaration = deriveDeclarationIdentity
        (baseDeclaration (DeclarationPresentation "store" ["Steve"]))
      childBefore = deriveArchitectureInstanceIdentity
        (baseInstance childDeclaration (InstanceKey "steve.store"))
      childAfter = deriveArchitectureInstanceIdentity
        (baseInstance childDeclaration (InstanceKey "steve.store"))
  in do
    assert
      (identityDefinitionRevision parentBefore /= identityDefinitionRevision parentAfter)
      "sibling edit fixture did not revise the containing architecture definition"
    assert
      (childBefore == childAfter)
      "containing architecture revision recursively rekeyed an unaffected child"

testRealizationReplacement :: Either String ()
testRealizationReplacement =
  let declarationIdentity = deriveDeclarationIdentity
        (baseDeclaration (DeclarationPresentation "blob" ["Steve"]))
      instanceIdentity = deriveArchitectureInstanceIdentity
        (baseInstance declarationIdentity (InstanceKey "steve.store"))
      first = deriveArchitectureRealizationIdentity ArchitectureRealizationDescriptor
        { realizationInstanceIdentity = instanceIdentity
        , realizationSemantics = SemanticRecord (Map.fromList
            [ ("implementation", SemanticAtom "filesystem-v1")
            , ("target", SemanticAtom "host")
            ])
        }
      replacement = deriveArchitectureRealizationIdentity ArchitectureRealizationDescriptor
        { realizationInstanceIdentity = instanceIdentity
        , realizationSemantics = SemanticRecord (Map.fromList
            [ ("implementation", SemanticAtom "object-store-v1")
            , ("target", SemanticAtom "host")
            ])
        }
  in do
    assert
      (identityRealizationRevision first /= identityRealizationRevision replacement)
      "provider realization replacement did not revise RealizationRevision"
    assert
      (realizationInstanceIdentity ArchitectureRealizationDescriptor
        { realizationInstanceIdentity = instanceIdentity
        , realizationSemantics = SemanticAtom "unused"
        } == instanceIdentity)
      "realization construction changed the abstract ArchitectureInstance identity"

baseDeclaration :: DeclarationPresentation -> DeclarationDescriptor
baseDeclaration presentation = DeclarationDescriptor
  { declarationPresentation = presentation
  , declarationKey = DeclarationKey "provider.blob"
  , declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "BlobProvider")
      , ("authority", SemanticAtom "read-write")
      ])
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("algorithm", SemanticAtom "install-if-absent-v1")
      , ("cleanup", SemanticAtom "release-on-failure")
      ])
  }

baseInstance
  :: DeclarationIdentity
  -> InstanceKey
  -> ArchitectureInstanceDescriptor
baseInstance declarationIdentity instanceKey = ArchitectureInstanceDescriptor
  { architectureInstanceKey = instanceKey
  , architectureParentInstanceKey = Just (InstanceKey "architecture.steve")
  , architectureDeclarationIdentity = declarationIdentity
  , architectureStaticBindings = Map.fromList
      [ ("contract", SemanticAtom "BlobProvider")
      , ("mode", SemanticAtom "read-write")
      ]
  }

endpointContext :: Name -> Session -> Either String ResourceContext
endpointContext endpoint session =
  mapLeft show $ insertBinding Linear endpoint (TyEndpoint session) emptyContext

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
