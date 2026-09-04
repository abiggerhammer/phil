{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Session
  ( SessionError (..)
  , exposeSessionHead
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SessionSemantics
  ( grammarV1PrimitiveSession
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-002 session select/offer recursion and continue preserve exact structure"
        sessionFamilyPreserved
    , test "SURF-002 session expression is admitted as a static actual"
        sessionStaticActualPreserved
    , test "SURF-003 select requires at least one branch" $
        expectReject emptySelectSource
    , test "SURF-003 session branch list rejects a trailing pipe" $
        expectReject trailingPipeSource
    , test "SURF-003 explicit branch params reject a trailing comma" $
        expectReject trailingParamCommaSource
    , test "SURF-008 primitive Grammar-v1 session structure routes exactly to Core"
        primitiveSessionRoutes
    , test "SURF-008 explicit empty branch payload syntax elaborates as no-payload Core"
        explicitEmptyBranchPayloadRoutes
    , test "SURF-008 primitive session bridge preserves competence boundaries"
        primitiveSessionCompetence
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sessionFamilyPreserved :: Either String ()
sessionFamilyPreserved = do
  protocol <- onlyProtocol sessionSource
  case grammarV1ProtocolRoles protocol of
    [Located _ firstRole, Located _ secondRole] -> do
      assert (locatedValue (grammarV1RoleSessionName firstRole) == "Client")
        "first role name was not Client"
      expectRecursiveSelect (grammarV1RoleSessionExpression firstRole)
      assert (locatedValue (grammarV1RoleSessionName secondRole) == "Server")
        "second role name was not Server"
      expectOffer (grammarV1RoleSessionExpression secondRole)
    roles -> Left ("expected two roles, got " <> show roles)

expectRecursiveSelect :: Located GrammarV1SessionExpression -> Either String ()
expectRecursiveSelect (Located _ session) = case session of
  GrammarV1SessionRecursive loopName body -> do
    assert (locatedValue loopName == "Loop") "recursive label was not Loop"
    case locatedValue body of
      GrammarV1SessionSelect branches -> case branches of
        [Located _ goBranch, Located _ stopBranch] -> do
          expectGoSelectBranch goBranch
          expectStopSelectBranch stopBranch
        other -> Left ("expected two select branches, got " <> show other)
      other -> Left ("expected select inside recursion, got " <> show other)
  other -> Left ("expected recursive session, got " <> show other)

expectGoSelectBranch :: GrammarV1SessionBranch -> Either String ()
expectGoSelectBranch branch = do
  assert (locatedValue (grammarV1SessionBranchLabel branch) == "Go")
    "select branch label was not Go"
  case grammarV1SessionBranchParams branch of
    Just [param] -> assertParam "x" "U8" param
    other -> Left ("expected one explicit Go parameter, got " <> show other)
  case grammarV1SessionBranchBoundary branch of
    Just boundary -> assertStaticReference "Wire" boundary
    Nothing -> Left "Go select branch lost its using boundary"
  case grammarV1SessionBranchGuard branch of
    Just guard -> assert (locatedValue guard == GrammarV1TrueProposition)
      "Go select guard was not true"
    Nothing -> Left "Go select branch lost its guard"
  case locatedValue (grammarV1SessionBranchContinuation branch) of
    GrammarV1SessionSend param Nothing Nothing continuation -> do
      assertParam "y" "U8" param
      case locatedValue continuation of
        GrammarV1SessionContinue loopName ->
          assert (locatedValue loopName == "Loop") "continue target was not Loop"
        other -> Left ("expected continue Loop, got " <> show other)
    other -> Left ("expected send continuation in Go branch, got " <> show other)

expectStopSelectBranch :: GrammarV1SessionBranch -> Either String ()
expectStopSelectBranch branch = do
  assert (locatedValue (grammarV1SessionBranchLabel branch) == "Stop")
    "select branch label was not Stop"
  assert (grammarV1SessionBranchParams branch == Just [])
    "explicit Stop() parameters were not preserved as Just []"
  assert (grammarV1SessionBranchBoundary branch == Nothing)
    "Stop select branch unexpectedly acquired a boundary"
  assert (grammarV1SessionBranchGuard branch == Nothing)
    "Stop select branch unexpectedly acquired a guard"
  assertEnd "Done" (grammarV1SessionBranchContinuation branch)

expectOffer :: Located GrammarV1SessionExpression -> Either String ()
expectOffer (Located _ session) = case session of
  GrammarV1SessionOffer branches -> case branches of
    [Located _ goBranch, Located _ stopBranch] -> do
      expectGoOfferBranch goBranch
      expectStopOfferBranch stopBranch
    other -> Left ("expected two offer branches, got " <> show other)
  other -> Left ("expected offer session, got " <> show other)

expectGoOfferBranch :: GrammarV1SessionBranch -> Either String ()
expectGoOfferBranch branch = do
  assert (locatedValue (grammarV1SessionBranchLabel branch) == "Go")
    "offer branch label was not Go"
  assert (grammarV1SessionBranchParams branch == Nothing)
    "omitted Go branch params were not preserved as Nothing"
  case grammarV1SessionBranchBoundary branch of
    Just boundary -> assertStaticReference "Wire" boundary
    Nothing -> Left "Go offer branch lost its using boundary"
  case grammarV1SessionBranchGuard branch of
    Just guard -> assert (locatedValue guard == GrammarV1FalseProposition)
      "Go offer guard was not false"
    Nothing -> Left "Go offer branch lost its guard"
  case locatedValue (grammarV1SessionBranchContinuation branch) of
    GrammarV1SessionReceive param Nothing Nothing continuation -> do
      assertParam "z" "U8" param
      assertEnd "Done" continuation
    other -> Left ("expected receive continuation in Go offer branch, got " <> show other)

expectStopOfferBranch :: GrammarV1SessionBranch -> Either String ()
expectStopOfferBranch branch = do
  assert (locatedValue (grammarV1SessionBranchLabel branch) == "Stop")
    "offer branch label was not Stop"
  assert (grammarV1SessionBranchParams branch == Nothing)
    "omitted Stop branch params were not preserved as Nothing"
  assert (grammarV1SessionBranchBoundary branch == Nothing)
    "Stop offer branch unexpectedly acquired a boundary"
  assert (grammarV1SessionBranchGuard branch == Nothing)
    "Stop offer branch unexpectedly acquired a guard"
  assertEnd "Done" (grammarV1SessionBranchContinuation branch)

sessionStaticActualPreserved :: Either String ()
sessionStaticActualPreserved = do
  alias <- onlyAlias "type SessionBox = Box[select { Go => end Done }];"
  case locatedValue (grammarV1TypeAliasTarget alias) of
    GrammarV1NamedType reference ->
      case grammarV1StaticReferenceArguments reference of
        [GrammarV1StaticSessionArgument session] ->
          case locatedValue session of
            GrammarV1SessionSelect [Located _ branch] -> do
              assert (locatedValue (grammarV1SessionBranchLabel branch) == "Go")
                "static session branch label was not Go"
              assert (grammarV1SessionBranchParams branch == Nothing)
                "static session branch unexpectedly acquired params"
              assertEnd "Done" (grammarV1SessionBranchContinuation branch)
            other -> Left ("expected static select session, got " <> show other)
        other -> Left ("expected one static session argument, got " <> show other)
    other -> Left ("expected named alias target, got " <> show other)

primitiveSessionRoutes :: Either String ()
primitiveSessionRoutes = do
  protocol <- onlyProtocol primitiveSessionSource
  client <- roleSession "Client" protocol
  server <- roleSession "Server" protocol
  let loop = Name "Loop"
      expectedClient = Rec loop (Select
        [ Branch
            { branchLabel = "Go"
            , branchPayload = Just (Name "x", TyUInt 8)
            , branchContinuation = Send (Name "y") (TyUInt 8) (SessionVar loop)
            }
        , Branch
            { branchLabel = "Stop"
            , branchPayload = Nothing
            , branchContinuation = End (Outcome "Done")
            }
        ])
      expectedServer = Offer
        [ Branch
            { branchLabel = "Go"
            , branchPayload = Nothing
            , branchContinuation = Receive (Name "z") (TyUInt 8) (End (Outcome "Done"))
            }
        , Branch
            { branchLabel = "Stop"
            , branchPayload = Nothing
            , branchContinuation = End (Outcome "Done")
            }
        ]
  assert
    (grammarV1PrimitiveSession (locatedValue client) == Just expectedClient)
    "primitive client session did not preserve exact Core structure"
  assert
    (grammarV1PrimitiveSession (locatedValue server) == Just expectedServer)
    "primitive server session did not preserve exact Core structure"

  unguarded <- roleSession "A" =<< onlyProtocol unguardedRecursionSource
  case grammarV1PrimitiveSession (locatedValue unguarded) of
    Just coreSession ->
      assert
        (exposeSessionHead coreSession == Left (UnguardedRecursion (Name "Loop")))
        "unguarded recursion was not preserved for the existing Core checker"
    Nothing -> Left "bound unguarded recursion was rejected before Core could check it"

explicitEmptyBranchPayloadRoutes :: Either String ()
explicitEmptyBranchPayloadRoutes = do
  explicit <- firstProtocolRole =<< onlyProtocol explicitEmptyBranchSource
  omitted <- firstProtocolRole =<< onlyProtocol omittedEmptyBranchSource
  case locatedValue explicit of
    GrammarV1SessionSelect [Located _ branch] ->
      assert
        (grammarV1SessionBranchParams branch == Just [])
        "parser did not preserve explicit empty branch payload syntax"
    other -> Left ("expected explicit-empty select branch, got " <> show other)
  case locatedValue omitted of
    GrammarV1SessionSelect [Located _ branch] ->
      assert
        (grammarV1SessionBranchParams branch == Nothing)
        "parser did not preserve omitted branch payload syntax"
    other -> Left ("expected omitted-payload select branch, got " <> show other)
  let expected = Select
        [ Branch
            { branchLabel = "Stop"
            , branchPayload = Nothing
            , branchContinuation = End (Outcome "Done")
            }
        ]
      explicitCore = grammarV1PrimitiveSession (locatedValue explicit)
      omittedCore = grammarV1PrimitiveSession (locatedValue omitted)
  assert
    (explicitCore == Just expected)
    "explicit empty branch payload did not elaborate as a no-payload Core branch"
  assert
    (explicitCore == omittedCore)
    "explicit empty and omitted branch payload syntax diverged after elaboration"

primitiveSessionCompetence :: Either String ()
primitiveSessionCompetence = do
  staticRef <- firstProtocolRole =<< onlyProtocol staticReferenceSource
  codec <- firstProtocolRole =<< onlyProtocol codecSessionSource
  guarded <- firstProtocolRole =<< onlyProtocol guardedSessionSource
  richPayload <- firstProtocolRole =<< onlyProtocol richPayloadSource
  multiPayload <- firstProtocolRole =<< onlyProtocol multiPayloadBranchSource
  unbound <- firstProtocolRole =<< onlyProtocol unboundContinueSource
  duplicateBinder <- firstProtocolRole =<< onlyProtocol duplicateBinderSource
  mapM_ expectNothing
    [ ("static session reference", staticRef)
    , ("codec-bearing session", codec)
    , ("guard-bearing session", guarded)
    , ("nonprimitive message payload", richPayload)
    , ("multi-parameter branch payload", multiPayload)
    , ("unbound continue", unbound)
    , ("duplicate dependent binder", duplicateBinder)
    ]
  where
    expectNothing (label, session) =
      assert
        (grammarV1PrimitiveSession (locatedValue session) == Nothing)
        (label <> " escaped the primitive session competence boundary")

roleSession
  :: Text.Text
  -> GrammarV1ProtocolDecl
  -> Either String (Located GrammarV1SessionExpression)
roleSession expected protocol =
  case
    [ grammarV1RoleSessionExpression role
    | Located _ role <- grammarV1ProtocolRoles protocol
    , locatedValue (grammarV1RoleSessionName role) == expected
    ] of
    [session] -> Right session
    sessions -> Left
      ("expected one role " <> Text.unpack expected <> ", got " <> show (length sessions))

firstProtocolRole :: GrammarV1ProtocolDecl -> Either String (Located GrammarV1SessionExpression)
firstProtocolRole protocol =
  case grammarV1ProtocolRoles protocol of
    Located _ role : _ -> Right (grammarV1RoleSessionExpression role)
    [] -> Left "expected at least one protocol role"

assertParam
  :: Text.Text
  -> Text.Text
  -> Located GrammarV1TermParam
  -> Either String ()
assertParam expectedName expectedWidth (Located _ param) = do
  assert (locatedValue (grammarV1TermParamName param) == expectedName)
    ("unexpected parameter name " <> show (locatedValue (grammarV1TermParamName param)))
  assert
    (locatedValue (grammarV1TermParamType param) == GrammarV1UnsignedType expectedWidth)
    ("unexpected parameter type " <> show (locatedValue (grammarV1TermParamType param)))

assertStaticReference :: Text.Text -> Located GrammarV1StaticReference -> Either String ()
assertStaticReference expected (Located _ reference) = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
    ("expected static reference " <> Text.unpack expected)
  assert (null (grammarV1StaticReferenceArguments reference))
    "static reference unexpectedly had arguments"

assertEnd :: Text.Text -> Located GrammarV1SessionExpression -> Either String ()
assertEnd expected (Located _ session) = case session of
  GrammarV1SessionEnd label ->
    assert (locatedValue label == expected)
      ("expected end " <> Text.unpack expected <> ", got " <> show (locatedValue label))
  other -> Left ("expected end session, got " <> show other)

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "session-family" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

onlyAlias :: Text.Text -> Either String GrammarV1TypeAliasDecl
onlyAlias source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "session-static-actual" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1TypeAliasDeclaration alias -> Right alias
      other -> Left ("expected type alias declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "session-reject" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

sessionSource :: Text.Text
sessionSource = Text.unlines
  [ "protocol P {"
  , "  role Client = recursive Loop = select {"
  , "    Go(x : U8) using Wire when true => send (y : U8) then continue Loop"
  , "    | Stop() => end Done"
  , "  };"
  , "  role Server = offer {"
  , "    Go using Wire when false => receive (z : U8) then end Done"
  , "    | Stop => end Done"
  , "  };"
  , "}"
  ]

primitiveSessionSource :: Text.Text
primitiveSessionSource = Text.unlines
  [ "protocol P {"
  , "  role Client = recursive Loop = select {"
  , "    Go(x : U8) => send (y : U8) then continue Loop"
  , "    | Stop => end Done"
  , "  };"
  , "  role Server = offer {"
  , "    Go => receive (z : U8) then end Done"
  , "    | Stop => end Done"
  , "  };"
  , "}"
  ]

unguardedRecursionSource :: Text.Text
unguardedRecursionSource = Text.unlines
  [ "protocol P {"
  , "  role A = recursive Loop = continue Loop;"
  , "  role B = end Done;"
  , "}"
  ]

staticReferenceSource :: Text.Text
staticReferenceSource = Text.unlines
  [ "protocol P {"
  , "  role A = Next;"
  , "  role B = end Done;"
  , "}"
  ]

codecSessionSource :: Text.Text
codecSessionSource = Text.unlines
  [ "protocol P {"
  , "  role A = send (x : U8) using Wire then end Done;"
  , "  role B = end Done;"
  , "}"
  ]

guardedSessionSource :: Text.Text
guardedSessionSource = Text.unlines
  [ "protocol P {"
  , "  role A = receive (x : U8) when true then end Done;"
  , "  role B = end Done;"
  , "}"
  ]

richPayloadSource :: Text.Text
richPayloadSource = Text.unlines
  [ "protocol P {"
  , "  role A = send (payload : Bytes[1]) then end Done;"
  , "  role B = end Done;"
  , "}"
  ]

explicitEmptyBranchSource :: Text.Text
explicitEmptyBranchSource = Text.unlines
  [ "protocol P {"
  , "  role A = select { Stop() => end Done };"
  , "  role B = end Done;"
  , "}"
  ]

omittedEmptyBranchSource :: Text.Text
omittedEmptyBranchSource = Text.unlines
  [ "protocol P {"
  , "  role A = select { Stop => end Done };"
  , "  role B = end Done;"
  , "}"
  ]

multiPayloadBranchSource :: Text.Text
multiPayloadBranchSource = Text.unlines
  [ "protocol P {"
  , "  role A = offer { Pair(x : U8, y : Bool) => end Done };"
  , "  role B = end Done;"
  , "}"
  ]

unboundContinueSource :: Text.Text
unboundContinueSource = Text.unlines
  [ "protocol P {"
  , "  role A = continue Missing;"
  , "  role B = end Done;"
  , "}"
  ]

duplicateBinderSource :: Text.Text
duplicateBinderSource = Text.unlines
  [ "protocol P {"
  , "  role A = send (x : U8) then receive (x : Bool) then end Done;"
  , "  role B = end Done;"
  , "}"
  ]

emptySelectSource :: Text.Text
emptySelectSource = Text.unlines
  [ "protocol P {"
  , "  role A = select {};"
  , "  role B = S;"
  , "}"
  ]

trailingPipeSource :: Text.Text
trailingPipeSource = Text.unlines
  [ "protocol P {"
  , "  role A = select { Go => end Done | };"
  , "  role B = S;"
  , "}"
  ]

trailingParamCommaSource :: Text.Text
trailingParamCommaSource = Text.unlines
  [ "protocol P {"
  , "  role A = offer { Go(x : U8,) => end Done };"
  , "  role B = S;"
  , "}"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
