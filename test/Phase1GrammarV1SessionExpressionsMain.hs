{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
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
