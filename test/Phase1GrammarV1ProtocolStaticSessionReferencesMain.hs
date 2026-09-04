{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolSessionParameterReferences
  ( GrammarV1ProtocolSessionParameterReferenceError (..)
  , GrammarV1ResolvedProtocolSessionParameter (..)
  , GrammarV1ResolvedProtocolSessionRoleReference (..)
  , grammarV1ResolvedSessionParameterRoleReferences
  )
import Phil.Surface.GrammarV1.ProtocolStaticSessionReferences
  ( grammarV1ClosedProtocolRoleSessionReferences
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed protocol role session references preserve unresolved static identity"
        closedReferencesPreserved
    , test "SURF-008 protocol display spelling cannot resolve static session identity"
        protocolRenameIsNonsemantic
    , test "SURF-008 static session reference projection preserves duplicate role spelling"
        duplicateRoleSpellingRemainsVisible
    , test "SURF-008 static session references remain unresolved before category checking"
        unresolvedCategoryRemainsUnresolved
    , test "SURF-008 richer static session reference forms remain fail-closed"
        competenceBoundaries
    , test "SURF-008 Session-parameter role references consume exact binder evidence"
        sessionParameterReferencesConsumeBinderEvidence
    , test "SURF-008 Session-parameter references reject missing, wrong, or foreign binder evidence"
        sessionParameterEvidenceBoundaries
    , test "SURF-008 Session-parameter reference routing preserves its competence wall"
        sessionParameterCompetenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closedReferencesPreserved :: Either String ()
closedReferencesPreserved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol P {"
    , "  role Client = sessions.client.Flow;"
    , "  role Server = sessions.server.Flow;"
    , "}"
    ]
  let expected =
        ( ( ProtocolRoleKey "Client"
          , ReferencedGenericStaticActual "sessions.client.Flow"
          )
        , ( ProtocolRoleKey "Server"
          , ReferencedGenericStaticActual "sessions.server.Flow"
          )
        )
  assert
    (grammarV1ClosedProtocolRoleSessionReferences protocol == Just expected)
    "qualified static session references changed spelling, role order, or unresolved identity"

protocolRenameIsNonsemantic :: Either String ()
protocolRenameIsNonsemantic = do
  first <- onlyProtocol $ Text.unlines
    [ "protocol FirstPresentation {"
    , "  role Client = sessions.Client;"
    , "  role Server = sessions.Server;"
    , "}"
    ]
  renamed <- onlyProtocol $ Text.unlines
    [ "protocol RenamedPresentation {"
    , "  role Client = sessions.Client;"
    , "  role Server = sessions.Server;"
    , "}"
    ]
  assert
    ( grammarV1ClosedProtocolRoleSessionReferences first
        == grammarV1ClosedProtocolRoleSessionReferences renamed
    )
    "protocol declaration display-name change leaked into unresolved role session references"

duplicateRoleSpellingRemainsVisible :: Either String ()
duplicateRoleSpellingRemainsVisible = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Duplicate {"
    , "  role Same = sessions.Left;"
    , "  role Same = sessions.Right;"
    , "}"
    ]
  let expected =
        ( (ProtocolRoleKey "Same", ReferencedGenericStaticActual "sessions.Left")
        , (ProtocolRoleKey "Same", ReferencedGenericStaticActual "sessions.Right")
        )
  assert
    (grammarV1ClosedProtocolRoleSessionReferences protocol == Just expected)
    "static-session projection normalized or rejected duplicate role spelling before competent role checking"

unresolvedCategoryRemainsUnresolved :: Either String ()
unresolvedCategoryRemainsUnresolved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Unresolved {"
    , "  role A = maybe.NotASession;"
    , "  role B = maybe.AlsoUnknown;"
    , "}"
    ]
  let expected =
        ( (ProtocolRoleKey "A", ReferencedGenericStaticActual "maybe.NotASession")
        , (ProtocolRoleKey "B", ReferencedGenericStaticActual "maybe.AlsoUnknown")
        )
  assert
    (grammarV1ClosedProtocolRoleSessionReferences protocol == Just expected)
    "unresolved static session projection invented category-resolution authority"

competenceBoundaries :: Either String ()
competenceBoundaries = do
  inline <- onlyProtocol $ Text.unlines
    [ "protocol Inline {"
    , "  role A = send (x : U8) then end Done;"
    , "  role B = receive (y : U8) then end Done;"
    , "}"
    ]
  mixed <- onlyProtocol $ Text.unlines
    [ "protocol Mixed {"
    , "  role A = sessions.A;"
    , "  role B = end Done;"
    , "}"
    ]
  generic <- onlyProtocol $ Text.unlines
    [ "protocol Generic[S : Session] {"
    , "  role A = S;"
    , "  role B = S;"
    , "}"
    ]
  required <- onlyProtocol $ Text.unlines
    [ "protocol Required requires { proposition true; } {"
    , "  role A = sessions.A;"
    , "  role B = sessions.B;"
    , "}"
    ]
  specialized <- onlyProtocol $ Text.unlines
    [ "protocol Specialized {"
    , "  role A = sessions.Flow[U8];"
    , "  role B = sessions.Flow[U8];"
    , "}"
    ]
  mapM_ (\(label, protocol) ->
    assert
      (grammarV1ClosedProtocolRoleSessionReferences protocol == Nothing)
      (label <> " escaped the static-session-reference competence wall"))
    [ ("inline role body", inline)
    , ("mixed inline/reference roles", mixed)
    , ("generic Session binder", generic)
    , ("requirement-bearing protocol", required)
    , ("specialized session reference", specialized)
    ]

sessionParameterReferencesConsumeBinderEvidence :: Either String ()
sessionParameterReferencesConsumeBinderEvidence = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Generic[S : Session] {"
    , "  role Client = S;"
    , "  role Server = S;"
    , "}"
    ]
  renamed <- onlyProtocol $ Text.unlines
    [ "protocol Renamed[Flow : Session] {"
    , "  role Client = Flow;"
    , "  role Server = Flow;"
    , "}"
    ]
  let key = GenericStaticParameterKey "protocol.session.parameter.stable"
      expected =
        ( (ProtocolRoleKey "Client", key)
        , (ProtocolRoleKey "Server", key)
        )
  (parameterEvidence, roleEvidence) <- sessionParameterEvidence key protocol
  (renamedParameterEvidence, renamedRoleEvidence) <- sessionParameterEvidence key renamed
  assert
    ( grammarV1ResolvedSessionParameterRoleReferences
        [parameterEvidence] roleEvidence protocol
        == Just (Right expected)
    )
    "Session-parameter role references did not preserve caller-supplied stable binder identity"
  assert
    ( grammarV1ResolvedSessionParameterRoleReferences
        [renamedParameterEvidence] renamedRoleEvidence renamed
        == Just (Right expected)
    )
    "Session parameter/source declaration rename leaked into stable binder identity"

sessionParameterEvidenceBoundaries :: Either String ()
sessionParameterEvidenceBoundaries = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Generic[S : Session] {"
    , "  role Client = S;"
    , "  role Server = S;"
    , "}"
    ]
  let key = GenericStaticParameterKey "protocol.session.parameter.stable"
      foreignKey = GenericStaticParameterKey "protocol.session.parameter.foreign"
  (parameterEvidence, roleEvidence) <- sessionParameterEvidence key protocol
  assert
    ( grammarV1ResolvedSessionParameterRoleReferences [] roleEvidence protocol
        == Just
          (Left
            (GrammarV1ProtocolSessionParameterEvidenceCountMismatch 1 0))
    )
    "missing Session parameter evidence was not rejected explicitly"
  let wrongKind = parameterEvidence
        { resolvedProtocolSessionParameter =
            GenericStaticParameter key GenericMessageKind
        }
  assert
    ( grammarV1ResolvedSessionParameterRoleReferences
        [wrongKind] roleEvidence protocol
        == Just
          (Left
            (GrammarV1ProtocolSessionParameterKindMismatch
              key GenericMessageKind))
    )
    "wrong-kind binder evidence was accepted for a Session parameter"
  foreignRoleEvidence <- case roleEvidence of
    first : rest -> Right
      ( first
          { resolvedProtocolSessionRoleParameterKey = foreignKey }
      : rest
      )
    [] -> Left "expected two Session role evidence entries"
  assert
    ( grammarV1ResolvedSessionParameterRoleReferences
        [parameterEvidence] foreignRoleEvidence protocol
        == Just
          (Left
            (GrammarV1ProtocolSessionRoleUndeclaredParameter foreignKey))
    )
    "foreign stable binder key was accepted for a Session role reference"
  swappedRoleEvidence <- case roleEvidence of
    [first, second] -> Right [second, first]
    other -> Left ("expected two Session role evidence entries, got " <> show (length other))
  case grammarV1ResolvedSessionParameterRoleReferences
      [parameterEvidence] swappedRoleEvidence protocol of
    Just (Left (GrammarV1ProtocolSessionRoleSourceMismatch 0 _ _)) -> Right ()
    other -> Left ("role evidence detached from its located source occurrence: " <> show other)

sessionParameterCompetenceBoundaries :: Either String ()
sessionParameterCompetenceBoundaries = do
  closed <- onlyProtocol $ Text.unlines
    [ "protocol Closed { role A = sessions.A; role B = sessions.B; }"
    ]
  typeGeneric <- onlyProtocol $ Text.unlines
    [ "protocol Generic[T : Type] { role A = T; role B = T; }"
    ]
  required <- onlyProtocol $ Text.unlines
    [ "protocol Required[S : Session] requires { proposition true; } {"
    , "  role A = S;"
    , "  role B = S;"
    , "}"
    ]
  specialized <- onlyProtocol $ Text.unlines
    [ "protocol Specialized[S : Session] {"
    , "  role A = S[U8];"
    , "  role B = S[U8];"
    , "}"
    ]
  assert
    (grammarV1ResolvedSessionParameterRoleReferences [] [] closed == Nothing)
    "nongeneric static session reference escaped through Session-parameter route"
  assert
    (grammarV1ResolvedSessionParameterRoleReferences [] [] typeGeneric == Nothing)
    "non-Session generic parameter escaped Session-parameter route"
  let key = GenericStaticParameterKey "protocol.session.parameter.stable"
  (requiredParameter, requiredRoles) <- sessionParameterEvidence key required
  assert
    ( grammarV1ResolvedSessionParameterRoleReferences
        [requiredParameter] requiredRoles required
        == Nothing
    )
    "requirement-bearing Session-parameter protocol escaped bounded route"
  specializedParameter <- onlySessionParameterEvidence key specialized
  assert
    ( grammarV1ResolvedSessionParameterRoleReferences
        [specializedParameter] [] specialized
        == Nothing
    )
    "specialized Session-parameter reference was flattened to a direct binder use"

sessionParameterEvidence
  :: GenericStaticParameterKey
  -> GrammarV1ProtocolDecl
  -> Either
      String
      ( GrammarV1ResolvedProtocolSessionParameter
      , [GrammarV1ResolvedProtocolSessionRoleReference]
      )
sessionParameterEvidence key protocol = do
  parameter <- onlySessionParameterEvidence key protocol
  roles <- case grammarV1ProtocolRoles protocol of
    [firstRole, secondRole] -> Right
      [ GrammarV1ResolvedProtocolSessionRoleReference firstRole key
      , GrammarV1ResolvedProtocolSessionRoleReference secondRole key
      ]
    other -> Left ("expected two protocol roles, got " <> show (length other))
  Right (parameter, roles)

onlySessionParameterEvidence
  :: GenericStaticParameterKey
  -> GrammarV1ProtocolDecl
  -> Either String GrammarV1ResolvedProtocolSessionParameter
onlySessionParameterEvidence key protocol =
  case grammarV1ProtocolGenericParams protocol of
    [sourceParameter] -> Right GrammarV1ResolvedProtocolSessionParameter
      { resolvedProtocolSessionSourceParameter = sourceParameter
      , resolvedProtocolSessionParameter =
          GenericStaticParameter key GenericSessionKind
      }
    other -> Left
      ("expected one protocol Session parameter, got " <> show (length other))

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "protocol-static-session-references" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left
      ("expected one protocol declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
