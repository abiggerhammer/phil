{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( BinaryProtocolFamily (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  )
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolMessageTemplates
  ( GrammarV1ProtocolMessageTemplateError (..)
  , GrammarV1ResolvedProtocolMessageParameter (..)
  , GrammarV1ResolvedProtocolMessageUse (..)
  , grammarV1ResolvedMessageProtocolRoleTemplates
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  , grammarV1CheckedClosedProtocolRoleTemplates
  , grammarV1ClosedBinaryProtocolFamily
  , grammarV1ClosedProtocolRoleTemplates
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed protocol roles preserve exact Core template order and payloads"
        closedRolesPreserved
    , test "SURF-008 protocol role projection does not invent duality"
        nonDualRolesPreserved
    , test "SURF-008 checked protocol roles enforce distinct alpha-aware Core duals"
        checkedRoleSemantics
    , test "SURF-008 caller identity closes dual Grammar-v1 protocols into Core families"
        closedFamilySemantics
    , test "SURF-008 protocol role templates preserve session competence boundaries"
        competenceBoundaries
    , test "SURF-008 resolved Message parameters route exact source uses into Core protocol templates"
        resolvedMessageParameterTemplates
    , test "SURF-008 protocol Message parameter projection consumes exact binder evidence"
        resolvedMessageEvidenceBoundaries
    , test "SURF-008 parameterized protocol templates stay fail-closed outside Message competence"
        parameterizedProtocolCompetenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closedRolesPreserved :: Either String ()
closedRolesPreserved = do
  protocol <- onlyProtocol closedProtocolSource
  assert
    (grammarV1ClosedProtocolRoleTemplates protocol == Just expectedClosedRoles)
    "closed binary protocol did not preserve role order and exact session templates"

nonDualRolesPreserved :: Either String ()
nonDualRolesPreserved = do
  protocol <- onlyProtocol nonDualProtocolSource
  let expected =
        ( (ProtocolRoleKey "First", ProtocolTemplateEnd (Outcome "Left"))
        , (ProtocolRoleKey "Second", ProtocolTemplateEnd (Outcome "Right"))
        )
  assert
    (grammarV1ClosedProtocolRoleTemplates protocol == Just expected)
    "role-template projection incorrectly asserted or repaired protocol duality"

checkedRoleSemantics :: Either String ()
checkedRoleSemantics = do
  closed <- onlyProtocol closedProtocolSource
  duplicate <- onlyProtocol duplicateRoleSource
  nonDual <- onlyProtocol nonDualProtocolSource
  assert
    (grammarV1CheckedClosedProtocolRoleTemplates closed == Just (Right expectedClosedRoles))
    "alpha-renamed role-local binders were not accepted as definitionally dual"
  assert
    ( grammarV1CheckedClosedProtocolRoleTemplates duplicate
        == Just (Left (DuplicateProtocolRole (ProtocolRoleKey "Same")))
    )
    "duplicate protocol role identity did not reject before duality"
  assert
    ( grammarV1CheckedClosedProtocolRoleTemplates nonDual
        == Just
          (Left
            (NonDualProtocolRoles
              (ProtocolRoleKey "First")
              (ProtocolRoleKey "Second")))
    )
    "non-dual closed role sessions did not reject explicitly"

closedFamilySemantics :: Either String ()
closedFamilySemantics = do
  closed <- onlyProtocol closedProtocolSource
  renamed <- onlyProtocol renamedProtocolSource
  nonDual <- onlyProtocol nonDualProtocolSource
  let declarationKey = DeclarationKey "protocol.stable.lineage"
      interfaceRevision = InterfaceRevision "protocol.interface.v1"
      expected = BinaryProtocolFamily
        { protocolFamilyDeclarationKey = declarationKey
        , protocolFamilyInterfaceRevision = interfaceRevision
        , protocolFamilyRequirements = Set.empty
        , protocolFamilyPrimaryRole = ProtocolRoleKey "Client"
        , protocolFamilyPeerRole = ProtocolRoleKey "Server"
        , protocolFamilyPrimarySession =
            ProtocolTemplateSend
              (Name "outgoing")
              (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateEnd (Outcome "Done"))
        }
  assert
    ( grammarV1ClosedBinaryProtocolFamily declarationKey interfaceRevision closed
        == Just (Right expected)
    )
    "closed dual protocol did not preserve supplied stable identity and primary template"
  assert
    ( grammarV1ClosedBinaryProtocolFamily declarationKey interfaceRevision renamed
        == Just (Right expected)
    )
    "source protocol display-name change leaked into stable family identity"
  assert
    ( grammarV1ClosedBinaryProtocolFamily declarationKey interfaceRevision nonDual
        == Just
          (Left
            (NonDualProtocolRoles
              (ProtocolRoleKey "First")
              (ProtocolRoleKey "Second")))
    )
    "family construction bypassed checked protocol duality"

competenceBoundaries :: Either String ()
competenceBoundaries = do
  codec <- onlyProtocol codecProtocolSource
  generic <- onlyProtocol genericProtocolSource
  requirement <- onlyProtocol requirementProtocolSource
  let declarationKey = DeclarationKey "protocol.stable.lineage"
      interfaceRevision = InterfaceRevision "protocol.interface.v1"
  mapM_ (expectNothing declarationKey interfaceRevision)
    [ ("codec-bearing role", codec)
    , ("generic protocol", generic)
    , ("requirement-bearing protocol", requirement)
    ]
  where
    expectNothing declarationKey interfaceRevision (label, protocol) = do
      assert
        (grammarV1ClosedProtocolRoleTemplates protocol == Nothing)
        (label <> " escaped the closed protocol-role projection boundary")
      assert
        (grammarV1CheckedClosedProtocolRoleTemplates protocol == Nothing)
        (label <> " escaped the checked protocol-role competence boundary")
      assert
        (grammarV1ClosedBinaryProtocolFamily declarationKey interfaceRevision protocol == Nothing)
        (label <> " escaped the closed protocol-family competence boundary")

resolvedMessageParameterTemplates :: Either String ()
resolvedMessageParameterTemplates = do
  protocol <- onlyProtocol parameterizedMessageProtocolSource
  renamed <- onlyProtocol renamedMessageParameterProtocolSource
  let parameterKey = GenericStaticParameterKey "protocol.message.parameter.stable"
  (parameterEvidence, useEvidence, _) <- resolvedMessageEvidence parameterKey protocol
  (renamedParameterEvidence, renamedUseEvidence, _) <- resolvedMessageEvidence parameterKey renamed
  let expected = expectedParameterizedRoles parameterKey
  assert
    (grammarV1ClosedProtocolRoleTemplates protocol == Nothing)
    "parameterized protocol unexpectedly escaped through the closed role route"
  assert
    ( grammarV1ResolvedMessageProtocolRoleTemplates
        [parameterEvidence] useEvidence protocol
        == Just (Right expected)
    )
    "resolved Message parameter uses did not become exact ProtocolParameterType templates"
  assert
    ( grammarV1ResolvedMessageProtocolRoleTemplates
        [renamedParameterEvidence] renamedUseEvidence renamed
        == Just (Right expected)
    )
    "source Message parameter spelling change altered caller-supplied semantic key"

resolvedMessageEvidenceBoundaries :: Either String ()
resolvedMessageEvidenceBoundaries = do
  protocol <- onlyProtocol parameterizedMessageProtocolSource
  let parameterKey = GenericStaticParameterKey "protocol.message.parameter.stable"
      foreignKey = GenericStaticParameterKey "protocol.message.parameter.foreign"
  (parameterEvidence, useEvidence, primitiveUse) <- resolvedMessageEvidence parameterKey protocol
  (clientUse, serverUse) <- case useEvidence of
    [firstUse, secondUse] -> Right (firstUse, secondUse)
    other -> Left ("expected two Message use evidence entries, got " <> show other)
  let project parameters uses =
        grammarV1ResolvedMessageProtocolRoleTemplates parameters uses protocol
  assert
    ( project [] useEvidence
        == Just
          (Left
            (GrammarV1ProtocolMessageParameterEvidenceCountMismatch 1 0))
    )
    "missing declaration-parameter evidence was not rejected explicitly"
  assert
    ( project [parameterEvidence] [clientUse]
        == Just
          (Left
            (GrammarV1MissingProtocolMessageUseEvidence
              (resolvedProtocolMessageSourceType serverUse)))
    )
    "missing exact Message use evidence was not rejected explicitly"
  assert
    ( project [parameterEvidence] [clientUse, clientUse, serverUse]
        == Just
          (Left
            (GrammarV1DuplicateProtocolMessageUseEvidence
              (resolvedProtocolMessageSourceType clientUse)))
    )
    "duplicate exact Message use evidence was not rejected explicitly"
  let foreignUse = clientUse
        { resolvedProtocolMessageUseParameterKey = foreignKey }
  assert
    ( project [parameterEvidence] [foreignUse, serverUse]
        == Just
          (Left (GrammarV1ProtocolMessageUseUndeclaredParameter foreignKey))
    )
    "foreign Message parameter key was accepted at a source use occurrence"
  let extraUse = GrammarV1ResolvedProtocolMessageUse
        { resolvedProtocolMessageSourceType = primitiveUse
        , resolvedProtocolMessageUseParameterKey = parameterKey
        }
  assert
    ( project [parameterEvidence] (useEvidence <> [extraUse])
        == Just
          (Left (GrammarV1UnexpectedProtocolMessageUseEvidence primitiveUse))
    )
    "extra binder evidence was silently ignored"
  let wrongKindParameter = parameterEvidence
        { resolvedProtocolMessageParameter = GenericStaticParameter
            parameterKey
            GenericTypeKind
        }
  assert
    ( project [wrongKindParameter] useEvidence
        == Just
          (Left
            (GrammarV1ProtocolMessageParameterKindMismatch
              parameterKey
              GenericTypeKind))
    )
    "wrong-kind declaration evidence was accepted as a Message parameter"

parameterizedProtocolCompetenceBoundaries :: Either String ()
parameterizedProtocolCompetenceBoundaries = do
  closed <- onlyProtocol closedProtocolSource
  typeGeneric <- onlyProtocol typeParameterizedProtocolSource
  required <- onlyProtocol requiredMessageProtocolSource
  boundary <- onlyProtocol boundaryMessageProtocolSource
  specialized <- onlyProtocol specializedMessageProtocolSource
  let parameterKey = GenericStaticParameterKey "protocol.message.parameter.stable"
  assert
    (grammarV1ResolvedMessageProtocolRoleTemplates [] [] closed == Nothing)
    "closed protocol escaped through the separate parameterized route"
  assert
    (grammarV1ResolvedMessageProtocolRoleTemplates [] [] typeGeneric == Nothing)
    "non-Message generic protocol escaped Message-parameter competence"
  requiredParameter <- messageParameterEvidenceOnly parameterKey required
  assert
    ( grammarV1ResolvedMessageProtocolRoleTemplates [requiredParameter] [] required
        == Nothing
    )
    "requirement-bearing Message protocol escaped the bounded template route"
  boundaryParameter <- messageParameterEvidenceOnly parameterKey boundary
  assert
    ( grammarV1ResolvedMessageProtocolRoleTemplates [boundaryParameter] [] boundary
        == Nothing
    )
    "boundary-bearing Message transition lost its boundary semantics"
  specializedParameter <- messageParameterEvidenceOnly parameterKey specialized
  specializedType <- firstRoleOuterMessageType specialized
  let specializedUse = GrammarV1ResolvedProtocolMessageUse
        { resolvedProtocolMessageSourceType = specializedType
        , resolvedProtocolMessageUseParameterKey = parameterKey
        }
  assert
    ( grammarV1ResolvedMessageProtocolRoleTemplates
        [specializedParameter]
        [specializedUse]
        specialized
        == Nothing
    )
    "specialized Message type use was flattened to one parameter key"

expectedParameterizedRoles
  :: GenericStaticParameterKey
  -> ( (ProtocolRoleKey, ProtocolSessionTemplate)
     , (ProtocolRoleKey, ProtocolSessionTemplate)
     )
expectedParameterizedRoles parameterKey =
  ( ( ProtocolRoleKey "Client"
    , ProtocolTemplateSend
        (Name "payload")
        (ProtocolParameterType parameterKey)
        (ProtocolTemplateSend
          (Name "tag")
          (ProtocolConcreteType (TyUInt 8))
          (ProtocolTemplateEnd (Outcome "Done")))
    )
  , ( ProtocolRoleKey "Server"
    , ProtocolTemplateReceive
        (Name "payload")
        (ProtocolParameterType parameterKey)
        (ProtocolTemplateReceive
          (Name "tag")
          (ProtocolConcreteType (TyUInt 8))
          (ProtocolTemplateEnd (Outcome "Done")))
    )
  )

resolvedMessageEvidence
  :: GenericStaticParameterKey
  -> GrammarV1ProtocolDecl
  -> Either
      String
      ( GrammarV1ResolvedProtocolMessageParameter
      , [GrammarV1ResolvedProtocolMessageUse]
      , Located GrammarV1Type
      )
resolvedMessageEvidence parameterKey protocol = do
  parameterEvidence <- messageParameterEvidenceOnly parameterKey protocol
  (clientType, clientPrimitive, serverType) <- parameterizedMessageTypes protocol
  let oneUse sourceType = GrammarV1ResolvedProtocolMessageUse
        { resolvedProtocolMessageSourceType = sourceType
        , resolvedProtocolMessageUseParameterKey = parameterKey
        }
  Right
    ( parameterEvidence
    , [oneUse clientType, oneUse serverType]
    , clientPrimitive
    )

messageParameterEvidenceOnly
  :: GenericStaticParameterKey
  -> GrammarV1ProtocolDecl
  -> Either String GrammarV1ResolvedProtocolMessageParameter
messageParameterEvidenceOnly parameterKey protocol = case grammarV1ProtocolGenericParams protocol of
  [sourceParameter] -> Right GrammarV1ResolvedProtocolMessageParameter
    { resolvedProtocolMessageSourceParameter = sourceParameter
    , resolvedProtocolMessageParameter = GenericStaticParameter
        parameterKey
        GenericMessageKind
    }
  other -> Left
    ("expected one protocol generic parameter, got " <> show (length other))

parameterizedMessageTypes
  :: GrammarV1ProtocolDecl
  -> Either String (Located GrammarV1Type, Located GrammarV1Type, Located GrammarV1Type)
parameterizedMessageTypes protocol = case grammarV1ProtocolRoles protocol of
  [Located _ clientRole, Located _ serverRole] -> do
    (clientMessage, clientPrimitive) <- twoSequentialSendTypes
      (locatedValue (grammarV1RoleSessionExpression clientRole))
    (serverMessage, _) <- twoSequentialReceiveTypes
      (locatedValue (grammarV1RoleSessionExpression serverRole))
    Right (clientMessage, clientPrimitive, serverMessage)
  other -> Left ("expected two protocol roles, got " <> show (length other))

twoSequentialSendTypes
  :: GrammarV1SessionExpression
  -> Either String (Located GrammarV1Type, Located GrammarV1Type)
twoSequentialSendTypes source = case source of
  GrammarV1SessionSend first Nothing Nothing continuation ->
    case locatedValue continuation of
      GrammarV1SessionSend second Nothing Nothing _ -> Right
        ( grammarV1TermParamType (locatedValue first)
        , grammarV1TermParamType (locatedValue second)
        )
      other -> Left ("expected second send transition, got " <> show other)
  other -> Left ("expected first send transition, got " <> show other)

twoSequentialReceiveTypes
  :: GrammarV1SessionExpression
  -> Either String (Located GrammarV1Type, Located GrammarV1Type)
twoSequentialReceiveTypes source = case source of
  GrammarV1SessionReceive first Nothing Nothing continuation ->
    case locatedValue continuation of
      GrammarV1SessionReceive second Nothing Nothing _ -> Right
        ( grammarV1TermParamType (locatedValue first)
        , grammarV1TermParamType (locatedValue second)
        )
      other -> Left ("expected second receive transition, got " <> show other)
  other -> Left ("expected first receive transition, got " <> show other)

firstRoleOuterMessageType
  :: GrammarV1ProtocolDecl
  -> Either String (Located GrammarV1Type)
firstRoleOuterMessageType protocol = case grammarV1ProtocolRoles protocol of
  Located _ firstRole : _ -> case locatedValue (grammarV1RoleSessionExpression firstRole) of
    GrammarV1SessionSend parameter _ _ _ ->
      Right (grammarV1TermParamType (locatedValue parameter))
    GrammarV1SessionReceive parameter _ _ _ ->
      Right (grammarV1TermParamType (locatedValue parameter))
    other -> Left ("expected outer send/receive transition, got " <> show other)
  [] -> Left "expected at least one protocol role"

expectedClosedRoles
  :: ( (ProtocolRoleKey, ProtocolSessionTemplate)
     , (ProtocolRoleKey, ProtocolSessionTemplate)
     )
expectedClosedRoles =
  ( ( ProtocolRoleKey "Client"
    , ProtocolTemplateSend
        (Name "outgoing")
        (ProtocolConcreteType (TyUInt 8))
        (ProtocolTemplateEnd (Outcome "Done"))
    )
  , ( ProtocolRoleKey "Server"
    , ProtocolTemplateReceive
        (Name "incoming")
        (ProtocolConcreteType (TyUInt 8))
        (ProtocolTemplateEnd (Outcome "Done"))
    )
  )

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "protocol-role-templates" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

closedProtocolSource :: Text.Text
closedProtocolSource = Text.unlines
  [ "protocol P {"
  , "  role Client = send (outgoing : U8) then end Done;"
  , "  role Server = receive (incoming : U8) then end Done;"
  , "}"
  ]

renamedProtocolSource :: Text.Text
renamedProtocolSource = Text.unlines
  [ "protocol RenamedPresentation {"
  , "  role Client = send (outgoing : U8) then end Done;"
  , "  role Server = receive (incoming : U8) then end Done;"
  , "}"
  ]

duplicateRoleSource :: Text.Text
duplicateRoleSource = Text.unlines
  [ "protocol P {"
  , "  role Same = send (outgoing : U8) then end Done;"
  , "  role Same = receive (incoming : U8) then end Done;"
  , "}"
  ]

nonDualProtocolSource :: Text.Text
nonDualProtocolSource = Text.unlines
  [ "protocol P {"
  , "  role First = end Left;"
  , "  role Second = end Right;"
  , "}"
  ]

codecProtocolSource :: Text.Text
codecProtocolSource = Text.unlines
  [ "protocol P {"
  , "  role A = send (x : U8) using Wire then end Done;"
  , "  role B = end Done;"
  , "}"
  ]

genericProtocolSource :: Text.Text
genericProtocolSource = Text.unlines
  [ "protocol P[S : Session] {"
  , "  role A = end Done;"
  , "  role B = end Done;"
  , "}"
  ]

requirementProtocolSource :: Text.Text
requirementProtocolSource = Text.unlines
  [ "protocol P requires { proposition true; } {"
  , "  role A = end Done;"
  , "  role B = end Done;"
  , "}"
  ]

parameterizedMessageProtocolSource :: Text.Text
parameterizedMessageProtocolSource = Text.unlines
  [ "protocol P[M : Message] {"
  , "  role Client = send (payload : M) then send (tag : U8) then end Done;"
  , "  role Server = receive (payload : M) then receive (tag : U8) then end Done;"
  , "}"
  ]

renamedMessageParameterProtocolSource :: Text.Text
renamedMessageParameterProtocolSource = Text.unlines
  [ "protocol Renamed[Payload : Message] {"
  , "  role Client = send (payload : Payload) then send (tag : U8) then end Done;"
  , "  role Server = receive (payload : Payload) then receive (tag : U8) then end Done;"
  , "}"
  ]

typeParameterizedProtocolSource :: Text.Text
typeParameterizedProtocolSource = Text.unlines
  [ "protocol P[T : Type] {"
  , "  role Client = send (payload : T) then end Done;"
  , "  role Server = receive (payload : T) then end Done;"
  , "}"
  ]

requiredMessageProtocolSource :: Text.Text
requiredMessageProtocolSource = Text.unlines
  [ "protocol P[M : Message] requires { proposition true; } {"
  , "  role Client = send (payload : M) then end Done;"
  , "  role Server = receive (payload : M) then end Done;"
  , "}"
  ]

boundaryMessageProtocolSource :: Text.Text
boundaryMessageProtocolSource = Text.unlines
  [ "protocol P[M : Message] {"
  , "  role Client = send (payload : M) using Wire then end Done;"
  , "  role Server = receive (payload : M) then end Done;"
  , "}"
  ]

specializedMessageProtocolSource :: Text.Text
specializedMessageProtocolSource = Text.unlines
  [ "protocol P[M : Message] {"
  , "  role Client = send (payload : Box[M]) then end Done;"
  , "  role Server = receive (payload : Box[M]) then end Done;"
  , "}"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
