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
import Phil.Surface.GrammarV1.ParameterizedProtocolFamily
  ( GrammarV1ParameterizedProtocolFamilyError (..)
  , grammarV1ResolvedMessageBinaryProtocolFamily
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolMessageTemplates
  ( GrammarV1ResolvedProtocolMessageParameter (..)
  , GrammarV1ResolvedProtocolMessageUse (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 resolved Message protocols construct stable Core binary families"
        parameterizedFamilySemantics
    , test "SURF-008 parameterized family construction enforces distinct dual roles"
        parameterizedFamilyRoleFailures
    , test "SURF-008 parameterized duality distinguishes exact stable Message keys"
        parameterizedFamilyDistinguishesKeys
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

parameterizedFamilySemantics :: Either String ()
parameterizedFamilySemantics = do
  protocol <- onlyProtocol parameterizedMessageProtocolSource
  renamed <- onlyProtocol renamedMessageParameterProtocolSource
  let parameterKey = GenericStaticParameterKey "protocol.message.parameter.stable"
      declarationKey = DeclarationKey "protocol.stable.lineage"
      interfaceRevision = InterfaceRevision "protocol.interface.v2"
  (parameterEvidence, useEvidence) <- resolvedOneParameterEvidence parameterKey protocol
  (renamedParameterEvidence, renamedUseEvidence) <-
    resolvedOneParameterEvidence parameterKey renamed
  let expected = BinaryProtocolFamily
        { protocolFamilyDeclarationKey = declarationKey
        , protocolFamilyInterfaceRevision = interfaceRevision
        , protocolFamilyRequirements = Set.empty
        , protocolFamilyPrimaryRole = ProtocolRoleKey "Client"
        , protocolFamilyPeerRole = ProtocolRoleKey "Server"
        , protocolFamilyPrimarySession = ProtocolTemplateSend
            (Name "payload")
            (ProtocolParameterType parameterKey)
            (ProtocolTemplateSend
              (Name "tag")
              (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateEnd (Outcome "Done")))
        }
  assert
    ( grammarV1ResolvedMessageBinaryProtocolFamily
        declarationKey interfaceRevision [parameterEvidence] useEvidence protocol
        == Just (Right expected)
    )
    "resolved Message protocol did not preserve supplied stable family identity and primary template"
  assert
    ( grammarV1ResolvedMessageBinaryProtocolFamily
        declarationKey
        interfaceRevision
        [renamedParameterEvidence]
        renamedUseEvidence
        renamed
        == Just (Right expected)
    )
    "source protocol/Message parameter rename leaked into stable family semantics"

parameterizedFamilyRoleFailures :: Either String ()
parameterizedFamilyRoleFailures = do
  duplicate <- onlyProtocol duplicateParameterizedRoleSource
  nonDual <- onlyProtocol nonDualParameterizedMessageProtocolSource
  let parameterKey = GenericStaticParameterKey "protocol.message.parameter.stable"
      declarationKey = DeclarationKey "protocol.stable.lineage"
      interfaceRevision = InterfaceRevision "protocol.interface.v2"
  (duplicateParameter, duplicateUses) <-
    resolvedOneParameterEvidence parameterKey duplicate
  (nonDualParameter, nonDualUses) <-
    resolvedOneParameterEvidence parameterKey nonDual
  assert
    ( grammarV1ResolvedMessageBinaryProtocolFamily
        declarationKey interfaceRevision [duplicateParameter] duplicateUses duplicate
        == Just
          (Left
            (GrammarV1ParameterizedProtocolRoleError
              (DuplicateProtocolRole (ProtocolRoleKey "Same"))))
    )
    "duplicate parameterized protocol role escaped family construction"
  assert
    ( grammarV1ResolvedMessageBinaryProtocolFamily
        declarationKey interfaceRevision [nonDualParameter] nonDualUses nonDual
        == Just
          (Left
            (GrammarV1ParameterizedProtocolRoleError
              (NonDualProtocolRoles
                (ProtocolRoleKey "Client")
                (ProtocolRoleKey "Server"))))
    )
    "non-dual parameterized protocol escaped family construction"

parameterizedFamilyDistinguishesKeys :: Either String ()
parameterizedFamilyDistinguishesKeys = do
  protocol <- onlyProtocol twoMessageParameterProtocolSource
  let keyA = GenericStaticParameterKey "protocol.message.A.stable"
      keyB = GenericStaticParameterKey "protocol.message.B.stable"
      declarationKey = DeclarationKey "protocol.stable.lineage.two-message"
      interfaceRevision = InterfaceRevision "protocol.interface.v2"
  (parameterA, parameterB) <- case grammarV1ProtocolGenericParams protocol of
    [firstParameter, secondParameter] -> Right (firstParameter, secondParameter)
    other -> Left ("expected two protocol parameters, got " <> show (length other))
  (clientA, clientB, serverA, serverB) <- fourMessageTypes protocol
  let parameters =
        [ GrammarV1ResolvedProtocolMessageParameter
            parameterA (GenericStaticParameter keyA GenericMessageKind)
        , GrammarV1ResolvedProtocolMessageParameter
            parameterB (GenericStaticParameter keyB GenericMessageKind)
        ]
      oneUse sourceType key = GrammarV1ResolvedProtocolMessageUse
        { resolvedProtocolMessageSourceType = sourceType
        , resolvedProtocolMessageUseParameterKey = key
        }
      -- The client evidence is correct, while the peer evidence deliberately
      -- swaps the two already-declared stable keys. #640 accepts caller-supplied
      -- exact binder evidence; this family layer must notice that the resulting
      -- semantic templates are not dual rather than consulting source spelling.
      swappedUses =
        [ oneUse clientA keyA
        , oneUse clientB keyB
        , oneUse serverA keyB
        , oneUse serverB keyA
        ]
  assert
    ( grammarV1ResolvedMessageBinaryProtocolFamily
        declarationKey interfaceRevision parameters swappedUses protocol
        == Just
          (Left
            (GrammarV1ParameterizedProtocolRoleError
              (NonDualProtocolRoles
                (ProtocolRoleKey "Client")
                (ProtocolRoleKey "Server"))))
    )
    "parameterized duality collapsed distinct stable Message parameter identities"

resolvedOneParameterEvidence
  :: GenericStaticParameterKey
  -> GrammarV1ProtocolDecl
  -> Either
      String
      ( GrammarV1ResolvedProtocolMessageParameter
      , [GrammarV1ResolvedProtocolMessageUse]
      )
resolvedOneParameterEvidence parameterKey protocol = do
  sourceParameter <- case grammarV1ProtocolGenericParams protocol of
    [parameter] -> Right parameter
    other -> Left ("expected one protocol generic parameter, got " <> show (length other))
  (clientMessage, serverMessage) <- outerMessageTypes protocol
  let parameterEvidence = GrammarV1ResolvedProtocolMessageParameter
        sourceParameter
        (GenericStaticParameter parameterKey GenericMessageKind)
      oneUse sourceType = GrammarV1ResolvedProtocolMessageUse
        { resolvedProtocolMessageSourceType = sourceType
        , resolvedProtocolMessageUseParameterKey = parameterKey
        }
  Right (parameterEvidence, [oneUse clientMessage, oneUse serverMessage])

outerMessageTypes
  :: GrammarV1ProtocolDecl
  -> Either String (Located GrammarV1Type, Located GrammarV1Type)
outerMessageTypes protocol = case grammarV1ProtocolRoles protocol of
  [Located _ clientRole, Located _ serverRole] -> do
    clientMessage <- firstSendType
      (locatedValue (grammarV1RoleSessionExpression clientRole))
    serverMessage <- firstReceiveType
      (locatedValue (grammarV1RoleSessionExpression serverRole))
    Right (clientMessage, serverMessage)
  other -> Left ("expected two protocol roles, got " <> show (length other))

fourMessageTypes
  :: GrammarV1ProtocolDecl
  -> Either
      String
      ( Located GrammarV1Type
      , Located GrammarV1Type
      , Located GrammarV1Type
      , Located GrammarV1Type
      )
fourMessageTypes protocol = case grammarV1ProtocolRoles protocol of
  [Located _ clientRole, Located _ serverRole] -> do
    (clientA, clientB) <- twoSequentialSendTypes
      (locatedValue (grammarV1RoleSessionExpression clientRole))
    (serverA, serverB) <- twoSequentialReceiveTypes
      (locatedValue (grammarV1RoleSessionExpression serverRole))
    Right (clientA, clientB, serverA, serverB)
  other -> Left ("expected two protocol roles, got " <> show (length other))

firstSendType :: GrammarV1SessionExpression -> Either String (Located GrammarV1Type)
firstSendType source = case source of
  GrammarV1SessionSend parameter Nothing Nothing _ ->
    Right (grammarV1TermParamType (locatedValue parameter))
  other -> Left ("expected send transition, got " <> show other)

firstReceiveType :: GrammarV1SessionExpression -> Either String (Located GrammarV1Type)
firstReceiveType source = case source of
  GrammarV1SessionReceive parameter Nothing Nothing _ ->
    Right (grammarV1TermParamType (locatedValue parameter))
  other -> Left ("expected receive transition, got " <> show other)

twoSequentialSendTypes
  :: GrammarV1SessionExpression
  -> Either String (Located GrammarV1Type, Located GrammarV1Type)
twoSequentialSendTypes source = case source of
  GrammarV1SessionSend first Nothing Nothing continuation -> case locatedValue continuation of
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
  GrammarV1SessionReceive first Nothing Nothing continuation -> case locatedValue continuation of
    GrammarV1SessionReceive second Nothing Nothing _ -> Right
      ( grammarV1TermParamType (locatedValue first)
      , grammarV1TermParamType (locatedValue second)
      )
    other -> Left ("expected second receive transition, got " <> show other)
  other -> Left ("expected first receive transition, got " <> show other)

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "parameterized-protocol-family" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

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

duplicateParameterizedRoleSource :: Text.Text
duplicateParameterizedRoleSource = Text.unlines
  [ "protocol P[M : Message] {"
  , "  role Same = send (payload : M) then send (tag : U8) then end Done;"
  , "  role Same = receive (payload : M) then receive (tag : U8) then end Done;"
  , "}"
  ]

nonDualParameterizedMessageProtocolSource :: Text.Text
nonDualParameterizedMessageProtocolSource = Text.unlines
  [ "protocol P[M : Message] {"
  , "  role Client = send (payload : M) then send (tag : U8) then end Done;"
  , "  role Server = receive (payload : M) then receive (tag : U8) then end Different;"
  , "}"
  ]

twoMessageParameterProtocolSource :: Text.Text
twoMessageParameterProtocolSource = Text.unlines
  [ "protocol P[A : Message, B : Message] {"
  , "  role Client = send (first : A) then send (second : B) then end Done;"
  , "  role Server = receive (first : A) then receive (second : B) then end Done;"
  , "}"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
