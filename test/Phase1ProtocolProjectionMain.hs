{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Generic
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session (dualSession)
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROT-004 identity-bearing parameters distinguish equal local projections" equalProjectionShapeDistinctIdentity
    , test "PROT-004 valid primary role projects exact local session" validPrimaryProjection
    , test "PROT-004 peer projection is exact dependent dual" validPeerProjectionDual
    , test "PROT-004 unknown role projection rejects" invalidRoleRejects
    , test "PROT-004 fabricated role-local session evidence rejects" fabricatedProjectionRejects
    , test "PROT-004 mixed-instance projection evidence rejects despite equal local shape" mixedInstanceProjectionRejects
    , test "PROT-004 missing message argument rejects" missingMessageArgumentRejects
    , test "PROT-004 family requirements discharge through generic instantiation" missingGenericRequirementRejects
    , test "PROT-004 message parameter substitution changes exact projection" messageParameterSubstitution
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

equalProjectionShapeDistinctIdentity :: Either String ()
equalProjectionShapeDistinctIdentity = do
  left <- instanceA
  right <- instanceB
  leftProjection <- mapLeft show (projectProtocolRole left clientRole)
  rightProjection <- mapLeft show (projectProtocolRole right clientRole)
  assert
    (protocolProjectionSession leftProjection == protocolProjectionSession rightProjection)
    "identity-only parameter unexpectedly changed the local session"
  assert
    (binaryProtocolInstanceRevision left /= binaryProtocolInstanceRevision right)
    "distinct exact static arguments collapsed protocol-instance identity"

validPrimaryProjection :: Either String ()
validPrimaryProjection = do
  instanceValue <- instanceA
  projection <- mapLeft show (projectProtocolRole instanceValue clientRole)
  assert (protocolProjectionInstance projection == binaryProtocolInstanceRevision instanceValue)
    "projection lost exact protocol-instance identity"
  assert (protocolProjectionRole projection == clientRole)
    "projection lost exact role identity"
  assert (protocolProjectionSession projection == expectedClientSession)
    "primary projection did not substitute the exact local session"
  mapLeft show (verifyProtocolProjection instanceValue projection)

validPeerProjectionDual :: Either String ()
validPeerProjectionDual = do
  instanceValue <- instanceA
  client <- mapLeft show (projectProtocolRole instanceValue clientRole)
  server <- mapLeft show (projectProtocolRole instanceValue serverRole)
  assert
    (protocolProjectionSession server == dualSession (protocolProjectionSession client))
    "peer projection is not the exact session dual"
  mapLeft show (verifyProtocolProjection instanceValue server)

invalidRoleRejects :: Either String ()
invalidRoleRejects = do
  instanceValue <- instanceA
  case projectProtocolRole instanceValue auditorRole of
    Left (UnknownProtocolProjectionRole role available) ->
      assert
        (role == auditorRole && clientRole `elem` available && serverRole `elem` available)
        "unknown-role diagnostic lost the exact requested/available roles"
    other -> Left ("unknown role was not rejected exactly: " <> show other)

fabricatedProjectionRejects :: Either String ()
fabricatedProjectionRejects = do
  instanceValue <- instanceA
  client <- mapLeft show (projectProtocolRole instanceValue clientRole)
  let fabricated = client { protocolProjectionSession = expectedServerSession }
  case verifyProtocolProjection instanceValue fabricated of
    Left (ProtocolProjectionSessionMismatch role expected actual) ->
      assert
        (role == clientRole && expected == expectedClientSession && actual == expectedServerSession)
        "fabricated projection mismatch lost exact role/session values"
    other -> Left ("fabricated local session evidence was accepted: " <> show other)

mixedInstanceProjectionRejects :: Either String ()
mixedInstanceProjectionRejects = do
  left <- instanceA
  right <- instanceB
  projection <- mapLeft show (projectProtocolRole right clientRole)
  assert
    (protocolProjectionSession projection == expectedClientSession)
    "mixed-instance fixture does not have equal local session shape"
  case verifyProtocolProjection left projection of
    Left (ProtocolProjectionInstanceMismatch expected actual) ->
      assert
        (expected == binaryProtocolInstanceRevision left
          && actual == binaryProtocolInstanceRevision right)
        "mixed-instance rejection lost exact instance identities"
    other -> Left ("projection evidence crossed protocol instances: " <> show other)

missingMessageArgumentRejects :: Either String ()
missingMessageArgumentRejects =
  case instantiateBinaryProtocol
      strictGenericInstantiationPolicy
      requestResponseFamily
      [requestArgument32, variantArgumentA]
      [boundaryDisposition] of
    Left (MissingProtocolMessageArgument key) ->
      assert (key == responseParameter)
        "missing argument rejection named the wrong parameter"
    other -> Left ("missing message argument did not reject: " <> show other)

missingGenericRequirementRejects :: Either String ()
missingGenericRequirementRejects =
  case instantiateBinaryProtocol
      strictGenericInstantiationPolicy
      requestResponseFamily
      argumentsA
      [] of
    Left (ProtocolGenericInstantiationError (MissingGenericRequirementDisposition requirement)) ->
      assert (requirement == boundaryRequirement)
        "generic requirement rejection named the wrong requirement"
    other -> Left ("family requirement bypassed generic instantiation: " <> show other)

messageParameterSubstitution :: Either String ()
messageParameterSubstitution = do
  original <- instanceA
  changed <- mapLeft show $ instantiateBinaryProtocol
    strictGenericInstantiationPolicy
    requestResponseFamily
    [requestArgument64, responseArgument16, variantArgumentA]
    [boundaryDisposition]
  originalProjection <- mapLeft show (projectProtocolRole original clientRole)
  changedProjection <- mapLeft show (projectProtocolRole changed clientRole)
  assert
    (protocolProjectionSession originalProjection == expectedClientSession)
    "baseline projection changed unexpectedly"
  assert
    (protocolProjectionSession changedProjection == expectedClientSession64)
    "message parameter was not substituted into the exact local session"
  assert
    (binaryProtocolInstanceRevision original /= binaryProtocolInstanceRevision changed)
    "message argument change did not revise protocol-instance identity"

instanceA :: Either String BinaryProtocolInstance
instanceA = mapLeft show $ instantiateBinaryProtocol
  strictGenericInstantiationPolicy
  requestResponseFamily
  argumentsA
  [boundaryDisposition]

instanceB :: Either String BinaryProtocolInstance
instanceB = mapLeft show $ instantiateBinaryProtocol
  strictGenericInstantiationPolicy
  requestResponseFamily
  argumentsB
  [boundaryDisposition]

requestResponseFamily :: BinaryProtocolFamily
requestResponseFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.request-response"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.request-response.family.v1"
  , protocolFamilyRequirements = Set.singleton boundaryRequirement
  , protocolFamilyPrimaryRole = clientRole
  , protocolFamilyPeerRole = serverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      (Name "request")
      (ProtocolParameterType requestParameter)
      (ProtocolTemplateReceive
        (Name "response")
        (ProtocolParameterType responseParameter)
        (ProtocolTemplateEnd (Outcome "done")))
  }

requestParameter, responseParameter, variantParameter :: GenericStaticParameterKey
requestParameter = GenericStaticParameterKey "Request"
responseParameter = GenericStaticParameterKey "Response"
variantParameter = GenericStaticParameterKey "Variant"

clientRole, serverRole, auditorRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "client"
serverRole = ProtocolRoleKey "server"
auditorRole = ProtocolRoleKey "auditor"

requestArgument32, requestArgument64, responseArgument16, variantArgumentA, variantArgumentB :: ProtocolMessageArgument
requestArgument32 = ProtocolMessageArgument
  { protocolMessageArgumentKey = requestParameter
  , protocolMessageArgumentType = TyUInt 32
  , protocolMessageArgumentSemantics = SemanticAtom "message.uint32"
  }
requestArgument64 = ProtocolMessageArgument
  { protocolMessageArgumentKey = requestParameter
  , protocolMessageArgumentType = TyUInt 64
  , protocolMessageArgumentSemantics = SemanticAtom "message.uint64"
  }
responseArgument16 = ProtocolMessageArgument
  { protocolMessageArgumentKey = responseParameter
  , protocolMessageArgumentType = TyUInt 16
  , protocolMessageArgumentSemantics = SemanticAtom "message.uint16"
  }
variantArgumentA = ProtocolMessageArgument
  { protocolMessageArgumentKey = variantParameter
  , protocolMessageArgumentType = TyUnit
  , protocolMessageArgumentSemantics = SemanticAtom "variant.a"
  }
variantArgumentB = ProtocolMessageArgument
  { protocolMessageArgumentKey = variantParameter
  , protocolMessageArgumentType = TyUnit
  , protocolMessageArgumentSemantics = SemanticAtom "variant.b"
  }

argumentsA, argumentsB :: [ProtocolMessageArgument]
argumentsA = [requestArgument32, responseArgument16, variantArgumentA]
argumentsB = [requestArgument32, responseArgument16, variantArgumentB]

boundaryProposition :: Proposition
boundaryProposition = Atom "BoundaryMessageParametersAdmissible" []

boundaryRequirement :: GenericRequirement
boundaryRequirement = GenericPropositionRequirement boundaryProposition

boundaryDisposition :: (GenericRequirement, GenericRequirementDisposition)
boundaryDisposition =
  ( boundaryRequirement
  , GenericSatisfiedByEvidence GenericEvidence
      { genericEvidenceProposition = boundaryProposition
      , genericEvidenceIdentity = "proof.boundary-message-parameters.001"
      }
  )

expectedClientSession, expectedServerSession, expectedClientSession64 :: Session
expectedClientSession = Send
  (Name "request")
  (TyUInt 32)
  (Receive (Name "response") (TyUInt 16) (End (Outcome "done")))
expectedServerSession = dualSession expectedClientSession
expectedClientSession64 = Send
  (Name "request")
  (TyUInt 64)
  (Receive (Name "response") (TyUInt 16) (End (Outcome "done")))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
