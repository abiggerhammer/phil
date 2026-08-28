{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Generic
  ( GenericStaticParameterKey (..)
  , strictGenericInstantiationPolicy
  )
import Phil.Core.Protocol
  ( ProtocolRoleKey (..)
  )
import Phil.Core.Protocol.Family
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Outcome (..)
  , ProductElementType (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROT-008 exact owned restricted message is admitted" ownedRestrictedMessageAccepts
    , test "PROT-008 admitted linear aggregate remains a Message" admittedLinearAggregateAccepts
    , test "PROT-008 scoped borrowed view is not a Message" scopedViewRejects
    , test "PROT-008 direct endpoint rejects despite admitted-leaf misclassification" directEndpointRejects
    , test "PROT-008 aggregate wrapping cannot hide endpoint" nestedEndpointRejects
    , test "PROT-008 live authority-bearing capability is not a Message" liveAuthorityRejects
    , test "PROT-008 aggregate wrapping cannot hide live authority" nestedAuthorityRejects
    , test "PROT-008 boundary contract is tied to exact type" contractTypeMismatchRejects
    , test "PROT-008 boundary contract is tied to exact semantic identity" contractSemanticsMismatchRejects
    , test "PROT-008 opaque concrete message requires explicit boundary contract" opaqueConcreteRejects
    , test "PROT-008 intrinsic concrete scalar remains admissible" intrinsicConcreteAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

ownedRestrictedMessageAccepts :: Either String ()
ownedRestrictedMessageAccepts = do
  instanceValue <- mapLeft show $ instantiate ownedArgument
  projection <- mapLeft show $ projectProtocolRole instanceValue senderRole
  assert
    (protocolProjectionSession projection
      == Send (Name "payload") ownedTy (End doneOutcome))
    "admitted owned message did not instantiate exact session payload type"

admittedLinearAggregateAccepts :: Either String ()
admittedLinearAggregateAccepts =
  mapLeft show $ instantiate aggregateOwnedArgument >> Right ()

scopedViewRejects :: Either String ()
scopedViewRejects =
  case instantiate scopedViewArgument of
    Left (ProtocolMessageArgumentAdmissibilityError key
      (BoundaryMessageInadmissible [] (ScopedViewNotCommunicable detail))) ->
        assert
          (key == messageParameter && detail == "loan.payload")
          "scoped-view rejection lost exact parameter/view identity"
    other -> Left ("scoped view was admitted as Message: " <> show other)

directEndpointRejects :: Either String ()
directEndpointRejects =
  case instantiate endpointMisclassifiedArgument of
    Left (ProtocolMessageArgumentAdmissibilityError key
      (BoundaryMessageInadmissible [] LiveEndpointNotCommunicable)) ->
        assert (key == messageParameter)
          "endpoint rejection lost exact Message parameter"
    other -> Left ("live endpoint crossed Message boundary: " <> show other)

nestedEndpointRejects :: Either String ()
nestedEndpointRejects =
  case instantiate nestedEndpointArgument of
    Left (ProtocolMessageArgumentAdmissibilityError key
      (BoundaryMessageInadmissible path LiveEndpointNotCommunicable)) ->
        assert
          (key == messageParameter && path == [1])
          "nested-endpoint rejection lost exact aggregate path"
    other -> Left ("aggregate wrapping laundered endpoint into Message: " <> show other)

liveAuthorityRejects :: Either String ()
liveAuthorityRejects =
  case instantiate authorityArgument of
    Left (ProtocolMessageArgumentAdmissibilityError key
      (BoundaryMessageInadmissible [] (LiveAuthorityNotCommunicable authority))) ->
        assert
          (key == messageParameter && authority == "cap.store.write")
          "live-authority rejection lost exact authority identity"
    other -> Left ("live authority was admitted as Message: " <> show other)

nestedAuthorityRejects :: Either String ()
nestedAuthorityRejects =
  case instantiate nestedAuthorityArgument of
    Left (ProtocolMessageArgumentAdmissibilityError key
      (BoundaryMessageInadmissible path (LiveAuthorityNotCommunicable authority))) ->
        assert
          ( key == messageParameter
            && path == [0]
            && authority == "provider.database.admin"
          )
          "nested-authority rejection lost exact aggregate path/authority"
    other -> Left ("aggregate wrapping laundered authority into Message: " <> show other)

contractTypeMismatchRejects :: Either String ()
contractTypeMismatchRejects =
  let bad = ownedArgument
        { protocolMessageArgumentBoundaryContract = ownedContract
            { boundaryMessageContractType = TyUInt 64 }
        }
  in case instantiate bad of
      Left (ProtocolMessageArgumentAdmissibilityError key
        (BoundaryMessageContractTypeMismatch expected actual)) ->
          assert
            (key == messageParameter && expected == ownedTy && actual == TyUInt 64)
            "contract type mismatch lost exact expected/actual type"
      other -> Left ("message contract transferred across types: " <> show other)

contractSemanticsMismatchRejects :: Either String ()
contractSemanticsMismatchRejects =
  let bad = ownedArgument
        { protocolMessageArgumentBoundaryContract = ownedContract
            { boundaryMessageContractSemantics = SemanticAtom "message.other" }
        }
  in case instantiate bad of
      Left (ProtocolMessageArgumentAdmissibilityError key
        (BoundaryMessageContractSemanticsMismatch expected actual)) ->
          assert
            ( key == messageParameter
              && expected == ownedSemantics
              && actual == SemanticAtom "message.other"
            )
            "contract semantic mismatch lost exact expected/actual identity"
      other -> Left ("message contract transferred across semantic actuals: " <> show other)

opaqueConcreteRejects :: Either String ()
opaqueConcreteRejects =
  case instantiateBinaryProtocol
      strictGenericInstantiationPolicy
      (familyFor (ProtocolConcreteType ownedTy))
      []
      [] of
    Left (ProtocolConcreteMessageRequiresBoundaryContract actualTy) ->
      assert (actualTy == ownedTy)
        "opaque-concrete rejection lost exact message type"
    other -> Left ("opaque concrete message bypassed boundary contract: " <> show other)

intrinsicConcreteAccepts :: Either String ()
intrinsicConcreteAccepts =
  mapLeft show $
    instantiateBinaryProtocol
      strictGenericInstantiationPolicy
      (familyFor (ProtocolConcreteType (TyUInt 32)))
      []
      []
    >> Right ()

instantiate
  :: ProtocolMessageArgument
  -> Either ProtocolFamilyError BinaryProtocolInstance
instantiate messageArgument = instantiateBinaryProtocol
  strictGenericInstantiationPolicy
  parameterizedFamily
  [messageArgument]
  []

parameterizedFamily :: BinaryProtocolFamily
parameterizedFamily = familyFor (ProtocolParameterType messageParameter)

familyFor :: ProtocolTypeTemplate -> BinaryProtocolFamily
familyFor message = BinaryProtocolFamily
  { protocolFamilyDeclarationKey = DeclarationKey "protocol.prot008"
  , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.prot008.v1"
  , protocolFamilyRequirements = Set.empty
  , protocolFamilyPrimaryRole = senderRole
  , protocolFamilyPeerRole = receiverRole
  , protocolFamilyPrimarySession = ProtocolTemplateSend
      (Name "payload")
      message
      (ProtocolTemplateEnd doneOutcome)
  }

messageParameter :: GenericStaticParameterKey
messageParameter = GenericStaticParameterKey "M"

senderRole, receiverRole :: ProtocolRoleKey
senderRole = ProtocolRoleKey "sender"
receiverRole = ProtocolRoleKey "receiver"

doneOutcome :: Outcome
doneOutcome = Outcome "done"

ownedTy :: Ty
ownedTy = TyOpaque "OwnedBoundaryPayload"

ownedSemantics :: SemanticForm
ownedSemantics = SemanticAtom "message.owned-boundary-payload"

ownedContract :: BoundaryMessageContract
ownedContract = BoundaryMessageContract
  { boundaryMessageContractRevision = "boundary.message.owned.v1"
  , boundaryMessageContractType = ownedTy
  , boundaryMessageContractSemantics = ownedSemantics
  , boundaryMessageContractShape =
      BoundaryMessageAdmittedLeaf "owned-restricted-message"
  }

ownedArgument :: ProtocolMessageArgument
ownedArgument = argument ownedTy ownedSemantics ownedContract

aggregateOwnedArgument :: ProtocolMessageArgument
aggregateOwnedArgument = argument aggregateOwnedTy aggregateOwnedSemantics
  BoundaryMessageContract
    { boundaryMessageContractRevision = "boundary.message.aggregate-owned.v1"
    , boundaryMessageContractType = aggregateOwnedTy
    , boundaryMessageContractSemantics = aggregateOwnedSemantics
    , boundaryMessageContractShape = BoundaryMessageAggregate
        [ BoundaryMessageAdmittedLeaf "owned-header"
        , BoundaryMessageAdmittedLeaf "owned-payload"
        ]
    }

aggregateOwnedTy :: Ty
aggregateOwnedTy = TyProduct
  [ ProductElementType Unrestricted (TyUInt 16)
  , ProductElementType Linear ownedTy
  ]

aggregateOwnedSemantics :: SemanticForm
aggregateOwnedSemantics = SemanticAtom "message.aggregate-owned"

scopedViewArgument :: ProtocolMessageArgument
scopedViewArgument = argument scopedViewTy (SemanticAtom "message.scoped-view")
  BoundaryMessageContract
    { boundaryMessageContractRevision = "boundary.message.scoped-view.v1"
    , boundaryMessageContractType = scopedViewTy
    , boundaryMessageContractSemantics = SemanticAtom "message.scoped-view"
    , boundaryMessageContractShape = BoundaryMessageScopedView "loan.payload"
    }

scopedViewTy :: Ty
scopedViewTy = TyBytes (RefNat 32)

endpointMisclassifiedArgument :: ProtocolMessageArgument
endpointMisclassifiedArgument = argument endpointTy (SemanticAtom "message.endpoint")
  BoundaryMessageContract
    { boundaryMessageContractRevision = "boundary.message.endpoint.bogus.v1"
    , boundaryMessageContractType = endpointTy
    , boundaryMessageContractSemantics = SemanticAtom "message.endpoint"
    , boundaryMessageContractShape =
        BoundaryMessageAdmittedLeaf "incorrectly-classified-endpoint"
    }

endpointTy :: Ty
endpointTy = TyEndpoint (End doneOutcome)

nestedEndpointArgument :: ProtocolMessageArgument
nestedEndpointArgument = argument nestedEndpointTy (SemanticAtom "message.nested-endpoint")
  BoundaryMessageContract
    { boundaryMessageContractRevision = "boundary.message.nested-endpoint.v1"
    , boundaryMessageContractType = nestedEndpointTy
    , boundaryMessageContractSemantics = SemanticAtom "message.nested-endpoint"
    , boundaryMessageContractShape = BoundaryMessageAggregate
        [ BoundaryMessageAdmittedLeaf "header"
        , BoundaryMessageLiveEndpoint
        ]
    }

nestedEndpointTy :: Ty
nestedEndpointTy = TyProduct
  [ ProductElementType Unrestricted (TyUInt 8)
  , ProductElementType Linear endpointTy
  ]

authorityArgument :: ProtocolMessageArgument
authorityArgument = argument authorityTy (SemanticAtom "message.live-authority")
  BoundaryMessageContract
    { boundaryMessageContractRevision = "boundary.message.live-authority.v1"
    , boundaryMessageContractType = authorityTy
    , boundaryMessageContractSemantics = SemanticAtom "message.live-authority"
    , boundaryMessageContractShape =
        BoundaryMessageLiveAuthority "cap.store.write"
    }

authorityTy :: Ty
authorityTy = TyOpaque "Capability<StoreWrite>"

nestedAuthorityArgument :: ProtocolMessageArgument
nestedAuthorityArgument = argument nestedAuthorityTy (SemanticAtom "message.nested-authority")
  BoundaryMessageContract
    { boundaryMessageContractRevision = "boundary.message.nested-authority.v1"
    , boundaryMessageContractType = nestedAuthorityTy
    , boundaryMessageContractSemantics = SemanticAtom "message.nested-authority"
    , boundaryMessageContractShape = BoundaryMessageAggregate
        [ BoundaryMessageLiveAuthority "provider.database.admin"
        , BoundaryMessageAdmittedLeaf "ordinary-field"
        ]
    }

nestedAuthorityTy :: Ty
nestedAuthorityTy = TyProduct
  [ ProductElementType Linear (TyOpaque "Provider<DatabaseAdmin>")
  , ProductElementType Unrestricted (TyUInt 32)
  ]

argument
  :: Ty
  -> SemanticForm
  -> BoundaryMessageContract
  -> ProtocolMessageArgument
argument ty semantics contract = ProtocolMessageArgument
  { protocolMessageArgumentKey = messageParameter
  , protocolMessageArgumentType = ty
  , protocolMessageArgumentSemantics = semantics
  , protocolMessageArgumentBoundaryContract = contract
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
