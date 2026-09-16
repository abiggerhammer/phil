module Phil.Surface.GrammarV1.ComponentUnrestrictedRendezvous
  ( GrammarV1RootEntryScalar (..)
  , GrammarV1UnrestrictedMessageValueFlow (..)
  , GrammarV1UnrestrictedRendezvousError (..)
  , grammarV1CheckUnrestrictedComponentRendezvous
  ) where

import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Process
  ( ProcessNetwork
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState
  , ProcessRendezvousError
  , ProcessRendezvousRequest (..)
  , checkProcessCommunicationState
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance
  )
import Phil.Core.Scalar
  ( ScalarLiteral
  , ScalarType (..)
  , scalarLiteralInRange
  , scalarLiteralType
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
  ( GrammarV1ProvisionedComponentParameter (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder
  )
import Phil.Surface.GrammarV1.ComponentReceiveProvisioning
  ( GrammarV1ResolvedComponentReceive (..)
  )
import Phil.Surface.GrammarV1.ComponentSendProvisioning
  ( GrammarV1ResolvedComponentSend (..)
  )

-- | One concrete scalar supplied at a root architecture entry at runtime.
-- The occurrence key is the source-derived provisioning identity, so callers
-- cannot satisfy a send with an equal-typed value from a different entry.
data GrammarV1RootEntryScalar = GrammarV1RootEntryScalar
  { rootEntryScalarOccurrence :: ActivationOccurrenceKey
  , rootEntryScalarValue :: ScalarLiteral
  }
  deriving (Eq, Show)

-- | Evidence that one exact unrestricted root-entry scalar participated in a
-- successful internal send/receive rendezvous and became the value of the exact
-- source-derived receive binder. Unrestricted values are copied semantically;
-- no restricted-owner transfer is fabricated.
data GrammarV1UnrestrictedMessageValueFlow = GrammarV1UnrestrictedMessageValueFlow
  { unrestrictedValueFlowEntryOccurrence :: ActivationOccurrenceKey
  , unrestrictedValueFlowSenderBinder :: GrammarV1ResolvedBinder
  , unrestrictedValueFlowReceiverBinder :: GrammarV1ResolvedBinder
  , unrestrictedValueFlowType :: Ty
  , unrestrictedValueFlowValue :: ScalarLiteral
  }
  deriving (Eq, Show)

data GrammarV1UnrestrictedRendezvousError
  = GrammarV1UnrestrictedRendezvousSenderModeMismatch Mode
  | GrammarV1UnrestrictedRendezvousEntryOccurrenceMismatch
      ActivationOccurrenceKey
      ActivationOccurrenceKey
  | GrammarV1UnrestrictedRendezvousScalarOutOfRange ScalarLiteral
  | GrammarV1UnrestrictedRendezvousScalarTypeMismatch Ty Ty
  | GrammarV1UnrestrictedRendezvousProcessError ProcessRendezvousError
  deriving (Eq, Show)

-- | Execute the exact source-derived send/receive pair while carrying one
-- concrete unrestricted root-entry scalar through the same checked transition.
--
-- The source/provisioning slices have already established that the sender
-- parameter is the architecture entry bound to the send operand and that the
-- receiver binder is the payload result of the matching receive. This function
-- closes the remaining runtime value seam: the supplied entry occurrence must
-- be that exact source occurrence; its scalar representation must be valid and
-- exactly typed; and only a successful protocol rendezvous can produce the
-- receiver-value evidence.
grammarV1CheckUnrestrictedComponentRendezvous
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> GrammarV1ResolvedComponentSend
  -> GrammarV1ResolvedComponentReceive
  -> GrammarV1RootEntryScalar
  -> Either
      GrammarV1UnrestrictedRendezvousError
      (ProcessCommunicationState, GrammarV1UnrestrictedMessageValueFlow)
grammarV1CheckUnrestrictedComponentRendezvous
    instanceValue network communication sender receiver rootValue = do
  let payloadParameter = resolvedComponentSendPayloadParameter sender
      checkedMode = provisionedComponentParameterCheckedMode payloadParameter
      expectedOccurrence = resolvedComponentSendPayloadOccurrence sender
      actualOccurrence = rootEntryScalarOccurrence rootValue
      literal = rootEntryScalarValue rootValue
      expectedType = checkedBindingType checkedMode
      actualType = scalarLiteralCoreType literal
  case checkedBindingMode checkedMode of
    Unrestricted -> Right ()
    other -> Left (GrammarV1UnrestrictedRendezvousSenderModeMismatch other)
  if actualOccurrence == expectedOccurrence
    then Right ()
    else Left
      (GrammarV1UnrestrictedRendezvousEntryOccurrenceMismatch
        expectedOccurrence actualOccurrence)
  if scalarLiteralInRange literal
    then Right ()
    else Left (GrammarV1UnrestrictedRendezvousScalarOutOfRange literal)
  if actualType == expectedType
    then Right ()
    else Left
      (GrammarV1UnrestrictedRendezvousScalarTypeMismatch expectedType actualType)
  let request = SendReceiveRendezvous
        (resolvedComponentSendRendezvousSide sender)
        (resolvedComponentReceiveRendezvousSide receiver)
  communication' <- mapLeft GrammarV1UnrestrictedRendezvousProcessError $
    checkProcessCommunicationState instanceValue network communication request
  let senderBinder = provisionedComponentParameterBinder payloadParameter
      receiverBinder = resolvedComponentReceivePayloadBinder receiver
  Right
    ( communication'
    , GrammarV1UnrestrictedMessageValueFlow
        { unrestrictedValueFlowEntryOccurrence = expectedOccurrence
        , unrestrictedValueFlowSenderBinder = senderBinder
        , unrestrictedValueFlowReceiverBinder = receiverBinder
        , unrestrictedValueFlowType = expectedType
        , unrestrictedValueFlowValue = literal
        }
    )

scalarLiteralCoreType :: ScalarLiteral -> Ty
scalarLiteralCoreType literal =
  case scalarLiteralType literal of
    ScalarBool -> TyBool
    ScalarUInt width -> TyUInt width

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
