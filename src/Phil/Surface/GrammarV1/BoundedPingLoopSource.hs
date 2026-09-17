{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.BoundedPingLoopSource
  ( GrammarV1CheckedBoundedPingLoop (..)
  , GrammarV1BoundedPingProtocolError (..)
  , GrammarV1BoundedPingLoopError (..)
  , grammarV1CheckBoundedPingProtocol
  , grammarV1CheckedBoundedPingLoop
  ) where

import Data.Text (Text)
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( BinaryProtocolFamily (..)
  , ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Core.UnicodeString (unicodeStringCoreType)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1CheckedLoopBodyStep (..)
  , GrammarV1CheckedLoopSlot (..)
  , GrammarV1CheckedLoopState (..)
  , GrammarV1LoopStateScopeError
  , grammarV1CheckedLoopExpressionInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1StateBinding (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  , grammarV1QualifiedNameParts
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1BoundedPingProtocolError
  = GrammarV1BoundedPingProtocolRoleMismatch
      ProtocolRoleKey
      ProtocolRoleKey
  | GrammarV1BoundedPingProtocolShapeMismatch ProtocolSessionTemplate
  deriving (Eq, Show)

data GrammarV1CheckedBoundedPingLoop = GrammarV1CheckedBoundedPingLoop
  { boundedPingEndpointParameter :: GrammarV1ResolvedBinder
  , boundedPingCountParameter :: GrammarV1ResolvedBinder
  , boundedPingEndpointState :: GrammarV1ResolvedBinder
  , boundedPingCountState :: GrammarV1ResolvedBinder
  }
  deriving (Eq, Show)

data GrammarV1BoundedPingLoopError
  = GrammarV1BoundedPingBinderError GrammarV1BinderScopeError
  | GrammarV1BoundedPingParameterShape [GrammarV1ResolvedBinder]
  | GrammarV1BoundedPingLoopScopeError GrammarV1LoopStateScopeError
  | GrammarV1BoundedPingLoopStateShape [GrammarV1CheckedLoopSlot]
  | GrammarV1BoundedPingLoopStateNameMismatch Text Text
  | GrammarV1BoundedPingLoopStateTypeMismatch Text
  | GrammarV1BoundedPingInitializerNotSimple Text
  | GrammarV1BoundedPingInitializerReferenceMismatch
      Text
      GrammarV1ResolvedBinder
      [GrammarV1CheckedLexicalReference]
  | GrammarV1BoundedPingLoopBodyShape [GrammarV1CheckedLoopBodyStep]
  | GrammarV1BoundedPingContinueArity Int
  | GrammarV1BoundedPingContinueActualMismatch Int Text
  | GrammarV1BoundedPingContinueReferenceMismatch
      [GrammarV1ResolvedBinder]
      [GrammarV1CheckedLexicalReference]
  deriving (Eq, Show)

grammarV1CheckBoundedPingProtocol
  :: BinaryProtocolFamily
  -> Either GrammarV1BoundedPingProtocolError ()
grammarV1CheckBoundedPingProtocol family
  | protocolFamilyPrimaryRole family /= clientRole
      || protocolFamilyPeerRole family /= serverRole =
      Left
        (GrammarV1BoundedPingProtocolRoleMismatch
          (protocolFamilyPrimaryRole family)
          (protocolFamilyPeerRole family))
  | protocolFamilyPrimarySession family /= expectedClientSession =
      Left
        (GrammarV1BoundedPingProtocolShapeMismatch
          (protocolFamilyPrimarySession family))
  | otherwise = Right ()
  where
    clientRole = ProtocolRoleKey "Client"
    serverRole = ProtocolRoleKey "Server"

expectedClientSession :: ProtocolSessionTemplate
expectedClientSession =
  ProtocolTemplateRec loopName $
    ProtocolTemplateSelect
      [ ProtocolBranchTemplate
          { protocolTemplateBranchLabel = "Ping"
          , protocolTemplateBranchPayload = Nothing
          , protocolTemplateBranchContinuation =
              ProtocolTemplateSend
                (Name "x")
                (ProtocolConcreteType (TyUInt 8))
                (ProtocolTemplateReceive
                  (Name "reply")
                  (ProtocolConcreteType unicodeStringCoreType)
                  (ProtocolTemplateVar loopName))
          }
      , ProtocolBranchTemplate
          { protocolTemplateBranchLabel = "Done"
          , protocolTemplateBranchPayload = Nothing
          , protocolTemplateBranchContinuation =
              ProtocolTemplateEnd (Outcome "Done")
          }
      ]
  where
    loopName = Name "Loop"

grammarV1CheckedBoundedPingLoop
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1BoundedPingLoopError
        GrammarV1CheckedBoundedPingLoop)
grammarV1CheckedBoundedPingLoop declarationKey component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [Located _ (GrammarV1ExpressionStatement loopSource)] -> Just $ do
        (maybeParameters, parameterScope) <- mapLeft
          GrammarV1BoundedPingBinderError
          (grammarV1ComponentParameterScope declarationKey component)
        (endpointParameter, countParameter) <-
          requireParameters (maybe [] id maybeParameters)
        checked <- case grammarV1CheckedLoopExpressionInScope
            parameterScope loopSource of
          Nothing -> Left (GrammarV1BoundedPingLoopBodyShape [])
          Just (Left err) -> Left (GrammarV1BoundedPingLoopScopeError err)
          Just (Right (value, _outerScope)) -> Right value
        (endpointSlot, countSlot) <-
          requireSlots (grammarV1CheckedLoopSlots checked)
        requireSlotName "currentEndpoint" endpointSlot
        requireSlotName "remaining" countSlot
        requireEndpointSlotType endpointSlot
        requireCountSlotType countSlot
        requireInitializer "currentEndpoint" endpointParameter endpointSlot
        requireInitializer "remaining" countParameter countSlot
        requireContinue
          (grammarV1CheckedLoopSlotBinder endpointSlot)
          (grammarV1CheckedLoopSlotBinder countSlot)
          (grammarV1CheckedLoopBodySteps checked)
        Right GrammarV1CheckedBoundedPingLoop
          { boundedPingEndpointParameter = endpointParameter
          , boundedPingCountParameter = countParameter
          , boundedPingEndpointState = grammarV1CheckedLoopSlotBinder endpointSlot
          , boundedPingCountState = grammarV1CheckedLoopSlotBinder countSlot
          }
    _ -> Nothing
  where
    requireParameters parameters = case parameters of
      [endpointParameter, countParameter]
        | grammarV1ResolvedBinderDisplayName endpointParameter == "endpoint"
        , grammarV1ResolvedBinderDisplayName countParameter == "count" ->
            Right (endpointParameter, countParameter)
      other -> Left (GrammarV1BoundedPingParameterShape other)

requireSlots
  :: [GrammarV1CheckedLoopSlot]
  -> Either
      GrammarV1BoundedPingLoopError
      (GrammarV1CheckedLoopSlot, GrammarV1CheckedLoopSlot)
requireSlots slots = case slots of
  [endpointSlot, countSlot] -> Right (endpointSlot, countSlot)
  other -> Left (GrammarV1BoundedPingLoopStateShape other)

requireSlotName
  :: Text
  -> GrammarV1CheckedLoopSlot
  -> Either GrammarV1BoundedPingLoopError ()
requireSlotName expected slot =
  let actual = grammarV1ResolvedBinderDisplayName
        (grammarV1CheckedLoopSlotBinder slot)
  in if actual == expected
      then Right ()
      else Left (GrammarV1BoundedPingLoopStateNameMismatch expected actual)

requireEndpointSlotType
  :: GrammarV1CheckedLoopSlot
  -> Either GrammarV1BoundedPingLoopError ()
requireEndpointSlotType slot =
  case grammarV1StateBindingType
      (locatedValue (grammarV1CheckedLoopSlotSource slot)) of
    Nothing -> Right ()
    Just _ -> Left
      (GrammarV1BoundedPingLoopStateTypeMismatch "currentEndpoint")

requireCountSlotType
  :: GrammarV1CheckedLoopSlot
  -> Either GrammarV1BoundedPingLoopError ()
requireCountSlotType slot =
  case grammarV1StateBindingType
      (locatedValue (grammarV1CheckedLoopSlotSource slot)) of
    Just (Located _ (GrammarV1UnsignedType "U32")) -> Right ()
    _ -> Left (GrammarV1BoundedPingLoopStateTypeMismatch "remaining")

requireInitializer
  :: Text
  -> GrammarV1ResolvedBinder
  -> GrammarV1CheckedLoopSlot
  -> Either GrammarV1BoundedPingLoopError ()
requireInitializer slotName expected slot = do
  let source = grammarV1StateBindingInitializer
        (locatedValue (grammarV1CheckedLoopSlotSource slot))
  case simpleLocalName source of
    Just _ -> Right ()
    Nothing -> Left (GrammarV1BoundedPingInitializerNotSimple slotName)
  let references = grammarV1CheckedLoopSlotInitializerReferences slot
  case references of
    [reference]
      | grammarV1ResolvedBinderKey
          (grammarV1CheckedLexicalReferenceBinder reference)
          == grammarV1ResolvedBinderKey expected -> Right ()
    _ -> Left
      (GrammarV1BoundedPingInitializerReferenceMismatch
        slotName expected references)

requireContinue
  :: GrammarV1ResolvedBinder
  -> GrammarV1ResolvedBinder
  -> [GrammarV1CheckedLoopBodyStep]
  -> Either GrammarV1BoundedPingLoopError ()
requireContinue endpointState countState steps =
  case steps of
    [GrammarV1CheckedLoopContinueStep _ actuals references] -> do
      if length actuals == 2
        then Right ()
        else Left (GrammarV1BoundedPingContinueArity (length actuals))
      requireActual 0 "currentEndpoint" (actuals !! 0)
      requireActual 1 "remaining" (actuals !! 1)
      let expected = [endpointState, countState]
          actualBinders = map grammarV1CheckedLexicalReferenceBinder references
      if map grammarV1ResolvedBinderKey actualBinders
          == map grammarV1ResolvedBinderKey expected
        then Right ()
        else Left
          (GrammarV1BoundedPingContinueReferenceMismatch expected references)
    other -> Left (GrammarV1BoundedPingLoopBodyShape other)
  where
    requireActual index expected source =
      case simpleLocalName source of
        Just actual
          | actual == expected -> Right ()
          | otherwise -> Left
              (GrammarV1BoundedPingContinueActualMismatch index actual)
        Nothing -> Left
          (GrammarV1BoundedPingContinueActualMismatch index "<non-local>")

simpleLocalName :: Located GrammarV1Expression -> Maybe Text
simpleLocalName (Located _ expression) = case expression of
  GrammarV1NameExpression reference []
    | null (grammarV1StaticReferenceArguments reference)
    , [name] <- grammarV1QualifiedNameParts
        (grammarV1StaticReferenceName reference) -> Just name
  GrammarV1ParenthesizedExpression inner -> simpleLocalName inner
  _ -> Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
