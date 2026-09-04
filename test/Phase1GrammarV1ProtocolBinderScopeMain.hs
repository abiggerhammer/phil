{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Focusing (FocusingError (UnknownClaim))
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceState (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  , GrammarV1LexicalReferenceError (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolBinderScope
  ( GrammarV1CheckedProtocolBinder (..)
  , GrammarV1CheckedProtocolBinderScope (..)
  , GrammarV1CheckedProtocolGuard (..)
  , GrammarV1CheckedProtocolRoleScope (..)
  , GrammarV1ProtocolBinderScopeError (..)
  , grammarV1CheckedProtocolBinderScope
  )
import Phil.Surface.GrammarV1.ProtocolGuardChecking
  ( GrammarV1CheckedProtocolCoreGuard (..)
  , GrammarV1ProtocolGuardCheckingError (..)
  , grammarV1CheckedProtocolCoreGuards
  )
import Phil.Surface.GrammarV1.SemanticProtocolRoles
  ( grammarV1CheckedSemanticProtocolRoleTemplates
  )
import Phil.Surface.GrammarV1.SemanticSessionSemantics
  ( GrammarV1SemanticSessionError (..)
  , grammarV1CheckedSemanticSession
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 message binders persist within a role and close before sibling roles"
        messageBindersPersistOnlyWithinRole
    , test "SURF-009 branch payload and nested message binders are sibling-scoped"
        branchScopesAreDisjoint
    , test "SURF-009 branch payload telescopes resolve earlier binders"
        dependentBranchPayloadResolvesEarlierBinder
    , test "SURF-009 branch payload telescopes reject forward references"
        branchPayloadForwardReferenceRejects
    , test "SURF-009 branch payloads cannot shadow active message binders"
        branchPayloadCannotShadowMessage
    , test "SURF-009 sequential message binders reject duplicate active spelling"
        sequentialMessageDuplicateRejects
    , test "SURF-009 protocol binder alpha-renaming preserves semantic identity"
        protocolAlphaRenamingPreservesIdentity
    , test "SURF-009 protocol guards use generated semantic names in SurfaceState"
        protocolGuardStateUsesSemanticNames
    , test "SURF-009 dependent protocol guard types use semantic binder dependencies"
        dependentProtocolGuardUsesSemanticType
    , test "SURF-009 checked protocol guards are alpha-stable at Core identity"
        protocolCoreGuardAlphaRenamingPreservesIdentity
    , test "SURF-009 protocol guard Core focusing errors remain explicit"
        protocolCoreGuardFocusingErrorPreserved
    , test "SURF-009 protocol sessions consume generated binder names in dependent payloads"
        semanticProtocolSessionsUseGeneratedNames
    , test "SURF-009 semantic protocol sessions are alpha-stable at Core identity"
        semanticProtocolSessionsAreAlphaStable
    , test "SURF-009 semantic protocol branch state remains sibling-local"
        semanticProtocolBranchStateIsSiblingLocal
    , test "SURF-009 semantic protocol sessions require exact binder evidence"
        semanticProtocolSessionEvidenceMismatch
    , test "SURF-009 semantic protocol session competence remains bounded"
        semanticProtocolSessionCompetenceBoundary
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

messageBindersPersistOnlyWithinRole :: Either String ()
messageBindersPersistOnlyWithinRole = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol MessageScope {"
    , "  role Client = send (n : U8) when n == n then"
    , "    send (payload : Bytes[n]) when n == n then end Done;"
    , "  role Server = receive (n : U8) when n == n then"
    , "    receive (payload : Bytes[n]) when n == n then end Done;"
    , "}"
    ]
  checked <- checkedProtocol (DeclarationKey "decl.MessageScope") protocol
  case grammarV1CheckedProtocolRoles checked of
    [client, server] -> do
      assert (grammarV1CheckedProtocolRole client == ProtocolRoleKey "Client") "first role was not Client"
      assert (grammarV1CheckedProtocolRole server == ProtocolRoleKey "Server") "second role was not Server"
      case (grammarV1CheckedProtocolRoleBinders client, grammarV1CheckedProtocolRoleBinders server) of
        ([clientN, clientPayload], [serverN, serverPayload]) -> do
          let clientNBinder = resolved clientN
              clientPayloadBinder = resolved clientPayload
              serverNBinder = resolved serverN
              serverPayloadBinder = resolved serverPayload
              allBinders = [clientNBinder, clientPayloadBinder, serverNBinder, serverPayloadBinder]
          assert (map (grammarV1BinderOrdinal . grammarV1ResolvedBinderKey) allBinders == [0, 1, 2, 3])
            "role-local binders did not use one declaration-wide ordinal stream"
          assert (grammarV1ResolvedBinderKey clientNBinder /= grammarV1ResolvedBinderKey serverNBinder)
            "same-spelled binders in sibling roles reused identity"
          dependency <- exactlyOne "Client payload type dependency"
            (grammarV1CheckedProtocolBinderTypeReferences clientPayload)
          assert (referenceKey dependency == grammarV1ResolvedBinderKey clientNBinder)
            "later Client message type did not resolve earlier n"
          assertRoleGuardKey client clientNBinder
          assertRoleGuardKey server serverNBinder
          case grammarV1ResolveLocal
              (Located (grammarV1ResolvedBinderSourceSpan clientNBinder) "n")
              (grammarV1CheckedProtocolFinalScope checked) of
            Left (GrammarV1BinderNotInScope _) -> Right ()
            other -> Left ("role-local n leaked out of protocol declaration: " <> show other)
        other -> Left ("unexpected role binder shape: " <> show other)
    other -> Left ("expected two checked roles, got " <> show other)

branchScopesAreDisjoint :: Either String ()
branchScopesAreDisjoint = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol BranchScope {"
    , "  role Client = select {"
    , "    Go(item : U8) when item == item =>"
    , "      send (inside : U8) when inside == item then end Done"
    , "    | Stop(item : U8) when item == item =>"
    , "      send (inside : U8) when inside == item then end Done"
    , "  };"
    , "  role Server = end Done;"
    , "}"
    ]
  checked <- checkedProtocol (DeclarationKey "decl.BranchScope") protocol
  role <- roleByKey (ProtocolRoleKey "Client") (grammarV1CheckedProtocolRoles checked)
  let binders = map resolved (grammarV1CheckedProtocolRoleBinders role)
  assert (map grammarV1ResolvedBinderDisplayName binders == ["item", "inside", "item", "inside"])
    "branch-local binder traversal did not preserve source order"
  assert (map (grammarV1BinderOrdinal . grammarV1ResolvedBinderKey) binders == [0, 1, 2, 3])
    "sibling branch binder identities did not remain monotone"
  assert (List.nub (map grammarV1ResolvedBinderKey binders) == map grammarV1ResolvedBinderKey binders)
    "sibling branches reused semantic binder identity"
  case (binders, grammarV1CheckedProtocolRoleGuards role) of
    ([goItem, goInside, stopItem, stopInside], [goGuard, goMessageGuard, stopGuard, stopMessageGuard]) -> do
      assertGuardKeys goGuard [goItem, goItem]
      assertGuardKeys goMessageGuard [goInside, goItem]
      assertGuardKeys stopGuard [stopItem, stopItem]
      assertGuardKeys stopMessageGuard [stopInside, stopItem]
    other -> Left ("unexpected branch binder/guard trace: " <> show other)

dependentBranchPayloadResolvesEarlierBinder :: Either String ()
dependentBranchPayloadResolvesEarlierBinder = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol DependentBranch {"
    , "  role Client = select {"
    , "    Go(n : U8, payload : Bytes[n]) when n >= 0 => end Done"
    , "  };"
    , "  role Server = end Done;"
    , "}"
    ]
  checked <- checkedProtocol (DeclarationKey "decl.DependentBranch") protocol
  role <- roleByKey (ProtocolRoleKey "Client") (grammarV1CheckedProtocolRoles checked)
  case grammarV1CheckedProtocolRoleBinders role of
    [nSource, payloadSource] -> do
      dependency <- exactlyOne "dependent payload type reference"
        (grammarV1CheckedProtocolBinderTypeReferences payloadSource)
      assert (referenceKey dependency == grammarV1ResolvedBinderKey (resolved nSource))
        "later branch payload type did not resolve earlier n"
      guard <- exactlyOne "dependent branch guard" (grammarV1CheckedProtocolRoleGuards role)
      assertGuardKeys guard [resolved nSource]
    other -> Left ("expected n/payload branch telescope, got " <> show other)

branchPayloadForwardReferenceRejects :: Either String ()
branchPayloadForwardReferenceRejects = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol ForwardBranch {"
    , "  role Client = select {"
    , "    Go(payload : Bytes[n], n : U8) => end Done"
    , "  };"
    , "  role Server = end Done;"
    , "}"
    ]
  case grammarV1CheckedProtocolBinderScope (DeclarationKey "decl.ForwardBranch") protocol of
    Just (Left (GrammarV1ProtocolReferenceError
      (GrammarV1LexicalReferenceForwardReference missing))) ->
        assert (locatedValue missing == "n") "forward-reference diagnostic lost future spelling"
    other -> Left ("expected branch-payload forward-reference rejection, got " <> show other)

branchPayloadCannotShadowMessage :: Either String ()
branchPayloadCannotShadowMessage = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol ShadowBranch {"
    , "  role Client = send (item : U8) then select {"
    , "    Go(item : U8) => end Done"
    , "  };"
    , "  role Server = end Done;"
    , "}"
    ]
  case grammarV1CheckedProtocolBinderScope (DeclarationKey "decl.ShadowBranch") protocol of
    Just (Left (GrammarV1ProtocolBinderError
      (GrammarV1ActiveShadowing shadowing previous))) -> do
        assert (locatedValue shadowing == "item") "active-shadow diagnostic lost branch spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "item") "active-shadow diagnostic lost message binder"
    other -> Left ("expected branch-payload active-shadow rejection, got " <> show other)

sequentialMessageDuplicateRejects :: Either String ()
sequentialMessageDuplicateRejects = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol DuplicateMessage {"
    , "  role Client = send (value : U8) then"
    , "    send (value : U8) then end Done;"
    , "  role Server = end Done;"
    , "}"
    ]
  case grammarV1CheckedProtocolBinderScope (DeclarationKey "decl.DuplicateMessage") protocol of
    Just (Left (GrammarV1ProtocolBinderError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "value") "duplicate message diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "value") "duplicate diagnostic lost first binder"
    other -> Left ("expected duplicate message-binder rejection, got " <> show other)

protocolAlphaRenamingPreservesIdentity :: Either String ()
protocolAlphaRenamingPreservesIdentity = do
  original <- onlyProtocol $ Text.unlines
    [ "protocol AlphaProtocol {"
    , "  role Client = send (n : U8) when n == n then select {"
    , "    Go(item : Bytes[n]) when item == item => end Done"
    , "  };"
    , "  role Server = receive (m : U8) when m == m then offer {"
    , "    Go(value : Bytes[m]) when value == value => end Done"
    , "  };"
    , "}"
    ]
  renamed <- onlyProtocol $ Text.unlines
    [ "protocol AlphaProtocol {"
    , "    role Client = send (count : U8) when count == count then select {"
    , "      Go(payload : Bytes[count]) when payload == payload => end Done"
    , "    };"
    , "    role Server = receive (size : U8) when size == size then offer {"
    , "      Go(bytes : Bytes[size]) when bytes == bytes => end Done"
    , "    };"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.AlphaProtocol"
  originalChecked <- checkedProtocol declarationKey original
  renamedChecked <- checkedProtocol declarationKey renamed
  let originalBinders = allResolvedBinders originalChecked
      renamedBinders = allResolvedBinders renamedChecked
  assert (map grammarV1ResolvedBinderKey originalBinders == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming changed protocol BinderKeys"
  assert (map grammarV1ResolvedBinderCoreName originalBinders == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming changed protocol Core names"
  assert (map grammarV1ResolvedBinderDisplayName originalBinders == ["n", "item", "m", "value"])
    "original protocol binder spellings changed"
  assert (map grammarV1ResolvedBinderDisplayName renamedBinders == ["count", "payload", "size", "bytes"])
    "renamed protocol binder spellings changed"

protocolGuardStateUsesSemanticNames :: Either String ()
protocolGuardStateUsesSemanticNames = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol CoreGuard {"
    , "  role Client = send (n : U8) when n == n then end Done;"
    , "  role Server = receive (value : U8) when value == value then end Done;"
    , "}"
    ]
  guards <- checkedCoreGuards (DeclarationKey "decl.CoreGuard") protocol
  firstGuard <- exactlyOne "first Core guard" (take 1 guards)
  binder <- exactlyOne
    "first Core guard binder"
    (grammarV1CheckedProtocolCoreGuardBinders firstGuard)
  let semanticName@(Name semanticText) = grammarV1ResolvedBinderCoreName binder
      state = grammarV1CheckedProtocolCoreGuardState firstGuard
      context = resourceContext (stateCore state)
  assert (semanticText /= "n")
    "semantic protocol binder collapsed to source spelling"
  assert (Map.member semanticText (stateBindings state))
    "semantic SurfaceState did not use generated Core name"
  assert (not (Map.member "n" (stateBindings state)))
    "source spelling leaked into semantic SurfaceState"
  assert (Map.member semanticName (unrestrictedBindings context))
    "Core resource context did not use generated binder name"
  assert (not (Map.member (Name "n") (unrestrictedBindings context)))
    "Core resource context retained source spelling as identity"

dependentProtocolGuardUsesSemanticType :: Either String ()
dependentProtocolGuardUsesSemanticType = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol DependentCore {"
    , "  role Client = select {"
    , "    Go(n : U8, payload : Bytes[toNat(n)]) when payload == payload => end Done"
    , "  };"
    , "  role Server = end Done;"
    , "}"
    ]
  guards <- checkedCoreGuards (DeclarationKey "decl.DependentCore") protocol
  guard <- exactlyOne "dependent Core guard" guards
  let binders = grammarV1CheckedProtocolCoreGuardBinders guard
      state = grammarV1CheckedProtocolCoreGuardState guard
  nBinder <- binderNamed "n" binders
  payloadBinder <- binderNamed "payload" binders
  let nName = grammarV1ResolvedBinderCoreName nBinder
      Name payloadName = grammarV1ResolvedBinderCoreName payloadBinder
  payloadMeta <- maybe
    (Left "dependent payload semantic binding missing from SurfaceState")
    Right
    (Map.lookup payloadName (stateBindings state))
  assert (bindingType payloadMeta == TyBytes (RefToNat (RefVar nName)))
    ("dependent payload type did not preserve semantic n identity: " <> show (bindingType payloadMeta))

protocolCoreGuardAlphaRenamingPreservesIdentity :: Either String ()
protocolCoreGuardAlphaRenamingPreservesIdentity = do
  original <- onlyProtocol $ Text.unlines
    [ "protocol CoreAlpha {"
    , "  role Client = send (n : U8) when n == n then end Done;"
    , "  role Server = receive (m : U8) when m == m then end Done;"
    , "}"
    ]
  renamed <- onlyProtocol $ Text.unlines
    [ "protocol CoreAlpha {"
    , "  role Client = send (count : U8) when count == count then end Done;"
    , "  role Server = receive (size : U8) when size == size then end Done;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.CoreAlpha"
  originalGuards <- checkedCoreGuards declarationKey original
  renamedGuards <- checkedCoreGuards declarationKey renamed
  assert (map guardCoreNames originalGuards == map guardCoreNames renamedGuards)
    "alpha-renaming changed materialized Core binder names"
  assert
    ( map grammarV1CheckedProtocolCoreGuardProposition originalGuards
        == map grammarV1CheckedProtocolCoreGuardProposition renamedGuards
    )
    "alpha-renaming changed checked Core guard propositions"
  assert (map guardDisplayNames originalGuards /= map guardDisplayNames renamedGuards)
    "Core guard alpha test did not change source display spellings"

protocolCoreGuardFocusingErrorPreserved :: Either String ()
protocolCoreGuardFocusingErrorPreserved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol BadCoreGuard {"
    , "  role Client = send (n : U8) when Missing(n) then end Done;"
    , "  role Server = receive (value : U8) then end Done;"
    , "}"
    ]
  case grammarV1CheckedProtocolCoreGuards
      emptyStaticContext
      (DeclarationKey "decl.BadCoreGuard")
      protocol of
    Just (Left
      (GrammarV1ProtocolGuardPropositionFocusingError (UnknownClaim "Missing"))) ->
        Right ()
    other -> Left ("Core UnknownClaim was collapsed or changed: " <> show other)

semanticProtocolSessionsUseGeneratedNames :: Either String ()
semanticProtocolSessionsUseGeneratedNames = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol SemanticDependent {"
    , "  role Client = send (payload : Bytes[4]) then"
    , "    send (tag : Bytes[len(payload)]) then end Done;"
    , "  role Server = receive (incoming : Bytes[4]) then"
    , "    receive (tag2 : Bytes[len(incoming)]) then end Done;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticProtocolDependent"
  scope <- checkedProtocol declarationKey protocol
  case grammarV1CheckedProtocolRoles scope of
    [clientScope, serverScope] ->
      case
          ( grammarV1CheckedProtocolRoleBinders clientScope
          , grammarV1CheckedProtocolRoleBinders serverScope
          ) of
        ([clientPayload, clientTag], [serverPayload, serverTag]) -> do
          let clientPayloadName = semanticBinderName clientPayload
              clientTagName = semanticBinderName clientTag
              serverPayloadName = semanticBinderName serverPayload
              serverTagName = semanticBinderName serverTag
          assert
            (clientPayloadName /= Name "payload" && clientTagName /= Name "tag")
            "semantic Client session reused source binder spelling"
          assert
            (serverPayloadName /= Name "incoming" && serverTagName /= Name "tag2")
            "semantic Server session reused source binder spelling"
          assert (clientPayloadName /= serverPayloadName)
            "sibling protocol roles reused semantic binder identity"
          ((clientKey, clientTemplate), (serverKey, serverTemplate)) <-
            checkedSemanticProtocolTemplates declarationKey protocol
          assert
            (clientKey == ProtocolRoleKey "Client" && serverKey == ProtocolRoleKey "Server")
            "semantic protocol role order changed"
          assert
            (clientTemplate ==
              ProtocolTemplateSend
                clientPayloadName
                (ProtocolConcreteType (TyBytes (RefNat 4)))
                (ProtocolTemplateSend
                  clientTagName
                  (ProtocolConcreteType
                    (TyBytes (RefLen (RefVar clientPayloadName))))
                  (ProtocolTemplateEnd (Outcome "Done"))))
            "Client dependent type did not consume generated SurfaceState identity"
          assert
            (serverTemplate ==
              ProtocolTemplateReceive
                serverPayloadName
                (ProtocolConcreteType (TyBytes (RefNat 4)))
                (ProtocolTemplateReceive
                  serverTagName
                  (ProtocolConcreteType
                    (TyBytes (RefLen (RefVar serverPayloadName))))
                  (ProtocolTemplateEnd (Outcome "Done"))))
            "Server dependent type did not consume generated SurfaceState identity"
        other -> Left ("unexpected semantic protocol binder shape: " <> show other)
    other -> Left ("expected two semantic protocol role scopes, got " <> show other)

semanticProtocolSessionsAreAlphaStable :: Either String ()
semanticProtocolSessionsAreAlphaStable = do
  original <- onlyProtocol $ Text.unlines
    [ "protocol SemanticAlpha {"
    , "  role Client = send (payload : Bytes[4]) then"
    , "    send (tag : Bytes[len(payload)]) then end Done;"
    , "  role Server = receive (incoming : Bytes[4]) then"
    , "    receive (tag2 : Bytes[len(incoming)]) then end Done;"
    , "}"
    ]
  renamed <- onlyProtocol $ Text.unlines
    [ "protocol RenamedSemanticAlpha {"
    , "  role Client = send (bytes : Bytes[4]) then"
    , "    send (checksum : Bytes[len(bytes)]) then end Done;"
    , "  role Server = receive (data : Bytes[4]) then"
    , "    receive (check : Bytes[len(data)]) then end Done;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticProtocolAlpha"
  originalScope <- checkedProtocol declarationKey original
  renamedScope <- checkedProtocol declarationKey renamed
  assert
    ( map grammarV1ResolvedBinderCoreName (allResolvedBinders originalScope)
        == map grammarV1ResolvedBinderCoreName (allResolvedBinders renamedScope)
    )
    "alpha-renaming changed protocol semantic Core names"
  originalTemplates <- checkedSemanticProtocolTemplates declarationKey original
  renamedTemplates <- checkedSemanticProtocolTemplates declarationKey renamed
  assert (originalTemplates == renamedTemplates)
    "alpha-renaming changed semantic protocol templates"

semanticProtocolBranchStateIsSiblingLocal :: Either String ()
semanticProtocolBranchStateIsSiblingLocal = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol SemanticBranches {"
    , "  role Client = select {"
    , "    Go(item : U8) => send (inside : Bytes[toNat(item)]) then end Done"
    , "    | Stop(item : U8) => send (inside : Bytes[toNat(item)]) then end Done"
    , "  };"
    , "  role Server = offer {"
    , "    Go(value : U8) => receive (received : Bytes[toNat(value)]) then end Done"
    , "    | Stop(value : U8) => receive (received : Bytes[toNat(value)]) then end Done"
    , "  };"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticProtocolBranches"
  scope <- checkedProtocol declarationKey protocol
  clientScope <- roleByKey (ProtocolRoleKey "Client") (grammarV1CheckedProtocolRoles scope)
  case map semanticBinderName (grammarV1CheckedProtocolRoleBinders clientScope) of
    [goItem, goInside, stopItem, stopInside] -> do
      assert (goItem /= stopItem && goInside /= stopInside)
        "sibling protocol branch binders reused semantic identity"
      ((_, clientTemplate), _) <- checkedSemanticProtocolTemplates declarationKey protocol
      case clientTemplate of
        ProtocolTemplateSelect [goBranch, stopBranch] -> do
          assertSemanticBranch "Go" goItem goInside goBranch
          assertSemanticBranch "Stop" stopItem stopInside stopBranch
        other -> Left ("expected semantic select template, got " <> show other)
    other -> Left ("unexpected semantic Client branch binder shape: " <> show other)

semanticProtocolSessionEvidenceMismatch :: Either String ()
semanticProtocolSessionEvidenceMismatch = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol SemanticEvidence {"
    , "  role Client = send (payload : Bytes[4]) then"
    , "    send (tag : Bytes[len(payload)]) then end Done;"
    , "  role Server = receive (incoming : Bytes[4]) then"
    , "    receive (tag2 : Bytes[len(incoming)]) then end Done;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticProtocolEvidence"
  scope <- checkedProtocol declarationKey protocol
  case (grammarV1ProtocolRoles protocol, grammarV1CheckedProtocolRoles scope) of
    (Located _ clientRole : _, clientScope : _) ->
      case grammarV1CheckedProtocolRoleBinders clientScope of
        _first : rest ->
          case grammarV1CheckedSemanticSession
              emptyStaticContext
              (ProtocolRoleKey "Client")
              rest
              (locatedValue (grammarV1RoleSessionExpression clientRole)) of
            Just
              (Left
                (GrammarV1SemanticSessionBinderEvidenceMismatch _ _ _ _)) -> Right ()
            other -> Left
              ("semantic session did not reject misordered binder evidence: "
                <> show other)
        [] -> Left "semantic evidence fixture unexpectedly had no Client binders"
    _ -> Left "semantic evidence fixture lost role/source alignment"

semanticProtocolSessionCompetenceBoundary :: Either String ()
semanticProtocolSessionCompetenceBoundary = do
  guarded <- onlyProtocol $ Text.unlines
    [ "protocol GuardedSemantic {"
    , "  role Client = send (x : U8) when x == x then end Done;"
    , "  role Server = receive (y : U8) when y == y then end Done;"
    , "}"
    ]
  generic <- onlyProtocol $ Text.unlines
    [ "protocol GenericSemantic[T : Type] {"
    , "  role Client = send (x : U8) then end Done;"
    , "  role Server = receive (y : U8) then end Done;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticProtocolBoundary"
  assert
    (grammarV1CheckedSemanticProtocolRoleTemplates
      emptyStaticContext declarationKey guarded == Nothing)
    "guard-bearing protocol escaped semantic session competence"
  assert
    (grammarV1CheckedSemanticProtocolRoleTemplates
      emptyStaticContext declarationKey generic == Nothing)
    "generic protocol escaped closed semantic session competence"

checkedSemanticProtocolTemplates
  :: DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Either
      String
      ( (ProtocolRoleKey, ProtocolSessionTemplate)
      , (ProtocolRoleKey, ProtocolSessionTemplate)
      )
checkedSemanticProtocolTemplates declarationKey protocol =
  case grammarV1CheckedSemanticProtocolRoleTemplates
      emptyStaticContext declarationKey protocol of
    Just (Right (templates, _steps)) -> Right templates
    other -> Left ("expected checked semantic protocol templates, got " <> show other)

semanticBinderName :: GrammarV1CheckedProtocolBinder -> Name
semanticBinderName =
  grammarV1ResolvedBinderCoreName . grammarV1CheckedProtocolBinderResolved

assertSemanticBranch
  :: Text.Text
  -> Name
  -> Name
  -> ProtocolBranchTemplate
  -> Either String ()
assertSemanticBranch label itemName insideName branch = do
  assert (protocolTemplateBranchLabel branch == label)
    ("semantic branch label changed for " <> Text.unpack label)
  assert
    (protocolTemplateBranchPayload branch
      == Just (itemName, ProtocolConcreteType (TyUInt 8)))
    ("semantic branch payload identity changed for " <> Text.unpack label)
  assert
    (protocolTemplateBranchContinuation branch ==
      ProtocolTemplateSend
        insideName
        (ProtocolConcreteType
          (TyBytes (RefToNat (RefVar itemName))))
        (ProtocolTemplateEnd (Outcome "Done")))
    ("branch-local dependent continuation lost semantic identity for "
      <> Text.unpack label)

checkedProtocol :: DeclarationKey -> GrammarV1ProtocolDecl -> Either String GrammarV1CheckedProtocolBinderScope
checkedProtocol declarationKey protocol =
  case grammarV1CheckedProtocolBinderScope declarationKey protocol of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked protocol binder scope, got " <> show other)

checkedCoreGuards
  :: DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Either String [GrammarV1CheckedProtocolCoreGuard]
checkedCoreGuards declarationKey protocol =
  case grammarV1CheckedProtocolCoreGuards emptyStaticContext declarationKey protocol of
    Just (Right guards) -> Right guards
    other -> Left ("expected checked protocol Core guards, got " <> show other)

resolved :: GrammarV1CheckedProtocolBinder -> GrammarV1ResolvedBinder
resolved = grammarV1CheckedProtocolBinderResolved

referenceKey :: GrammarV1CheckedLexicalReference -> GrammarV1BinderKey
referenceKey = grammarV1ResolvedBinderKey . grammarV1CheckedLexicalReferenceBinder

assertRoleGuardKey :: GrammarV1CheckedProtocolRoleScope -> GrammarV1ResolvedBinder -> Either String ()
assertRoleGuardKey role expected =
  case grammarV1CheckedProtocolRoleGuards role of
    [firstGuard, secondGuard] -> do
      assert (List.nub (map grammarV1ResolvedBinderKey (guardBinders firstGuard)) == [grammarV1ResolvedBinderKey expected])
        "first message guard did not resolve role-local n"
      assert (List.nub (map grammarV1ResolvedBinderKey (guardBinders secondGuard)) == [grammarV1ResolvedBinderKey expected])
        "later message guard did not retain earlier role-local n"
    other -> Left ("unexpected message guard trace: " <> show other)

assertGuardKeys :: GrammarV1CheckedProtocolGuard -> [GrammarV1ResolvedBinder] -> Either String ()
assertGuardKeys guard expected =
  assert
    (map grammarV1ResolvedBinderKey (guardBinders guard) == map grammarV1ResolvedBinderKey expected)
    ("guard resolved unexpected binder keys: " <> show guard)

guardBinders :: GrammarV1CheckedProtocolGuard -> [GrammarV1ResolvedBinder]
guardBinders = map grammarV1CheckedLexicalReferenceBinder . grammarV1CheckedProtocolGuardReferences

allResolvedBinders :: GrammarV1CheckedProtocolBinderScope -> [GrammarV1ResolvedBinder]
allResolvedBinders = concatMap (map resolved . grammarV1CheckedProtocolRoleBinders) . grammarV1CheckedProtocolRoles

guardCoreNames :: GrammarV1CheckedProtocolCoreGuard -> [Name]
guardCoreNames = map grammarV1ResolvedBinderCoreName . grammarV1CheckedProtocolCoreGuardBinders

guardDisplayNames :: GrammarV1CheckedProtocolCoreGuard -> [Text.Text]
guardDisplayNames = map grammarV1ResolvedBinderDisplayName . grammarV1CheckedProtocolCoreGuardBinders

binderNamed
  :: Text.Text
  -> [GrammarV1ResolvedBinder]
  -> Either String GrammarV1ResolvedBinder
binderNamed displayName binders =
  case filter ((== displayName) . grammarV1ResolvedBinderDisplayName) binders of
    [binder] -> Right binder
    matches -> Left
      ( "expected one binder named " <> Text.unpack displayName
        <> ", got " <> show (length matches)
      )

roleByKey
  :: ProtocolRoleKey
  -> [GrammarV1CheckedProtocolRoleScope]
  -> Either String GrammarV1CheckedProtocolRoleScope
roleByKey expected roles =
  case filter ((== expected) . grammarV1CheckedProtocolRole) roles of
    [role] -> Right role
    [] -> Left ("missing checked protocol role " <> show expected)
    matches -> Left
      ("duplicate checked protocol role " <> show expected <> ": " <> show (length matches))

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "protocol-binder-scope" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left ("expected one protocol declaration, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left ("expected exactly one " <> label <> ", got " <> show (length values))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right