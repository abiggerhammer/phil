{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( BinaryProtocolFamily (..)
  , ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolBinderScope
  ( GrammarV1CheckedProtocolBinder (..)
  , GrammarV1CheckedProtocolBinderScope (..)
  , GrammarV1CheckedProtocolRoleScope (..)
  , grammarV1CheckedProtocolBinderScope
  )
import Phil.Surface.GrammarV1.SemanticProtocolRoles
  ( grammarV1CheckedSemanticBinaryProtocolFamily
  , grammarV1CheckedSemanticProtocolRoleTemplates
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
    [ test "SURF-009 protocol sessions consume generated binder names in dependent payloads"
        semanticDependentMessagesUseGeneratedNames
    , test "SURF-009 semantic protocol sessions are alpha-stable at Core identity"
        semanticProtocolAlphaStable
    , test "SURF-009 sibling protocol branches retain disjoint semantic binder identity"
        semanticBranchScopesAreDisjoint
    , test "SURF-009 semantic sessions reject missing or misordered binder evidence"
        semanticSessionEvidenceMismatchPreserved
    , test "SURF-009 semantic protocol session competence remains bounded"
        semanticProtocolCompetenceBoundary
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

semanticDependentMessagesUseGeneratedNames :: Either String ()
semanticDependentMessagesUseGeneratedNames = do
  protocol <- onlyProtocol dependentProtocolSource
  let declarationKey = DeclarationKey "decl.SemanticProtocolDependent"
      interfaceRevision = InterfaceRevision "protocol.semantic.interface.v1"
  scope <- checkedBinderScope declarationKey protocol
  (clientBinders, serverBinders) <- twoRoleBinders scope
  case (clientBinders, serverBinders) of
    ([clientPayload, clientTag], [serverPayload, serverTag]) -> do
      let clientPayloadName = resolvedName clientPayload
          clientTagName = resolvedName clientTag
          serverPayloadName = resolvedName serverPayload
          serverTagName = resolvedName serverTag
      assert
        (clientPayloadName /= Name "payload" && clientTagName /= Name "tag")
        "Client semantic session reused source binder spelling"
      assert
        (serverPayloadName /= Name "incoming" && serverTagName /= Name "tag2")
        "Server semantic session reused source binder spelling"
      assert (clientPayloadName /= serverPayloadName)
        "sibling role binders reused one semantic Core name"
      ((clientKey, clientTemplate), (serverKey, serverTemplate), steps) <-
        checkedSemanticRoles declarationKey protocol
      assert (clientKey == ProtocolRoleKey "Client" && serverKey == ProtocolRoleKey "Server")
        "semantic protocol role order changed"
      assert (null steps) "primitive/dependent semantic protocol unexpectedly focused"
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
        "Client dependent payload did not use resolver-issued semantic identity"
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
        "Server dependent payload did not use resolver-issued semantic identity"
      family <- case grammarV1CheckedSemanticBinaryProtocolFamily
          emptyStaticContext declarationKey interfaceRevision protocol of
        Just (Right (value, familySteps)) -> do
          assert (null familySteps) "semantic family changed focusing trace"
          Right value
        other -> Left ("semantic protocol family did not close: " <> show other)
      assert (protocolFamilyDeclarationKey family == declarationKey)
        "semantic protocol family lost supplied declaration identity"
      assert (protocolFamilyInterfaceRevision family == interfaceRevision)
        "semantic protocol family lost supplied interface revision"
      assert (protocolFamilyPrimarySession family == clientTemplate)
        "semantic protocol family did not retain exact primary template"
    other -> Left ("unexpected semantic protocol binder shape: " <> show other)

semanticProtocolAlphaStable :: Either String ()
semanticProtocolAlphaStable = do
  original <- onlyProtocol dependentProtocolSource
  renamed <- onlyProtocol renamedDependentProtocolSource
  let declarationKey = DeclarationKey "decl.SemanticProtocolAlpha"
  originalScope <- checkedBinderScope declarationKey original
  renamedScope <- checkedBinderScope declarationKey renamed
  let originalNames = allBinderNames originalScope
      renamedNames = allBinderNames renamedScope
  assert (originalNames == renamedNames)
    "alpha-renaming changed resolver-issued protocol Core names"
  originalRoles <- checkedSemanticRoles declarationKey original
  renamedRoles <- checkedSemanticRoles declarationKey renamed
  assert (originalRoles == renamedRoles)
    "alpha-renaming changed semantic protocol templates or focusing trace"

semanticBranchScopesAreDisjoint :: Either String ()
semanticBranchScopesAreDisjoint = do
  protocol <- onlyProtocol branchProtocolSource
  let declarationKey = DeclarationKey "decl.SemanticProtocolBranches"
  scope <- checkedBinderScope declarationKey protocol
  case grammarV1CheckedProtocolRoles scope of
    clientScope : _ ->
      case map resolvedName (grammarV1CheckedProtocolRoleBinders clientScope) of
        [goItem, goInside, stopItem, stopInside] -> do
          assert (goItem /= stopItem && goInside /= stopInside)
            "sibling protocol branches reused semantic binder identity"
          ((_, clientTemplate), (_, _), _) <- checkedSemanticRoles declarationKey protocol
          case clientTemplate of
            ProtocolTemplateSelect [goBranch, stopBranch] -> do
              checkBranch "Go" goItem goInside goBranch
              checkBranch "Stop" stopItem stopInside stopBranch
            other -> Left ("expected semantic select template, got " <> show other)
        other -> Left ("unexpected Client branch binder names: " <> show other)
    _ -> Left "semantic branch fixture did not produce Client role scope"
  where
    checkBranch label itemName insideName branch = do
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

semanticSessionEvidenceMismatchPreserved :: Either String ()
semanticSessionEvidenceMismatchPreserved = do
  protocol <- onlyProtocol dependentProtocolSource
  let declarationKey = DeclarationKey "decl.SemanticProtocolEvidence"
  scope <- checkedBinderScope declarationKey protocol
  case (grammarV1ProtocolRoles protocol, grammarV1CheckedProtocolRoles scope) of
    (Located _ clientRole : _, clientScope : _) -> do
      let binders = grammarV1CheckedProtocolRoleBinders clientScope
      case binders of
        _first : rest ->
          case grammarV1CheckedSemanticSession
              emptyStaticContext
              (ProtocolRoleKey "Client")
              rest
              (locatedValue (grammarV1RoleSessionExpression clientRole)) of
            Just (Left GrammarV1SemanticSessionBinderEvidenceMismatch {}) -> Right ()
            other -> Left
              ("misordered semantic protocol binder evidence was not explicit: "
                <> show other)
        [] -> Left "evidence mismatch fixture unexpectedly had no Client binders"
    _ -> Left "evidence mismatch fixture did not preserve role alignment"

semanticProtocolCompetenceBoundary :: Either String ()
semanticProtocolCompetenceBoundary = do
  guarded <- onlyProtocol guardedProtocolSource
  generic <- onlyProtocol genericProtocolSource
  let declarationKey = DeclarationKey "decl.SemanticProtocolBoundary"
  assert
    (grammarV1CheckedSemanticProtocolRoleTemplates
      emptyStaticContext declarationKey guarded == Nothing)
    "guard-bearing protocol escaped semantic session competence"
  assert
    (grammarV1CheckedSemanticProtocolRoleTemplates
      emptyStaticContext declarationKey generic == Nothing)
    "generic protocol escaped closed semantic session competence"

checkedSemanticRoles
  :: DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Either
      String
      ( (ProtocolRoleKey, ProtocolSessionTemplate)
      , (ProtocolRoleKey, ProtocolSessionTemplate)
      , [a]
      )
checkedSemanticRoles declarationKey protocol =
  case grammarV1CheckedSemanticProtocolRoleTemplates
      emptyStaticContext declarationKey protocol of
    Just (Right ((client, server), steps)) -> Right (client, server, coerceSteps steps)
    other -> Left ("expected checked semantic protocol roles, got " <> show other)
  where
    coerceSteps :: [b] -> [a]
    coerceSteps [] = []
    coerceSteps _ = error "checkedSemanticRoles: nonempty focusing trace requires explicit type"

checkedBinderScope
  :: DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Either String GrammarV1CheckedProtocolBinderScope
checkedBinderScope declarationKey protocol =
  case grammarV1CheckedProtocolBinderScope declarationKey protocol of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked protocol binder scope, got " <> show other)

twoRoleBinders
  :: GrammarV1CheckedProtocolBinderScope
  -> Either String ([GrammarV1CheckedProtocolBinder], [GrammarV1CheckedProtocolBinder])
twoRoleBinders scope = case grammarV1CheckedProtocolRoles scope of
  [client, server] -> Right
    ( grammarV1CheckedProtocolRoleBinders client
    , grammarV1CheckedProtocolRoleBinders server
    )
  other -> Left ("expected two protocol role scopes, got " <> show (length other))

resolvedName :: GrammarV1CheckedProtocolBinder -> Name
resolvedName =
  grammarV1ResolvedBinderCoreName . grammarV1CheckedProtocolBinderResolved

allBinderNames :: GrammarV1CheckedProtocolBinderScope -> [Name]
allBinderNames scope =
  [ resolvedName binder
  | role <- grammarV1CheckedProtocolRoles scope
  , binder <- grammarV1CheckedProtocolRoleBinders role
  ]

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "semantic-protocol-roles" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1ProtocolDeclaration protocol -> Right protocol
        other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left
      ("expected one protocol declaration, got " <> show (length declarations))

dependentProtocolSource :: Text.Text
dependentProtocolSource = Text.unlines
  [ "protocol SemanticDependent {"
  , "  role Client = send (payload : Bytes[4]) then"
  , "    send (tag : Bytes[len(payload)]) then end Done;"
  , "  role Server = receive (incoming : Bytes[4]) then"
  , "    receive (tag2 : Bytes[len(incoming)]) then end Done;"
  , "}"
  ]

renamedDependentProtocolSource :: Text.Text
renamedDependentProtocolSource = Text.unlines
  [ "protocol RenamedSemanticDependent {"
  , "  role Client = send (bytes : Bytes[4]) then"
  , "    send (checksum : Bytes[len(bytes)]) then end Done;"
  , "  role Server = receive (data : Bytes[4]) then"
  , "    receive (check : Bytes[len(data)]) then end Done;"
  , "}"
  ]

branchProtocolSource :: Text.Text
branchProtocolSource = Text.unlines
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

guardedProtocolSource :: Text.Text
guardedProtocolSource = Text.unlines
  [ "protocol GuardedSemantic {"
  , "  role Client = send (x : U8) when x == x then end Done;"
  , "  role Server = receive (y : U8) when y == y then end Done;"
  , "}"
  ]

genericProtocolSource :: Text.Text
genericProtocolSource = Text.unlines
  [ "protocol GenericSemantic[T : Type] {"
  , "  role Client = send (x : U8) then end Done;"
  , "  role Server = receive (y : U8) then end Done;"
  , "}"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
