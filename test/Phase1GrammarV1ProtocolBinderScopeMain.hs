{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.List as List
import qualified Data.Text as Text
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Static (DeclarationKey (..))
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
    , "}"
    ]
  checked <- checkedProtocol (DeclarationKey "decl.BranchScope") protocol
  role <- exactlyOne "protocol role" (grammarV1CheckedProtocolRoles checked)
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
    , "}"
    ]
  checked <- checkedProtocol (DeclarationKey "decl.DependentBranch") protocol
  role <- exactlyOne "protocol role" (grammarV1CheckedProtocolRoles checked)
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

checkedProtocol :: DeclarationKey -> GrammarV1ProtocolDecl -> Either String GrammarV1CheckedProtocolBinderScope
checkedProtocol declarationKey protocol =
  case grammarV1CheckedProtocolBinderScope declarationKey protocol of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked protocol binder scope, got " <> show other)

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
