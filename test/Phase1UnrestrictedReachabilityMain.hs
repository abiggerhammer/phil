{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.Static
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CONC-011 immutable unrestricted values may copy across processes" immutableCopyAccepted
    , test "CONC-011 unrestricted wrapper cannot alias one stateful occurrence across processes" hiddenSharedStateRejects
    , test "CONC-011 protocol-mediated proxies may share access to separately owned state" protocolMediatedProxyAccepted
    , test "CONC-011 same-process direct aliases remain a local semantic question" sameProcessDirectAliasesAccepted
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

immutableCopyAccepted :: Either String ()
immutableCopyAccepted = do
  network <- baseNetwork
  let (owner, clientA, clientB) = processKeys network
      sharedValue = ActivationOccurrenceKey "config-value"
      left = unrestrictedBinding
        sharedValue "config-a" (TyOpaque "ImmutableConfig")
        ExtensionalImmutableReachability
      right = unrestrictedBinding
        sharedValue "config-b" (TyOpaque "ImmutableConfig")
        ExtensionalImmutableReachability
  (_, state) <- mapLeft show $ activateProcessState network
    [ ProcessActivationContract owner []
    , ProcessActivationContract clientA [left]
    , ProcessActivationContract clientB [right]
    ]
  leftContext <- requireContext clientA state
  rightContext <- requireContext clientB state
  assert (Map.member (Name "config-a") (unrestrictedBindings leftContext))
    "client A did not receive immutable unrestricted copy"
  assert (Map.member (Name "config-b") (unrestrictedBindings rightContext))
    "client B did not receive immutable unrestricted copy"
  assert (Map.null (activationDirectStatefulReachability state))
    "immutable unrestricted copy was incorrectly classified as stateful reachability"

hiddenSharedStateRejects :: Either String ()
hiddenSharedStateRejects = do
  network <- baseNetwork
  let (owner, clientA, clientB) = processKeys network
      stateKey = ActivationOccurrenceKey "qualified-provider-state"
      wrapperA = unrestrictedBinding
        (ActivationOccurrenceKey "provider-wrapper-a")
        "provider-a"
        (TyOpaque "InterferenceQualifiedProvider")
        (DirectStatefulReachability stateKey)
      wrapperB = unrestrictedBinding
        (ActivationOccurrenceKey "provider-wrapper-b")
        "provider-b"
        (TyOpaque "InterferenceQualifiedProvider")
        (DirectStatefulReachability stateKey)
  case activateProcessState network
      [ ProcessActivationContract owner []
      , ProcessActivationContract clientA [wrapperA]
      , ProcessActivationContract clientB [wrapperB]
      ] of
    Left (CrossProcessDirectStatefulAlias actualKey firstProcess firstName secondProcess secondName) -> do
      assert (actualKey == stateKey)
        "shared-state rejection named wrong reachable semantic occurrence"
      let actual = Set.fromList
            [ (firstProcess, firstName)
            , (secondProcess, secondName)
            ]
          expected = Set.fromList
            [ (clientA, Name "provider-a")
            , (clientB, Name "provider-b")
            ]
      assert (actual == expected)
        "shared-state rejection lost the two process-local wrapper aliases"
    other -> Left ("unrestricted provider wrappers laundered shared state: " <> show other)

protocolMediatedProxyAccepted :: Either String ()
protocolMediatedProxyAccepted = do
  network <- baseNetwork
  let (owner, clientA, clientB) = processKeys network
      stateKey = ActivationOccurrenceKey "service-state"
      stateOwner = ActivationBinding
        { activationOccurrenceKey = stateKey
        , activationLocalName = Name "service-owner"
        , activationCheckedTypeMode = CheckedTypeMode (TyOpaque "ServiceState") Linear
        , activationBindingOrigin = TargetParameterOrigin "service.state"
        , activationReachability = DirectStatefulReachability stateKey
        , activationStartsSharedLoan = False
        }
      proxyA = unrestrictedBinding
        (ActivationOccurrenceKey "proxy-a")
        "proxy-a"
        (TyOpaque "ProtocolMediatedServiceProxy")
        (ProtocolMediatedReachability stateKey)
      proxyB = unrestrictedBinding
        (ActivationOccurrenceKey "proxy-b")
        "proxy-b"
        (TyOpaque "ProtocolMediatedServiceProxy")
        (ProtocolMediatedReachability stateKey)
  (_, state) <- mapLeft show $ activateProcessState network
    [ ProcessActivationContract owner [stateOwner]
    , ProcessActivationContract clientA [proxyA]
    , ProcessActivationContract clientB [proxyB]
    ]
  assert
    (Map.lookup stateKey (activationRestrictedOwners state)
      == Just (owner, Name "service-owner"))
    "separately owned service state lost its exact restricted owner"
  assert
    (Map.lookup stateKey (activationDirectStatefulReachability state)
      == Just (owner, Name "service-owner"))
    "stateful service owner lost its exact direct-reachability identity"
  contextA <- requireContext clientA state
  contextB <- requireContext clientB state
  assert (Map.member (Name "proxy-a") (unrestrictedBindings contextA))
    "client A protocol proxy was not admitted"
  assert (Map.member (Name "proxy-b") (unrestrictedBindings contextB))
    "client B protocol proxy was not admitted"

sameProcessDirectAliasesAccepted :: Either String ()
sameProcessDirectAliasesAccepted = do
  network <- baseNetwork
  let (owner, clientA, clientB) = processKeys network
      stateKey = ActivationOccurrenceKey "process-local-state"
      aliasA = unrestrictedBinding
        (ActivationOccurrenceKey "local-wrapper-a")
        "local-a"
        (TyOpaque "LocalStateWrapper")
        (DirectStatefulReachability stateKey)
      aliasB = unrestrictedBinding
        (ActivationOccurrenceKey "local-wrapper-b")
        "local-b"
        (TyOpaque "LocalStateWrapper")
        (DirectStatefulReachability stateKey)
  (_, state) <- mapLeft show $ activateProcessState network
    [ ProcessActivationContract owner []
    , ProcessActivationContract clientA [aliasA, aliasB]
    , ProcessActivationContract clientB []
    ]
  context <- requireContext clientA state
  assert
    ( Map.member (Name "local-a") (unrestrictedBindings context)
      && Map.member (Name "local-b") (unrestrictedBindings context) )
    "same-process aliases were incorrectly rejected by cross-process ownership rule"

unrestrictedBinding
  :: ActivationOccurrenceKey
  -> Text
  -> Ty
  -> ActivationReachability
  -> ActivationBinding
unrestrictedBinding occurrence name ty reachability = ActivationBinding
  { activationOccurrenceKey = occurrence
  , activationLocalName = Name name
  , activationCheckedTypeMode = CheckedTypeMode ty Unrestricted
  , activationBindingOrigin = TargetParameterOrigin ("binding." <> name)
  , activationReachability = reachability
  , activationStartsSharedLoan = False
  }

requireContext
  :: ProcessKey
  -> ProcessActivationState
  -> Either String ResourceContext
requireContext processKey state =
  maybe (Left "missing activated process context") Right
    (Map.lookup processKey (activationProcessContexts state))

baseNetwork :: Either String ProcessNetwork
baseNetwork = do
  graph <- mapLeft show rootGraph
  mapLeft show $ elaborateProcessNetwork graph [siteOwner, siteA, siteB]

processKeys :: ProcessNetwork -> (ProcessKey, ProcessKey, ProcessKey)
processKeys network =
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
  in ( deriveProcessKey rootRevision (processSiteKey siteOwner)
     , deriveProcessKey rootRevision (processSiteKey siteA)
     , deriveProcessKey rootRevision (processSiteKey siteB)
     )

rootGraph :: Either ArchitectureInstantiationError ArchitectureInstanceGraph
rootGraph = instantiateArchitecture rootKey rootSpec

rootSpec :: ArchitectureNodeSpec
rootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ ArchitectureChildSpec slotOwner workerSpec
      , ArchitectureChildSpec slotA workerSpec
      , ArchitectureChildSpec slotB workerSpec
      ]
  , architectureNodeReferences = []
  }

workerSpec :: ArchitectureNodeSpec
workerSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "worker"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

declaration :: Text -> DeclarationIdentity
declaration label = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation
      { declarationDisplayName = label
      , declarationModulePath = []
      }
  , declarationKey = DeclarationKey ("decl-" <> label)
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

siteOwner, siteA, siteB :: ProcessDeclarationSite
siteOwner = ProcessDeclarationSite (ProcessSiteKey "site-owner") targetOwner
siteA = ProcessDeclarationSite (ProcessSiteKey "site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "site-b") targetB

rootKey, targetOwner, targetA, targetB :: InstanceKey
rootKey = InstanceKey "root-instance"
targetOwner = scopedInstanceKey rootKey slotOwner
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotOwner, slotA, slotB :: OccurrenceSlotKey
slotOwner = OccurrenceSlotKey "worker-owner"
slotA = OccurrenceSlotKey "worker-a"
slotB = OccurrenceSlotKey "worker-b"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
