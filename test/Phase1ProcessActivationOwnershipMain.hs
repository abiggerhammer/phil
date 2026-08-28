{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
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
    [ test "CONC-003 unrestricted activation values may contract" unrestrictedCopyAccepted
    , test "CONC-003 duplicate linear activation owner rejects" duplicateLinearOwnerRejects
    , test "CONC-003 duplicate endpoint activation rejects" duplicateEndpointRejects
    , test "CONC-003 duplicate affine capability rejects" duplicateAffineCapabilityRejects
    , test "CONC-003 duplicate scoped loan owner rejects" duplicateScopedLoanRejects
    , test "CONC-003 ambient activation binding rejects" ambientBindingRejects
    , test "CONC-003 every process requires explicit activation contract" missingActivationContractRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

unrestrictedCopyAccepted :: Either String ()
unrestrictedCopyAccepted = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      sharedKey = ActivationOccurrenceKey "shared-proof-source"
      ownerA = binding "owner-a-occ" "owner-a" Linear (TyOpaque "OwnedA")
        (TargetParameterOrigin "worker-a.owner") False
      ownerB = binding "owner-b-occ" "owner-b" Linear (TyOpaque "OwnedB")
        (TargetParameterOrigin "worker-b.owner") False
      sharedA = bindingFromKey sharedKey "proof-a" Unrestricted (TyProof Truth)
        (RootEntryOrigin "root.shared-proof") False
      sharedB = bindingFromKey sharedKey "proof-b" Unrestricted (TyProof Truth)
        (RootEntryOrigin "root.shared-proof") False
  (activated, contexts) <- mapLeft show $ activateProcessContexts network
    [ ProcessActivationContract processA [ownerA, sharedA]
    , ProcessActivationContract processB [ownerB, sharedB]
    ]
  assert
    (all ((== Active) . processOccurrenceActivation)
      (Map.elems (processNetworkPopulation activated)))
    "successful activation did not activate every process exactly once"
  contextA <- lookupContext processA contexts
  contextB <- lookupContext processB contexts
  assert (Map.member (Name "proof-a") (unrestrictedBindings contextA))
    "process A did not receive unrestricted contraction copy"
  assert (Map.member (Name "proof-b") (unrestrictedBindings contextB))
    "process B did not receive unrestricted contraction copy"
  assert (Map.member (Name "owner-a") (linearBindings contextA))
    "process A lost its distinct linear owner"
  assert (Map.member (Name "owner-b") (linearBindings contextB))
    "process B lost its distinct linear owner"

duplicateLinearOwnerRejects :: Either String ()
duplicateLinearOwnerRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      sameKey = ActivationOccurrenceKey "same-linear-owner"
      first = bindingFromKey sameKey "left-owner" Linear (TyOpaque "OwnedBuffer")
        (TargetParameterOrigin "worker-a.buffer") False
      second = bindingFromKey sameKey "right-owner" Linear (TyOpaque "OwnedBuffer")
        (TargetParameterOrigin "worker-b.buffer") False
  expectDuplicate processA (Name "left-owner") processB (Name "right-owner") sameKey $
    activateProcessContexts network
      [ ProcessActivationContract processA [first]
      , ProcessActivationContract processB [second]
      ]

duplicateEndpointRejects :: Either String ()
duplicateEndpointRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      sameKey = ActivationOccurrenceKey "endpoint-occurrence"
      endpointTy = TyEndpoint (End (Outcome "done"))
      first = bindingFromKey sameKey "endpoint-a" Linear endpointTy
        (ProtocolEndpointOrigin "protocol.p.left") False
      second = bindingFromKey sameKey "endpoint-b" Linear endpointTy
        (ProtocolEndpointOrigin "protocol.p.right") False
  expectDuplicate processA (Name "endpoint-a") processB (Name "endpoint-b") sameKey $
    activateProcessContexts network
      [ ProcessActivationContract processA [first]
      , ProcessActivationContract processB [second]
      ]

duplicateAffineCapabilityRejects :: Either String ()
duplicateAffineCapabilityRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      sameKey = ActivationOccurrenceKey "restricted-capability"
      first = bindingFromKey sameKey "cap-a" Affine (TyOpaque "WriteCapability")
        (ExplicitAuthorityOrigin "root.writer") False
      second = bindingFromKey sameKey "cap-b" Affine (TyOpaque "WriteCapability")
        (ExplicitAuthorityOrigin "root.writer") False
  expectDuplicate processA (Name "cap-a") processB (Name "cap-b") sameKey $
    activateProcessContexts network
      [ ProcessActivationContract processA [first]
      , ProcessActivationContract processB [second]
      ]

duplicateScopedLoanRejects :: Either String ()
duplicateScopedLoanRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      sameKey = ActivationOccurrenceKey "borrowed-owner"
      first = bindingFromKey sameKey "loan-owner-a" Linear (TyOpaque "BorrowedOwner")
        (InitializationTransitionOrigin "init.borrow-a") True
      second = bindingFromKey sameKey "loan-owner-b" Linear (TyOpaque "BorrowedOwner")
        (InitializationTransitionOrigin "init.borrow-b") True
  expectDuplicate processA (Name "loan-owner-a") processB (Name "loan-owner-b") sameKey $
    activateProcessContexts network
      [ ProcessActivationContract processA [first]
      , ProcessActivationContract processB [second]
      ]

ambientBindingRejects :: Either String ()
ambientBindingRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
      ambient = binding "ambient-handle" "host-handle" Unrestricted (TyOpaque "HostHandle")
        (AmbientActivationOrigin "current-host registry") False
  case activateProcessContexts network
    [ ProcessActivationContract processA [ambient]
    , ProcessActivationContract processB []
    ] of
    Left (AmbientActivationBinding actualProcess (Name "host-handle") detail) -> do
      assert (actualProcess == processA) "ambient-binding diagnostic named wrong process"
      assert (detail == "current-host registry") "ambient-binding diagnostic lost source detail"
    other -> Left ("ambient activation binding did not reject exactly: " <> show other)

missingActivationContractRejects :: Either String ()
missingActivationContractRejects = do
  network <- baseNetwork
  let (processA, processB) = processKeys network
  case activateProcessContexts network [ProcessActivationContract processA []] of
    Left (MissingActivationContract missing) ->
      assert (missing == processB) "missing activation diagnostic named wrong process"
    other -> Left ("missing process activation contract did not reject: " <> show other)

expectDuplicate
  :: Show a
  => ProcessKey
  -> Name
  -> ProcessKey
  -> Name
  -> ActivationOccurrenceKey
  -> Either ProcessActivationError a
  -> Either String ()
expectDuplicate expectedFirst firstName expectedSecond secondName expectedKey result =
  case result of
    Left (DuplicateRestrictedActivationOccurrence key firstProcess actualFirstName secondProcess actualSecondName) -> do
      assert (key == expectedKey) "duplicate restricted occurrence diagnostic named wrong occurrence"
      assert (firstProcess == expectedFirst && actualFirstName == firstName)
        "duplicate restricted occurrence diagnostic lost first owner"
      assert (secondProcess == expectedSecond && actualSecondName == secondName)
        "duplicate restricted occurrence diagnostic lost second owner"
    other -> Left ("duplicate restricted activation did not reject exactly: " <> show other)

binding
  :: Text
  -> Text
  -> Mode
  -> Ty
  -> ActivationBindingOrigin
  -> Bool
  -> ActivationBinding
binding occurrence name mode ty origin startsLoan =
  bindingFromKey (ActivationOccurrenceKey occurrence) name mode ty origin startsLoan

bindingFromKey
  :: ActivationOccurrenceKey
  -> Text
  -> Mode
  -> Ty
  -> ActivationBindingOrigin
  -> Bool
  -> ActivationBinding
bindingFromKey occurrence name mode ty origin startsLoan = ActivationBinding
  { activationOccurrenceKey = occurrence
  , activationLocalName = Name name
  , activationCheckedTypeMode = CheckedTypeMode ty mode
  , activationBindingOrigin = origin
  , activationStartsSharedLoan = startsLoan
  }

lookupContext
  :: ProcessKey
  -> Map.Map ProcessKey ResourceContext
  -> Either String ResourceContext
lookupContext processKey contexts =
  maybe (Left "missing activated process context") Right (Map.lookup processKey contexts)

baseNetwork :: Either String ProcessNetwork
baseNetwork = do
  graph <- mapLeft show rootGraph
  mapLeft show $ elaborateProcessNetwork graph [siteA, siteB]

processKeys :: ProcessNetwork -> (ProcessKey, ProcessKey)
processKeys network =
  let rootRevision = identityInstanceRevision (processNetworkRoot network)
  in ( deriveProcessKey rootRevision (processSiteKey siteA)
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
      [ ArchitectureChildSpec slotA workerSpec
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

siteA, siteB :: ProcessDeclarationSite
siteA = ProcessDeclarationSite (ProcessSiteKey "site-a") targetA
siteB = ProcessDeclarationSite (ProcessSiteKey "site-b") targetB

rootKey, targetA, targetB :: InstanceKey
rootKey = InstanceKey "root-instance"
targetA = scopedInstanceKey rootKey slotA
targetB = scopedInstanceKey rootKey slotB

slotA, slotB :: OccurrenceSlotKey
slotA = OccurrenceSlotKey "worker-a"
slotB = OccurrenceSlotKey "worker-b"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
