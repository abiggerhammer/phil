{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Static
  ( ClaimDefinition (..)
  , ClaimDecl (..)
  , StaticContext (..)
  , StaticError (..)
  , SemanticForm (..)
  , DeclarationKey (..)
  , InterfaceRevision (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , RealizationRevision (..)
  , DeclarationPresentation (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity (..)
  , ArchitectureRealizationDescriptor (..)
  , ArchitectureRealizationIdentity (..)
  , OccurrenceSlotKey (..)
  , RequirementKey (..)
  , ReferenceKey (..)
  , ArchitectureRequirementKind (..)
  , ArchitectureRequirementDisposition (..)
  , ArchitectureRequirement (..)
  , ArchitectureReferenceSpec (..)
  , ArchitectureChildSpec (..)
  , ArchitectureNodeSpec (..)
  , CheckedArchitectureInstance (..)
  , ArchitectureInstanceGraph (..)
  , ArchitectureInstantiationError (..)
  , canonicalSemanticForm
  , deriveDeclarationIdentity
  , deriveArchitectureInstanceIdentity
  , deriveArchitectureRealizationIdentity
  , scopedInstanceKey
  , instantiateArchitecture
  , lookupArchitectureInstance
  , lookupArchitectureReference
  , emptyStaticContext
  , declareTransparentClaim
  , declareOpaqueClaim
  , lookupClaim
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.SortCheck (SortError, validateRefSort)
import Phil.Core.Syntax
  ( Name
  , Proposition
  , RefSort
  )

data ClaimDefinition
  = TransparentClaim Proposition
  | OpaqueClaim
  deriving (Eq, Ord, Show)

data ClaimDecl = ClaimDecl
  { claimParameters :: [(Name, RefSort)]
  , claimDefinition :: ClaimDefinition
  }
  deriving (Eq, Ord, Show)

newtype StaticContext = StaticContext
  { staticClaims :: Map.Map Text ClaimDecl
  }
  deriving (Eq, Show)

data StaticError
  = DuplicateClaim Text
  | DuplicateClaimParameter Text Name
  | InvalidClaimParameterSort Text Name RefSort SortError
  deriving (Eq, Show)

-- | A target-independent canonical semantic value used when deriving exact
-- Phase 1 declaration, instance, and realization revisions.  The constructors
-- distinguish ordered data, set-like data, and named fields so that callers do
-- not have to rely on source text, source order, or container iteration order.
data SemanticForm
  = SemanticAtom Text
  | SemanticOrdered [SemanticForm]
  | SemanticUnordered (Set.Set SemanticForm)
  | SemanticRecord (Map.Map Text SemanticForm)
  deriving (Eq, Ord, Show)

newtype DeclarationKey = DeclarationKey { unDeclarationKey :: Text }
  deriving (Eq, Ord, Show)

newtype InterfaceRevision = InterfaceRevision { unInterfaceRevision :: Text }
  deriving (Eq, Ord, Show)

newtype DefinitionRevision = DefinitionRevision { unDefinitionRevision :: Text }
  deriving (Eq, Ord, Show)

newtype InstanceKey = InstanceKey { unInstanceKey :: Text }
  deriving (Eq, Ord, Show)

newtype InstanceRevision = InstanceRevision { unInstanceRevision :: Text }
  deriving (Eq, Ord, Show)

newtype RealizationRevision = RealizationRevision { unRealizationRevision :: Text }
  deriving (Eq, Ord, Show)

-- | Human-facing location data.  It is deliberately carried next to, rather
-- than inside, semantic identity inputs.  Renaming or moving a declaration can
-- therefore preserve identity when elaborated semantics and stable lineage are
-- unchanged.
data DeclarationPresentation = DeclarationPresentation
  { declarationDisplayName :: Text
  , declarationModulePath :: [Text]
  }
  deriving (Eq, Ord, Show)

-- | Minimal checked declaration descriptor for the first Phase 1 identity
-- slice.  The exact source syntax and full architecture graph vocabulary stay
-- deferred; the checked semantic forms are the identity-bearing inputs.
data DeclarationDescriptor = DeclarationDescriptor
  { declarationPresentation :: DeclarationPresentation
  , declarationKey :: DeclarationKey
  , declarationInterfaceSemantics :: SemanticForm
  , declarationDefinitionSemantics :: SemanticForm
  }
  deriving (Eq, Ord, Show)

data DeclarationIdentity = DeclarationIdentity
  { identityDeclarationKey :: DeclarationKey
  , identityInterfaceRevision :: InterfaceRevision
  , identityDefinitionRevision :: DefinitionRevision
  }
  deriving (Eq, Ord, Show)

-- | One exact architecture occurrence.  Parent occurrence identity is stable
-- lineage, not the complete parent revision, so an unrelated sibling edit does
-- not recursively rekey an unaffected child.  Broader evidence may still name
-- the containing architecture revision in its validity context.
data ArchitectureInstanceDescriptor = ArchitectureInstanceDescriptor
  { architectureInstanceKey :: InstanceKey
  , architectureParentInstanceKey :: Maybe InstanceKey
  , architectureDeclarationIdentity :: DeclarationIdentity
  , architectureStaticBindings :: Map.Map Text SemanticForm
  }
  deriving (Eq, Ord, Show)

data ArchitectureInstanceIdentity = ArchitectureInstanceIdentity
  { identityInstanceKey :: InstanceKey
  , identityInstanceRevision :: InstanceRevision
  }
  deriving (Eq, Ord, Show)

-- | Concrete realization choices are deliberately downstream of the abstract
-- architecture occurrence.  Replacing one qualified implementation may change
-- this identity without changing the ArchitectureInstance identity.
data ArchitectureRealizationDescriptor = ArchitectureRealizationDescriptor
  { realizationInstanceIdentity :: ArchitectureInstanceIdentity
  , realizationSemantics :: SemanticForm
  }
  deriving (Eq, Ord, Show)

newtype ArchitectureRealizationIdentity = ArchitectureRealizationIdentity
  { identityRealizationRevision :: RealizationRevision
  }
  deriving (Eq, Ord, Show)

-- Phase 1 architecture instantiation -----------------------------------------

-- | Stable declaration-level occurrence slot.  Display names are deliberately
-- absent: occurrence lineage is scoped from this key and the parent InstanceKey.
newtype OccurrenceSlotKey = OccurrenceSlotKey { unOccurrenceSlotKey :: Text }
  deriving (Eq, Ord, Show)

newtype RequirementKey = RequirementKey { unRequirementKey :: Text }
  deriving (Eq, Ord, Show)

newtype ReferenceKey = ReferenceKey { unReferenceKey :: Text }
  deriving (Eq, Ord, Show)

data ArchitectureRequirementKind
  = StaticArgumentRequirement
  | ProviderRequirement
  | CallableRequirement
  | CapabilityRequirement
  | ProtocolRequirement
  | BoundaryRequirement
  deriving (Eq, Ord, Show)

-- | Architecture-level disposition only.  Evidence artifacts and concrete
-- provider implementations remain assurance/realization metadata, not instance
-- semantic identity.  BoundTo names an already explicit semantic occurrence.
data ArchitectureRequirementDisposition
  = RequirementBoundTo InstanceKey
  | RequirementSatisfied SemanticForm
  | RequirementRuntimeBound Text
  | RequirementAssumed Text
  | RequirementReExported Text
  | RequirementDeploymentExported Text
  deriving (Eq, Ord, Show)

data ArchitectureRequirement = ArchitectureRequirement
  { architectureRequirementKey :: RequirementKey
  , architectureRequirementKind :: ArchitectureRequirementKind
  , architectureRequirementExpectedInterface :: Maybe InterfaceRevision
  , architectureRequirementDisposition :: Maybe ArchitectureRequirementDisposition
  }
  deriving (Eq, Ord, Show)

data ArchitectureReferenceSpec = ArchitectureReferenceSpec
  { architectureReferenceKey :: ReferenceKey
  , architectureReferenceTarget :: InstanceKey
  }
  deriving (Eq, Ord, Show)

-- | A new contained occurrence.  Repeating a child spec at another stable slot
-- creates another occurrence even when declaration and arguments are equal.
data ArchitectureChildSpec = ArchitectureChildSpec
  { architectureChildSlot :: OccurrenceSlotKey
  , architectureChildNode :: ArchitectureNodeSpec
  }
  deriving (Eq, Ord, Show)

-- | Target-abstract checked input to instance construction.  References share
-- existing instance keys explicitly; children create new scoped occurrences.
data ArchitectureNodeSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration :: DeclarationIdentity
  , architectureNodeStaticBindings :: Map.Map Text SemanticForm
  , architectureNodeRequirements :: [ArchitectureRequirement]
  , architectureNodeChildren :: [ArchitectureChildSpec]
  , architectureNodeReferences :: [ArchitectureReferenceSpec]
  }
  deriving (Eq, Ord, Show)

data CheckedArchitectureInstance = CheckedArchitectureInstance
  { checkedArchitectureIdentity :: ArchitectureInstanceIdentity
  , checkedArchitectureDescriptor :: ArchitectureInstanceDescriptor
  , checkedArchitectureRequirements :: Map.Map RequirementKey ArchitectureRequirement
  , checkedArchitectureChildren :: Map.Map OccurrenceSlotKey InstanceKey
  , checkedArchitectureReferences :: Map.Map ReferenceKey InstanceKey
  }
  deriving (Eq, Ord, Show)

data ArchitectureInstanceGraph = ArchitectureInstanceGraph
  { architectureGraphRoot :: ArchitectureInstanceIdentity
  , architectureGraphInstances :: Map.Map InstanceKey CheckedArchitectureInstance
  }
  deriving (Eq, Ord, Show)

data ArchitectureInstantiationError
  = DuplicateOccurrenceSlot InstanceKey OccurrenceSlotKey
  | DuplicateArchitectureRequirement InstanceKey RequirementKey
  | DuplicateArchitectureReference InstanceKey ReferenceKey
  | DuplicateArchitectureInstanceKey InstanceKey
  | UnresolvedArchitectureRequirement InstanceKey RequirementKey ArchitectureRequirementKind
  | UnknownArchitectureBindingTarget InstanceKey RequirementKey InstanceKey
  | ArchitectureBindingInterfaceMismatch
      InstanceKey RequirementKey InterfaceRevision InterfaceRevision
  | UnknownArchitectureReferenceTarget InstanceKey ReferenceKey InstanceKey
  deriving (Eq, Ord, Show)

canonicalSemanticForm :: SemanticForm -> Text
canonicalSemanticForm semantic = case semantic of
  SemanticAtom value -> "atom(" <> canonicalAtom value <> ")"
  SemanticOrdered values ->
    "ordered[" <> Text.intercalate "," (map canonicalSemanticForm values) <> "]"
  SemanticUnordered values ->
    "unordered["
      <> Text.intercalate "," (map canonicalSemanticForm (Set.toAscList values))
      <> "]"
  SemanticRecord fields ->
    "record{"
      <> Text.intercalate ","
          [ canonicalAtom field <> "=" <> canonicalSemanticForm value
          | (field, value) <- Map.toAscList fields
          ]
      <> "}"
  where
    canonicalAtom value = Text.pack (show (Text.length value)) <> ":" <> value

deriveDeclarationIdentity :: DeclarationDescriptor -> DeclarationIdentity
deriveDeclarationIdentity descriptor = DeclarationIdentity
  { identityDeclarationKey = declarationKey descriptor
  , identityInterfaceRevision = interfaceRevision
  , identityDefinitionRevision = definitionRevision
  }
  where
    interfaceRevision = InterfaceRevision
      ("phil.interface.canonical.v1:"
        <> canonicalSemanticForm (declarationInterfaceSemantics descriptor))
    definitionRevision = DefinitionRevision
      ("phil.definition.canonical.v1:"
        <> canonicalSemanticForm (SemanticRecord (Map.fromList
          [ ("interface_revision", SemanticAtom (unInterfaceRevision interfaceRevision))
          , ("definition", declarationDefinitionSemantics descriptor)
          ])))

deriveArchitectureInstanceIdentity
  :: ArchitectureInstanceDescriptor
  -> ArchitectureInstanceIdentity
deriveArchitectureInstanceIdentity descriptor = ArchitectureInstanceIdentity
  { identityInstanceKey = architectureInstanceKey descriptor
  , identityInstanceRevision = InstanceRevision
      ("phil.instance.canonical.v1:"
        <> canonicalSemanticForm (SemanticRecord (Map.fromList
          [ ("instance_key", SemanticAtom (unInstanceKey (architectureInstanceKey descriptor)))
          , ("parent_instance_key", maybe (SemanticAtom "")
              (SemanticAtom . unInstanceKey) (architectureParentInstanceKey descriptor))
          , ("declaration_key", SemanticAtom
              (unDeclarationKey (identityDeclarationKey declarationIdentity)))
          , ("interface_revision", SemanticAtom
              (unInterfaceRevision (identityInterfaceRevision declarationIdentity)))
          , ("definition_revision", SemanticAtom
              (unDefinitionRevision (identityDefinitionRevision declarationIdentity)))
          , ("bindings", SemanticRecord (architectureStaticBindings descriptor))
          ])))
  }
  where
    declarationIdentity = architectureDeclarationIdentity descriptor

deriveArchitectureRealizationIdentity
  :: ArchitectureRealizationDescriptor
  -> ArchitectureRealizationIdentity
deriveArchitectureRealizationIdentity descriptor = ArchitectureRealizationIdentity
  { identityRealizationRevision = RealizationRevision
      ("phil.realization.canonical.v1:"
        <> canonicalSemanticForm (SemanticRecord (Map.fromList
          [ ("instance_key", SemanticAtom
              (unInstanceKey (identityInstanceKey instanceIdentity)))
          , ("instance_revision", SemanticAtom
              (unInstanceRevision (identityInstanceRevision instanceIdentity)))
          , ("realization", realizationSemantics descriptor)
          ])))
  }
  where
    instanceIdentity = realizationInstanceIdentity descriptor

-- | Deterministically scope one stable occurrence slot under one exact parent
-- occurrence lineage.  The spelling is intentionally inspectable in Phase 1;
-- a future compact digest encoding must preserve this equality relation.
scopedInstanceKey :: InstanceKey -> OccurrenceSlotKey -> InstanceKey
scopedInstanceKey parent slot = InstanceKey
  ("phil.instance.scope.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("parent", SemanticAtom (unInstanceKey parent))
      , ("slot", SemanticAtom (unOccurrenceSlotKey slot))
      ])))

instantiateArchitecture
  :: InstanceKey
  -> ArchitectureNodeSpec
  -> Either ArchitectureInstantiationError ArchitectureInstanceGraph
instantiateArchitecture rootKey rootSpec = do
  (rootNode, nodes) <- buildArchitectureNode rootKey Nothing rootSpec
  let graph = ArchitectureInstanceGraph
        { architectureGraphRoot = checkedArchitectureIdentity rootNode
        , architectureGraphInstances = nodes
        }
  validateArchitectureGraph graph
  Right graph

lookupArchitectureInstance
  :: InstanceKey
  -> ArchitectureInstanceGraph
  -> Maybe CheckedArchitectureInstance
lookupArchitectureInstance key = Map.lookup key . architectureGraphInstances

lookupArchitectureReference
  :: InstanceKey
  -> ReferenceKey
  -> ArchitectureInstanceGraph
  -> Maybe InstanceKey
lookupArchitectureReference owner referenceKey graph = do
  ownerNode <- lookupArchitectureInstance owner graph
  Map.lookup referenceKey (checkedArchitectureReferences ownerNode)

buildArchitectureNode
  :: InstanceKey
  -> Maybe InstanceKey
  -> ArchitectureNodeSpec
  -> Either ArchitectureInstantiationError
      (CheckedArchitectureInstance, Map.Map InstanceKey CheckedArchitectureInstance)
buildArchitectureNode instanceKey parentKey spec = do
  requirementMap <- normalizeRequirements instanceKey (architectureNodeRequirements spec)
  referenceMap <- normalizeReferences instanceKey (architectureNodeReferences spec)
  childSpecs <- normalizeChildren instanceKey (architectureNodeChildren spec)
  (childIdentities, descendantNodes) <- buildChildren instanceKey childSpecs
  let requirementBindings = SemanticRecord (Map.fromList
        [ (unRequirementKey key, requirementSemantic requirement)
        | (key, requirement) <- Map.toAscList requirementMap
        ])
      childBindings = SemanticRecord (Map.fromList
        [ (unOccurrenceSlotKey slot, childSemantic childIdentity)
        | (slot, childIdentity) <- Map.toAscList childIdentities
        ])
      referenceBindings = SemanticRecord (Map.fromList
        [ (unReferenceKey key, SemanticAtom (unInstanceKey target))
        | (key, target) <- Map.toAscList referenceMap
        ])
      semanticBindings = Map.fromList
        [ ("requirements", requirementBindings)
        , ("children", childBindings)
        , ("references", referenceBindings)
        ]
      descriptor = ArchitectureInstanceDescriptor
        { architectureInstanceKey = instanceKey
        , architectureParentInstanceKey = parentKey
        , architectureDeclarationIdentity = architectureNodeDeclaration spec
        , architectureStaticBindings = architectureNodeStaticBindings spec
        }
      identity = deriveGraphInstanceIdentity descriptor semanticBindings
      node = CheckedArchitectureInstance
        { checkedArchitectureIdentity = identity
        , checkedArchitectureDescriptor = descriptor
        , checkedArchitectureRequirements = requirementMap
        , checkedArchitectureChildren = Map.map identityInstanceKey childIdentities
        , checkedArchitectureReferences = referenceMap
        }
  if Map.member instanceKey descendantNodes
    then Left (DuplicateArchitectureInstanceKey instanceKey)
    else Right (node, Map.insert instanceKey node descendantNodes)
  where
    childSemantic childIdentity = SemanticRecord (Map.fromList
      [ ("key", SemanticAtom (unInstanceKey (identityInstanceKey childIdentity)))
      , ("revision", SemanticAtom (unInstanceRevision (identityInstanceRevision childIdentity)))
      ])

deriveGraphInstanceIdentity
  :: ArchitectureInstanceDescriptor
  -> Map.Map Text SemanticForm
  -> ArchitectureInstanceIdentity
deriveGraphInstanceIdentity descriptor semanticBindings = ArchitectureInstanceIdentity
  { identityInstanceKey = identityInstanceKey baseIdentity
  , identityInstanceRevision = InstanceRevision
      ("phil.instance.graph.canonical.v1:"
        <> canonicalSemanticForm (SemanticRecord (Map.fromList
          [ ("base_revision", SemanticAtom
              (unInstanceRevision (identityInstanceRevision baseIdentity)))
          , ("semantic_bindings", SemanticRecord semanticBindings)
          ])))
  }
  where
    baseIdentity = deriveArchitectureInstanceIdentity descriptor

buildChildren
  :: InstanceKey
  -> Map.Map OccurrenceSlotKey ArchitectureNodeSpec
  -> Either ArchitectureInstantiationError
      (Map.Map OccurrenceSlotKey ArchitectureInstanceIdentity,
       Map.Map InstanceKey CheckedArchitectureInstance)
buildChildren parentKey = Map.foldlWithKey' step (Right (Map.empty, Map.empty))
  where
    step accumulated slot childSpec = do
      (identities, nodes) <- accumulated
      let childKey = scopedInstanceKey parentKey slot
      (childNode, childNodes) <- buildArchitectureNode childKey (Just parentKey) childSpec
      mergedNodes <- mergeNodeMaps nodes childNodes
      Right
        ( Map.insert slot (checkedArchitectureIdentity childNode) identities
        , mergedNodes
        )

mergeNodeMaps
  :: Map.Map InstanceKey CheckedArchitectureInstance
  -> Map.Map InstanceKey CheckedArchitectureInstance
  -> Either ArchitectureInstantiationError (Map.Map InstanceKey CheckedArchitectureInstance)
mergeNodeMaps left right =
  case Set.lookupMin (Map.keysSet left `Set.intersection` Map.keysSet right) of
    Just duplicate -> Left (DuplicateArchitectureInstanceKey duplicate)
    Nothing -> Right (Map.union left right)

normalizeRequirements
  :: InstanceKey
  -> [ArchitectureRequirement]
  -> Either ArchitectureInstantiationError (Map.Map RequirementKey ArchitectureRequirement)
normalizeRequirements owner = foldl step (Right Map.empty)
  where
    step accumulated requirement = do
      requirements <- accumulated
      let key = architectureRequirementKey requirement
      if Map.member key requirements
        then Left (DuplicateArchitectureRequirement owner key)
        else Right (Map.insert key requirement requirements)

normalizeReferences
  :: InstanceKey
  -> [ArchitectureReferenceSpec]
  -> Either ArchitectureInstantiationError (Map.Map ReferenceKey InstanceKey)
normalizeReferences owner = foldl step (Right Map.empty)
  where
    step accumulated reference = do
      references <- accumulated
      let key = architectureReferenceKey reference
      if Map.member key references
        then Left (DuplicateArchitectureReference owner key)
        else Right (Map.insert key (architectureReferenceTarget reference) references)

normalizeChildren
  :: InstanceKey
  -> [ArchitectureChildSpec]
  -> Either ArchitectureInstantiationError (Map.Map OccurrenceSlotKey ArchitectureNodeSpec)
normalizeChildren owner = foldl step (Right Map.empty)
  where
    step accumulated child = do
      children <- accumulated
      let slot = architectureChildSlot child
      if Map.member slot children
        then Left (DuplicateOccurrenceSlot owner slot)
        else Right (Map.insert slot (architectureChildNode child) children)

requirementSemantic :: ArchitectureRequirement -> SemanticForm
requirementSemantic requirement = SemanticRecord (Map.fromList
  [ ("kind", SemanticAtom (Text.pack (show (architectureRequirementKind requirement))))
  , ("expected_interface", maybe (SemanticAtom "")
      (SemanticAtom . unInterfaceRevision)
      (architectureRequirementExpectedInterface requirement))
  , ("disposition", maybe (SemanticAtom "unresolved") dispositionSemantic
      (architectureRequirementDisposition requirement))
  ])

dispositionSemantic :: ArchitectureRequirementDisposition -> SemanticForm
dispositionSemantic disposition = case disposition of
  RequirementBoundTo target -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "bound")
    , ("target", SemanticAtom (unInstanceKey target))
    ])
  RequirementSatisfied evidence -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "satisfied")
    , ("fact", evidence)
    ])
  RequirementRuntimeBound boundary -> boundaryDisposition "runtime" boundary
  RequirementAssumed boundary -> boundaryDisposition "assumed" boundary
  RequirementReExported boundary -> boundaryDisposition "re-exported" boundary
  RequirementDeploymentExported boundary -> boundaryDisposition "deployment-exported" boundary
  where
    boundaryDisposition kind boundary = SemanticRecord (Map.fromList
      [ ("kind", SemanticAtom kind)
      , ("boundary", SemanticAtom boundary)
      ])

validateArchitectureGraph
  :: ArchitectureInstanceGraph
  -> Either ArchitectureInstantiationError ()
validateArchitectureGraph graph =
  mapM_ validateNode (Map.elems (architectureGraphInstances graph))
  where
    validateNode node = do
      validateRequirements node
      validateReferences node

    validateRequirements node =
      mapM_ (validateRequirement node) (Map.elems (checkedArchitectureRequirements node))

    validateRequirement node requirement =
      case architectureRequirementDisposition requirement of
        Nothing -> Left (UnresolvedArchitectureRequirement
          ownerKey
          (architectureRequirementKey requirement)
          (architectureRequirementKind requirement))
        Just disposition -> case disposition of
          RequirementBoundTo target -> do
            targetNode <- maybe
              (Left (UnknownArchitectureBindingTarget
                ownerKey (architectureRequirementKey requirement) target))
              Right
              (lookupArchitectureInstance target graph)
            case architectureRequirementExpectedInterface requirement of
              Nothing -> Right ()
              Just expected ->
                let actual = identityInterfaceRevision
                      (architectureDeclarationIdentity
                        (checkedArchitectureDescriptor targetNode))
                in if actual == expected
                    then Right ()
                    else Left (ArchitectureBindingInterfaceMismatch
                      ownerKey (architectureRequirementKey requirement) expected actual)
          _ -> Right ()
      where
        ownerKey = identityInstanceKey (checkedArchitectureIdentity node)

    validateReferences node = mapM_ validateReference
      (Map.toList (checkedArchitectureReferences node))
      where
        ownerKey = identityInstanceKey (checkedArchitectureIdentity node)
        validateReference (referenceKey, target) =
          case lookupArchitectureInstance target graph of
            Just _ -> Right ()
            Nothing -> Left (UnknownArchitectureReferenceTarget
              ownerKey referenceKey target)

emptyStaticContext :: StaticContext
emptyStaticContext = StaticContext Map.empty

declareTransparentClaim
  :: Text
  -> [(Name, RefSort)]
  -> Proposition
  -> StaticContext
  -> Either StaticError StaticContext
declareTransparentClaim name parameters body =
  declareClaim name parameters (TransparentClaim body)

declareOpaqueClaim
  :: Text
  -> [(Name, RefSort)]
  -> StaticContext
  -> Either StaticError StaticContext
declareOpaqueClaim name parameters =
  declareClaim name parameters OpaqueClaim

lookupClaim :: Text -> StaticContext -> Maybe ClaimDecl
lookupClaim name = Map.lookup name . staticClaims

declareClaim
  :: Text
  -> [(Name, RefSort)]
  -> ClaimDefinition
  -> StaticContext
  -> Either StaticError StaticContext
declareClaim name parameters definition context
  | Map.member name (staticClaims context) = Left (DuplicateClaim name)
  | otherwise = do
      ensureUniqueParameters Set.empty parameters
      mapM_ validateParameter parameters
      Right context
        { staticClaims = Map.insert name (ClaimDecl parameters definition) (staticClaims context)
        }
  where
    ensureUniqueParameters _ [] = Right ()
    ensureUniqueParameters seen ((parameter, _) : rest)
      | Set.member parameter seen = Left (DuplicateClaimParameter name parameter)
      | otherwise = ensureUniqueParameters (Set.insert parameter seen) rest

    validateParameter (parameter, sort) =
      case validateRefSort sort of
        Right () -> Right ()
        Left err -> Left (InvalidClaimParameterSort name parameter sort err)
