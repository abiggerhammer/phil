module ArchitectureRevisionConstructionKernel where

import qualified Prelude

data ArchitectureRevisionNamespace =
   InterfaceRevisionNamespace
 | DefinitionRevisionNamespace
 | ScopedInstanceKeyNamespace
 | InstanceRevisionNamespace

data InterfaceRevisionPlan semantic =
   MkInterfaceRevisionPlan ArchitectureRevisionNamespace semantic

planInterfaceRevision :: a1 -> InterfaceRevisionPlan a1
planInterfaceRevision interfaceSemantics =
  MkInterfaceRevisionPlan InterfaceRevisionNamespace interfaceSemantics

data DefinitionRevisionPlan interface body =
   MkDefinitionRevisionPlan ArchitectureRevisionNamespace interface body

planDefinitionRevision :: a1 -> a2 -> DefinitionRevisionPlan a1 a2
planDefinitionRevision interfaceRevision definitionSemantics =
  MkDefinitionRevisionPlan DefinitionRevisionNamespace interfaceRevision
    definitionSemantics

data ScopedInstanceKeyPlan parent slot =
   MkScopedInstanceKeyPlan ArchitectureRevisionNamespace parent slot

planScopedInstanceKey :: a1 -> a2 -> ScopedInstanceKeyPlan a1 a2
planScopedInstanceKey parent slot =
  MkScopedInstanceKeyPlan ScopedInstanceKeyNamespace parent slot

data InstanceRevisionPlan key parent declarationKeyValue interface definitionValue bindings =
   MkInstanceRevisionPlan ArchitectureRevisionNamespace key parent declarationKeyValue 
 interface definitionValue bindings

planInstanceRevision :: a1 -> a2 -> a3 -> a4 -> a5 -> a6 ->
                        InstanceRevisionPlan a1 a2 a3 a4 a5 a6
planInstanceRevision instanceKey parent declarationKeyValue interfaceRevision definitionRevision bindings =
  MkInstanceRevisionPlan InstanceRevisionNamespace instanceKey parent
    declarationKeyValue interfaceRevision definitionRevision bindings
