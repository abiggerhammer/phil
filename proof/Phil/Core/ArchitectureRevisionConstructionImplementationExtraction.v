From Corelib Require Extraction.
From Phil.Core Require Import ArchitectureRevisionConstructionImplementation.

Extraction Language Haskell.

Extraction "ArchitectureRevisionConstructionKernel"
  ArchitectureRevisionNamespace
  planInterfaceRevision
  planDefinitionRevision
  planScopedInstanceKey
  planInstanceRevision.
