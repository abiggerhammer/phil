module SurfaceGrammarAstTopLevelCarrierKernel where

import qualified Prelude

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

data String =
   EmptyString
 | String0 Ascii0 String

data Phase1SurfaceDeclarationTag =
   Phase1RecordDeclaration
 | Phase1DataDeclaration
 | Phase1TypeAliasDeclaration
 | Phase1ClaimDeclaration
 | Phase1CallableContractDeclaration
 | Phase1FunctionDeclaration
 | Phase1ProviderContractDeclaration
 | Phase1ProviderImplementationDeclaration
 | Phase1OpaqueProviderImplementationDeclaration
 | Phase1ProtocolDeclaration
 | Phase1CapabilityDeclaration
 | Phase1BoundaryDeclaration
 | Phase1ArchitectureDeclaration
 | Phase1ComponentDeclaration
 | Phase1ProgramDeclaration

data Phase1SurfaceImplementationAttribute =
   Build_Phase1SurfaceImplementationAttribute String String

data Phase1SurfaceImplementationTopLevel =
   Build_Phase1SurfaceImplementationTopLevel ([]
                                             Phase1SurfaceImplementationAttribute) 
 Phase1SurfaceDeclarationTag

phase1_surface_make_implementation_attribute :: String -> String ->
                                                 Phase1SurfaceImplementationAttribute
phase1_surface_make_implementation_attribute name value =
  Build_Phase1SurfaceImplementationAttribute name value

phase1_surface_make_implementation_top_level :: ([]
                                                Phase1SurfaceImplementationAttribute)
                                                -> Phase1SurfaceDeclarationTag ->
                                                Phase1SurfaceImplementationTopLevel
phase1_surface_make_implementation_top_level attributes tag =
  Build_Phase1SurfaceImplementationTopLevel attributes tag
