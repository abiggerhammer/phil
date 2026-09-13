module SurfaceGrammarAstRecordDataCarrierKernel where

import qualified Prelude

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool
 Prelude.Bool Prelude.Bool Prelude.Bool

data String =
   EmptyString
 | String0 Ascii0 String

data Phase1SurfaceProductionGenericKind =
   Phase1ProductionTypeGenericKind
 | Phase1ProductionNatGenericKind
 | Phase1ProductionSessionGenericKind
 | Phase1ProductionMessageGenericKind
 | Phase1ProductionEffectsGenericKind
 | Phase1ProductionProviderGenericKind
 | Phase1ProductionCallableGenericKind
 | Phase1ProductionBoundaryGenericKind
 | Phase1ProductionArchitectureGenericKind

data Phase1SurfaceProductionStructuralMode =
   Phase1ProductionUnrestrictedMode
 | Phase1ProductionAffineMode
 | Phase1ProductionLinearMode

data Phase1SurfaceProductionRequirement =
   Phase1ProductionStructuralRequirement
 | Phase1ProductionPropositionRequirement
 | Phase1ProductionProviderRequirement
 | Phase1ProductionCallableRequirement
 | Phase1ProductionBoundaryRequirement
 | Phase1ProductionArchitectureRequirement
 | Phase1ProductionEffectsRequirement
 | Phase1ProductionAuthorityRequirement
 | Phase1ProductionBoundaryRepresentationRequirement
 | Phase1ProductionRepresentationRequirement
 | Phase1ProductionPlacementRequirement
 | Phase1ProductionCostRequirement
 | Phase1ProductionEnvironmentRequirement

data Phase1SurfaceProductionGenericParam =
   Build_Phase1SurfaceProductionGenericParam String
                                            Phase1SurfaceProductionGenericKind

data Phase1SurfaceProductionVariantPayload =
   Phase1ProductionRecordPayload ([] String)
 | Phase1ProductionTuplePayload ([] ())

data Phase1SurfaceProductionVariant =
   Build_Phase1SurfaceProductionVariant String
                                        (Prelude.Maybe Phase1SurfaceProductionVariantPayload)

data Phase1SurfaceProductionRecordDataDeclaration =
   Phase1ProductionRecordDeclaration String
                                     ([] Phase1SurfaceProductionGenericParam)
                                     (Prelude.Maybe Phase1SurfaceProductionStructuralMode)
                                     ([] Phase1SurfaceProductionRequirement)
                                     ([] String)
 | Phase1ProductionDataDeclaration String
                                   ([] Phase1SurfaceProductionGenericParam)
                                   (Prelude.Maybe Phase1SurfaceProductionStructuralMode)
                                   ([] Phase1SurfaceProductionRequirement)
                                   ([] Phase1SurfaceProductionVariant)

phase1_surface_make_production_generic_param :: String ->
                                                Phase1SurfaceProductionGenericKind ->
                                                Phase1SurfaceProductionGenericParam
phase1_surface_make_production_generic_param name kind =
  Build_Phase1SurfaceProductionGenericParam name kind

phase1_surface_make_production_record_payload :: ([] String) ->
                                                 Phase1SurfaceProductionVariantPayload
phase1_surface_make_production_record_payload fields =
  Phase1ProductionRecordPayload fields

phase1_surface_make_production_tuple_payload :: ([] ()) ->
                                                Phase1SurfaceProductionVariantPayload
phase1_surface_make_production_tuple_payload types =
  Phase1ProductionTuplePayload types

phase1_surface_make_production_variant :: String ->
                                          (Prelude.Maybe Phase1SurfaceProductionVariantPayload)
                                          -> Phase1SurfaceProductionVariant
phase1_surface_make_production_variant name payload =
  Build_Phase1SurfaceProductionVariant name payload

phase1_surface_make_production_record :: String ->
                                         ([] Phase1SurfaceProductionGenericParam)
                                         ->
                                         (Prelude.Maybe Phase1SurfaceProductionStructuralMode)
                                         ->
                                         ([] Phase1SurfaceProductionRequirement)
                                         -> ([] String) ->
                                         Phase1SurfaceProductionRecordDataDeclaration
phase1_surface_make_production_record name generic_params mode requirements fields =
  Phase1ProductionRecordDeclaration name generic_params mode requirements fields

phase1_surface_make_production_data :: String ->
                                       ([] Phase1SurfaceProductionGenericParam)
                                       ->
                                       (Prelude.Maybe Phase1SurfaceProductionStructuralMode)
                                       ->
                                       ([] Phase1SurfaceProductionRequirement)
                                       ->
                                       ([] Phase1SurfaceProductionVariant) ->
                                       Phase1SurfaceProductionRecordDataDeclaration
phase1_surface_make_production_data name generic_params mode requirements variants =
  Phase1ProductionDataDeclaration name generic_params mode requirements variants
