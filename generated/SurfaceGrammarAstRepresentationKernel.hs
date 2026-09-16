module SurfaceGrammarAstRepresentationKernel where

import qualified Prelude

data Nat =
   O
 | S Nat

length :: ([] a1) -> Nat
length l =
  case l of {
   [] -> O;
   (:) _ l' -> S (length l')}

eqb :: Nat -> Nat -> Prelude.Bool
eqb n m =
  case n of {
   O -> case m of {
         O -> Prelude.True;
         S _ -> Prelude.False};
   S n' -> case m of {
            O -> Prelude.False;
            S m' -> eqb n' m'}}

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a l0 -> (:) (f a) (map f l0)}

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

data String =
   EmptyString
 | String0 Ascii0 String

data ParseTree =
   PTLiteral String
 | PTLexical String String
 | PTNonterminal String ParseTree
 | PTSequence ([] ParseTree)
 | PTAlternative Nat ParseTree
 | PTOptionalNone
 | PTOptionalSome ParseTree
 | PTRepetition ([] ParseTree)

data Phase1SurfaceNameList =
   Build_Phase1SurfaceNameList String ([] String)

phase1_name_list_first :: Phase1SurfaceNameList -> String
phase1_name_list_first p =
  case p of {
   Build_Phase1SurfaceNameList phase1_name_list_first0 _ ->
    phase1_name_list_first0}

phase1_name_list_rest :: Phase1SurfaceNameList -> [] String
phase1_name_list_rest p =
  case p of {
   Build_Phase1SurfaceNameList _ phase1_name_list_rest0 ->
    phase1_name_list_rest0}

data Phase1SurfaceImportHeader =
   Build_Phase1SurfaceImportHeader Phase1SurfaceNameList (Prelude.Maybe
                                                         Phase1SurfaceNameList)

phase1_import_header_name :: Phase1SurfaceImportHeader ->
                             Phase1SurfaceNameList
phase1_import_header_name p =
  case p of {
   Build_Phase1SurfaceImportHeader phase1_import_header_name0 _ ->
    phase1_import_header_name0}

phase1_import_header_selection :: Phase1SurfaceImportHeader -> Prelude.Maybe
                                  Phase1SurfaceNameList
phase1_import_header_selection p =
  case p of {
   Build_Phase1SurfaceImportHeader _ phase1_import_header_selection0 ->
    phase1_import_header_selection0}

data Phase1SurfaceSourceHeader =
   Build_Phase1SurfaceSourceHeader (Prelude.Maybe Phase1SurfaceNameList) 
 ([] Phase1SurfaceImportHeader) ([] ParseTree)

phase1_source_header_module :: Phase1SurfaceSourceHeader -> Prelude.Maybe
                               Phase1SurfaceNameList
phase1_source_header_module p =
  case p of {
   Build_Phase1SurfaceSourceHeader phase1_source_header_module0 _ _ ->
    phase1_source_header_module0}

phase1_source_header_imports :: Phase1SurfaceSourceHeader -> []
                                Phase1SurfaceImportHeader
phase1_source_header_imports p =
  case p of {
   Build_Phase1SurfaceSourceHeader _ phase1_source_header_imports0 _ ->
    phase1_source_header_imports0}

phase1_source_header_top_levels :: Phase1SurfaceSourceHeader -> [] ParseTree
phase1_source_header_top_levels p =
  case p of {
   Build_Phase1SurfaceSourceHeader _ _ phase1_source_header_top_levels0 ->
    phase1_source_header_top_levels0}

data Phase1SurfaceImplementationImportHeader =
   Build_Phase1SurfaceImplementationImportHeader ([] String) (Prelude.Maybe
                                                             ([] String))

phase1_impl_import_name :: Phase1SurfaceImplementationImportHeader -> []
                           String
phase1_impl_import_name p =
  case p of {
   Build_Phase1SurfaceImplementationImportHeader phase1_impl_import_name0
    _ -> phase1_impl_import_name0}

phase1_impl_import_selection :: Phase1SurfaceImplementationImportHeader ->
                                Prelude.Maybe ([] String)
phase1_impl_import_selection p =
  case p of {
   Build_Phase1SurfaceImplementationImportHeader _
    phase1_impl_import_selection0 -> phase1_impl_import_selection0}

data Phase1SurfaceImplementationSourceHeader =
   Build_Phase1SurfaceImplementationSourceHeader (Prelude.Maybe ([] String)) 
 ([] Phase1SurfaceImplementationImportHeader) Nat

phase1_impl_source_module :: Phase1SurfaceImplementationSourceHeader ->
                             Prelude.Maybe ([] String)
phase1_impl_source_module p =
  case p of {
   Build_Phase1SurfaceImplementationSourceHeader phase1_impl_source_module0 _
    _ -> phase1_impl_source_module0}

phase1_impl_source_imports :: Phase1SurfaceImplementationSourceHeader -> []
                              Phase1SurfaceImplementationImportHeader
phase1_impl_source_imports p =
  case p of {
   Build_Phase1SurfaceImplementationSourceHeader _
    phase1_impl_source_imports0 _ -> phase1_impl_source_imports0}

phase1_impl_source_top_level_count :: Phase1SurfaceImplementationSourceHeader
                                      -> Nat
phase1_impl_source_top_level_count p =
  case p of {
   Build_Phase1SurfaceImplementationSourceHeader _ _
    phase1_impl_source_top_level_count0 ->
    phase1_impl_source_top_level_count0}

phase1_surface_name_list_to_implementation :: Phase1SurfaceNameList -> []
                                              String
phase1_surface_name_list_to_implementation names =
  (:) (phase1_name_list_first names) (phase1_name_list_rest names)

phase1_surface_name_list_from_implementation :: ([] String) -> Prelude.Maybe
                                                Phase1SurfaceNameList
phase1_surface_name_list_from_implementation values =
  case values of {
   [] -> Prelude.Nothing;
   (:) first rest -> Prelude.Just (Build_Phase1SurfaceNameList first rest)}

phase1_surface_optional_name_list_to_implementation :: (Prelude.Maybe
                                                       Phase1SurfaceNameList)
                                                       -> Prelude.Maybe
                                                       ([] String)
phase1_surface_optional_name_list_to_implementation names =
  case names of {
   Prelude.Just value -> Prelude.Just
    (phase1_surface_name_list_to_implementation value);
   Prelude.Nothing -> Prelude.Nothing}

phase1_surface_optional_name_list_from_implementation :: (Prelude.Maybe
                                                         ([] String)) ->
                                                         Prelude.Maybe
                                                         (Prelude.Maybe
                                                         Phase1SurfaceNameList)
phase1_surface_optional_name_list_from_implementation values =
  case values of {
   Prelude.Just names ->
    case phase1_surface_name_list_from_implementation names of {
     Prelude.Just value -> Prelude.Just (Prelude.Just value);
     Prelude.Nothing -> Prelude.Nothing};
   Prelude.Nothing -> Prelude.Just Prelude.Nothing}

phase1_surface_import_header_to_implementation :: Phase1SurfaceImportHeader
                                                  ->
                                                  Phase1SurfaceImplementationImportHeader
phase1_surface_import_header_to_implementation header =
  Build_Phase1SurfaceImplementationImportHeader
    (phase1_surface_name_list_to_implementation
      (phase1_import_header_name header))
    (phase1_surface_optional_name_list_to_implementation
      (phase1_import_header_selection header))

phase1_surface_import_header_from_implementation :: Phase1SurfaceImplementationImportHeader
                                                    -> Prelude.Maybe
                                                    Phase1SurfaceImportHeader
phase1_surface_import_header_from_implementation header =
  case phase1_surface_name_list_from_implementation
         (phase1_impl_import_name header) of {
   Prelude.Just name ->
    case phase1_surface_optional_name_list_from_implementation
           (phase1_impl_import_selection header) of {
     Prelude.Just selection -> Prelude.Just (Build_Phase1SurfaceImportHeader
      name selection);
     Prelude.Nothing -> Prelude.Nothing};
   Prelude.Nothing -> Prelude.Nothing}

phase1_surface_import_headers_from_implementation :: ([]
                                                     Phase1SurfaceImplementationImportHeader)
                                                     -> Prelude.Maybe
                                                     ([]
                                                     Phase1SurfaceImportHeader)
phase1_surface_import_headers_from_implementation headers =
  case headers of {
   [] -> Prelude.Just [];
   (:) header rest ->
    case phase1_surface_import_header_from_implementation header of {
     Prelude.Just value ->
      case phase1_surface_import_headers_from_implementation rest of {
       Prelude.Just values -> Prelude.Just ((:) value values);
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

phase1_surface_source_header_to_implementation :: Phase1SurfaceSourceHeader
                                                  ->
                                                  Phase1SurfaceImplementationSourceHeader
phase1_surface_source_header_to_implementation header =
  Build_Phase1SurfaceImplementationSourceHeader
    (phase1_surface_optional_name_list_to_implementation
      (phase1_source_header_module header))
    (map phase1_surface_import_header_to_implementation
      (phase1_source_header_imports header))
    (length (phase1_source_header_top_levels header))

phase1_surface_source_header_from_implementation :: Phase1SurfaceImplementationSourceHeader
                                                    -> ([] ParseTree) ->
                                                    Prelude.Maybe
                                                    Phase1SurfaceSourceHeader
phase1_surface_source_header_from_implementation header top_levels =
  case eqb (length top_levels) (phase1_impl_source_top_level_count header) of {
   Prelude.True ->
    case phase1_surface_optional_name_list_from_implementation
           (phase1_impl_source_module header) of {
     Prelude.Just module_name ->
      case phase1_surface_import_headers_from_implementation
             (phase1_impl_source_imports header) of {
       Prelude.Just imports -> Prelude.Just (Build_Phase1SurfaceSourceHeader
        module_name imports top_levels);
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Prelude.False -> Prelude.Nothing}
