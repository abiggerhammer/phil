module ArchitectureIdentityKernel where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

data DeclarationIdentityEqualityFacts =
   MkDeclarationIdentityEqualityFacts Prelude.Bool Prelude.Bool Prelude.Bool

declarationIdentityKeyMatches :: DeclarationIdentityEqualityFacts ->
                                 Prelude.Bool
declarationIdentityKeyMatches d =
  case d of {
   MkDeclarationIdentityEqualityFacts declarationIdentityKeyMatches0 _ _ ->
    declarationIdentityKeyMatches0}

declarationIdentityInterfaceMatches :: DeclarationIdentityEqualityFacts ->
                                       Prelude.Bool
declarationIdentityInterfaceMatches d =
  case d of {
   MkDeclarationIdentityEqualityFacts _ declarationIdentityInterfaceMatches0
    _ -> declarationIdentityInterfaceMatches0}

declarationIdentityDefinitionMatches :: DeclarationIdentityEqualityFacts ->
                                        Prelude.Bool
declarationIdentityDefinitionMatches d =
  case d of {
   MkDeclarationIdentityEqualityFacts _ _
    declarationIdentityDefinitionMatches0 ->
    declarationIdentityDefinitionMatches0}

declarationIdentityFactsb :: DeclarationIdentityEqualityFacts -> Prelude.Bool
declarationIdentityFactsb facts =
  andb (declarationIdentityKeyMatches facts)
    (andb (declarationIdentityInterfaceMatches facts)
      (declarationIdentityDefinitionMatches facts))

data DeclarationIdentityEqualityDecision =
   DeclarationIdentityEqual
 | DeclarationIdentityDifferent

decideDeclarationIdentityEquality :: DeclarationIdentityEqualityFacts ->
                                     DeclarationIdentityEqualityDecision
decideDeclarationIdentityEquality facts =
  case declarationIdentityFactsb facts of {
   Prelude.True -> DeclarationIdentityEqual;
   Prelude.False -> DeclarationIdentityDifferent}

data InterfaceValidityScopeEqualityFacts =
   MkInterfaceValidityScopeEqualityFacts Prelude.Bool Prelude.Bool

interfaceValidityKeyMatches :: InterfaceValidityScopeEqualityFacts ->
                               Prelude.Bool
interfaceValidityKeyMatches i =
  case i of {
   MkInterfaceValidityScopeEqualityFacts interfaceValidityKeyMatches0 _ ->
    interfaceValidityKeyMatches0}

interfaceValidityRevisionMatches :: InterfaceValidityScopeEqualityFacts ->
                                    Prelude.Bool
interfaceValidityRevisionMatches i =
  case i of {
   MkInterfaceValidityScopeEqualityFacts _
    interfaceValidityRevisionMatches0 -> interfaceValidityRevisionMatches0}

interfaceValidityScopeFactsb :: InterfaceValidityScopeEqualityFacts ->
                                Prelude.Bool
interfaceValidityScopeFactsb facts =
  andb (interfaceValidityKeyMatches facts)
    (interfaceValidityRevisionMatches facts)

data InterfaceValidityScopeEqualityDecision =
   InterfaceValidityScopeEqual
 | InterfaceValidityScopeDifferent

decideInterfaceValidityScopeEquality :: InterfaceValidityScopeEqualityFacts
                                        ->
                                        InterfaceValidityScopeEqualityDecision
decideInterfaceValidityScopeEquality facts =
  case interfaceValidityScopeFactsb facts of {
   Prelude.True -> InterfaceValidityScopeEqual;
   Prelude.False -> InterfaceValidityScopeDifferent}

data ArchitectureInstanceIdentityEqualityFacts =
   MkArchitectureInstanceIdentityEqualityFacts Prelude.Bool Prelude.Bool

architectureInstanceKeyMatches :: ArchitectureInstanceIdentityEqualityFacts
                                  -> Prelude.Bool
architectureInstanceKeyMatches a =
  case a of {
   MkArchitectureInstanceIdentityEqualityFacts architectureInstanceKeyMatches0
    _ -> architectureInstanceKeyMatches0}

architectureInstanceRevisionMatches :: ArchitectureInstanceIdentityEqualityFacts
                                       -> Prelude.Bool
architectureInstanceRevisionMatches a =
  case a of {
   MkArchitectureInstanceIdentityEqualityFacts _
    architectureInstanceRevisionMatches0 ->
    architectureInstanceRevisionMatches0}

architectureInstanceIdentityFactsb :: ArchitectureInstanceIdentityEqualityFacts
                                      -> Prelude.Bool
architectureInstanceIdentityFactsb facts =
  andb (architectureInstanceKeyMatches facts)
    (architectureInstanceRevisionMatches facts)

data ArchitectureInstanceIdentityEqualityDecision =
   ArchitectureInstanceIdentityEqual
 | ArchitectureInstanceIdentityDifferent

decideArchitectureInstanceIdentityEquality :: ArchitectureInstanceIdentityEqualityFacts
                                              ->
                                              ArchitectureInstanceIdentityEqualityDecision
decideArchitectureInstanceIdentityEquality facts =
  case architectureInstanceIdentityFactsb facts of {
   Prelude.True -> ArchitectureInstanceIdentityEqual;
   Prelude.False -> ArchitectureInstanceIdentityDifferent}
