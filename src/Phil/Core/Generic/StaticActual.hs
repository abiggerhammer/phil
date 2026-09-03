{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  , GenericStaticActual (..)
  , GenericStaticReferenceCandidate (..)
  , CheckedGenericStaticActual (..)
  , GenericStaticKindError (..)
  , checkGenericStaticActuals
  ) where

import Data.List (foldl')
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Generic (GenericStaticParameterKey)
import Phil.Core.GenericStaticKindKernelBridge
  ( CertifiedCheckedStaticActualShapeDecision (..)
  , CertifiedDirectStaticActualDecision (..)
  , CertifiedReferencedStaticActualDecision (..)
  , certifiedCheckedStaticActualShapeDecision
  , certifiedDirectStaticActualDecision
  , certifiedReferencedStaticActualDecision
  )
import Phil.Core.Static (SemanticForm)

data GenericStaticKind
  = GenericTypeKind
  | GenericIndexKind
  | GenericSessionKind
  | GenericMessageKind
  | GenericEffectsKind
  | GenericProviderContractKind
  | GenericCallableContractKind
  | GenericBoundaryContractKind
  | GenericArchitectureDependencyKind
  deriving (Eq, Ord, Show)

data GenericStaticParameter = GenericStaticParameter
  { genericStaticParameterKey :: GenericStaticParameterKey
  , genericStaticParameterKind :: GenericStaticKind
  }
  deriving (Eq, Ord, Show)

-- | Parsing has already chosen one concrete actual form. A name-shaped static
-- reference stays one reference and is interpreted only through the declared
-- parameter kind; this checker never retries it under another category.
data GenericStaticActual
  = DirectGenericStaticActual GenericStaticKind SemanticForm
  | ReferencedGenericStaticActual Text
  deriving (Eq, Ord, Show)

data GenericStaticReferenceCandidate = GenericStaticReferenceCandidate
  { genericStaticReferenceName :: Text
  , genericStaticReferenceKind :: GenericStaticKind
  , genericStaticReferenceSemanticForm :: SemanticForm
  }
  deriving (Eq, Ord, Show)

data CheckedGenericStaticActual = CheckedGenericStaticActual
  { checkedGenericStaticParameterKey :: GenericStaticParameterKey
  , checkedGenericStaticKind :: GenericStaticKind
  , checkedGenericStaticSemanticForm :: SemanticForm
  }
  deriving (Eq, Ord, Show)

data GenericStaticKindError
  = DuplicateGenericStaticParameter GenericStaticParameterKey
  | GenericStaticActualCountMismatch Int Int
  | GenericStaticDirectKindMismatch
      GenericStaticParameterKey
      GenericStaticKind
      GenericStaticKind
  | GenericStaticReferenceUnresolved
      GenericStaticParameterKey
      GenericStaticKind
      Text
  | GenericStaticReferenceKindMismatch
      GenericStaticParameterKey
      GenericStaticKind
      Text
      (Set.Set GenericStaticKind)
  | GenericStaticReferenceAmbiguous
      GenericStaticParameterKey
      GenericStaticKind
      Text
      [SemanticForm]
  | GenericStaticKindKernelDisagreement
  deriving (Eq, Show)

checkGenericStaticActuals
  :: [GenericStaticParameter]
  -> [GenericStaticActual]
  -> [GenericStaticReferenceCandidate]
  -> Either GenericStaticKindError [CheckedGenericStaticActual]
checkGenericStaticActuals parameters actuals references = do
  ensureUniqueParameters parameters
  if length parameters == length actuals
    then mapM (uncurry (checkActual references)) (zip parameters actuals)
    else Left (GenericStaticActualCountMismatch (length parameters) (length actuals))

ensureUniqueParameters
  :: [GenericStaticParameter]
  -> Either GenericStaticKindError ()
ensureUniqueParameters parameters =
  foldl' insertKey (Right Set.empty) parameters >> Right ()
  where
    insertKey accumulated parameter = do
      seen <- accumulated
      let key = genericStaticParameterKey parameter
      if Set.member key seen
        then Left (DuplicateGenericStaticParameter key)
        else Right (Set.insert key seen)

checkActual
  :: [GenericStaticReferenceCandidate]
  -> GenericStaticParameter
  -> GenericStaticActual
  -> Either GenericStaticKindError CheckedGenericStaticActual
checkActual references parameter actual =
  case actual of
    DirectGenericStaticActual actualKind semanticForm ->
      case certifiedDirectStaticActualDecision (actualKind == expectedKind) of
        CertifiedDirectStaticActualAccepted -> checked semanticForm
        CertifiedDirectStaticActualKindMismatch ->
          Left (GenericStaticDirectKindMismatch parameterKey expectedKind actualKind)
        CertifiedDirectStaticActualKernelDisagreement ->
          Left GenericStaticKindKernelDisagreement
    ReferencedGenericStaticActual referenceName -> do
      semanticForm <- resolveReference
        parameterKey expectedKind referenceName references
      checked semanticForm
  where
    parameterKey = genericStaticParameterKey parameter
    expectedKind = genericStaticParameterKind parameter
    checked semanticForm = do
      let result = CheckedGenericStaticActual
            { checkedGenericStaticParameterKey = parameterKey
            , checkedGenericStaticKind = expectedKind
            , checkedGenericStaticSemanticForm = semanticForm
            }
          parameterKeyExact = checkedGenericStaticParameterKey result == parameterKey
          kindExact = checkedGenericStaticKind result == expectedKind
      case certifiedCheckedStaticActualShapeDecision parameterKeyExact kindExact of
        CertifiedCheckedStaticActualShapeAccepted -> Right result
        _ -> Left GenericStaticKindKernelDisagreement

resolveReference
  :: GenericStaticParameterKey
  -> GenericStaticKind
  -> Text
  -> [GenericStaticReferenceCandidate]
  -> Either GenericStaticKindError SemanticForm
resolveReference parameterKey expectedKind referenceName references =
  case certifiedReferencedStaticActualDecision
      nameExists expectedKindPresent expectedKindUnique selectedSemanticFormExact of
    CertifiedReferencedStaticActualUnresolved ->
      Left (GenericStaticReferenceUnresolved parameterKey expectedKind referenceName)
    CertifiedReferencedStaticActualKindMismatch ->
      Left (GenericStaticReferenceKindMismatch
        parameterKey expectedKind referenceName availableKinds)
    CertifiedReferencedStaticActualAmbiguous ->
      Left (GenericStaticReferenceAmbiguous
        parameterKey expectedKind referenceName matchingForms)
    CertifiedReferencedStaticActualAccepted ->
      case matching of
        [candidate] -> Right (genericStaticReferenceSemanticForm candidate)
        _ -> Left GenericStaticKindKernelDisagreement
    CertifiedReferencedStaticActualSemanticFormMismatch ->
      Left GenericStaticKindKernelDisagreement
    CertifiedReferencedStaticActualKernelDisagreement ->
      Left GenericStaticKindKernelDisagreement
  where
    candidates =
      [ candidate
      | candidate <- references
      , genericStaticReferenceName candidate == referenceName
      ]
    matching =
      [ candidate
      | candidate <- candidates
      , genericStaticReferenceKind candidate == expectedKind
      ]
    matchingForms = map genericStaticReferenceSemanticForm matching
    availableKinds = Set.fromList (map genericStaticReferenceKind candidates)
    nameExists = not (null candidates)
    expectedKindPresent = not (null matching)
    expectedKindUnique = length matching == 1
    selectedSemanticFormExact = case matching of
      [candidate] ->
        case matchingForms of
          [selected] -> selected == genericStaticReferenceSemanticForm candidate
          _ -> False
      _ -> False
