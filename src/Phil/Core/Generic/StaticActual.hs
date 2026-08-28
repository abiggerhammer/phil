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
    DirectGenericStaticActual actualKind semanticForm
      | actualKind == expectedKind -> Right (checked semanticForm)
      | otherwise -> Left
          (GenericStaticDirectKindMismatch parameterKey expectedKind actualKind)
    ReferencedGenericStaticActual referenceName -> do
      semanticForm <- resolveReference
        parameterKey expectedKind referenceName references
      Right (checked semanticForm)
  where
    parameterKey = genericStaticParameterKey parameter
    expectedKind = genericStaticParameterKind parameter
    checked semanticForm = CheckedGenericStaticActual
      { checkedGenericStaticParameterKey = parameterKey
      , checkedGenericStaticKind = expectedKind
      , checkedGenericStaticSemanticForm = semanticForm
      }

resolveReference
  :: GenericStaticParameterKey
  -> GenericStaticKind
  -> Text
  -> [GenericStaticReferenceCandidate]
  -> Either GenericStaticKindError SemanticForm
resolveReference parameterKey expectedKind referenceName references =
  case candidates of
    [] -> Left (GenericStaticReferenceUnresolved parameterKey expectedKind referenceName)
    _ -> case matching of
      [] -> Left (GenericStaticReferenceKindMismatch
        parameterKey expectedKind referenceName availableKinds)
      [candidate] -> Right (genericStaticReferenceSemanticForm candidate)
      many -> Left (GenericStaticReferenceAmbiguous
        parameterKey
        expectedKind
        referenceName
        (map genericStaticReferenceSemanticForm many))
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
    availableKinds = Set.fromList (map genericStaticReferenceKind candidates)
