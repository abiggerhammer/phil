module Phil.Compiler.CallableAuthorityPossession
  ( CallableAuthorityPossessionBinding (..)
  , CheckedCallableAuthorityPossession (..)
  , CallableAuthorityPossessionError (..)
  , derivePossessedCallableAuthority
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Core.Authority
  ( AuthorityCheckError
  , AuthorityExerciseSource (..)
  , AuthorityRequirement
  , AuthorityState
  , CapabilityOccurrenceKey
  , CheckedAuthorityExercise
  , checkAuthorityExercise
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement
  )

-- | Explicit relation between one stabilized callable-level authority identity
-- and the exact Core authority requirement/capability occurrence claimed to
-- satisfy it. The callable label is intentionally not parsed or interpreted:
-- this binding is the semantic handoff from declaration/architecture competence
-- into the exact possession checker.
data CallableAuthorityPossessionBinding = CallableAuthorityPossessionBinding
  { callableAuthorityBindingRequirement :: CallableAuthorityRequirement
  , callableAuthorityBindingExactRequirement :: AuthorityRequirement
  , callableAuthorityBindingCapabilityOccurrence :: CapabilityOccurrenceKey
  }
  deriving (Eq, Ord, Show)

-- | Successful authority handoff for one callable requirement. Retaining the
-- exact CheckedAuthorityExercise prevents later caller-context code from
-- replacing possession evidence with mere label membership.
data CheckedCallableAuthorityPossession = CheckedCallableAuthorityPossession
  { checkedCallableAuthorityRequirement :: CallableAuthorityRequirement
  , checkedCallableAuthorityExercise :: CheckedAuthorityExercise
  }
  deriving (Eq, Ord, Show)

data CallableAuthorityPossessionError
  = CallableAuthorityBindingMissing CallableAuthorityRequirement
  | CallableAuthorityBindingKeyMismatch
      CallableAuthorityRequirement
      CallableAuthorityRequirement
  | CallableAuthorityExerciseRejected
      CallableAuthorityRequirement
      AuthorityCheckError
  deriving (Eq, Ord, Show)

-- | Establish exactly the callable authority requirements requested by a source
-- invocation summary. Every requested label must have an explicit binding, that
-- binding must be keyed by the same opaque callable authority identity, and its
-- exact requirement must be accepted by Phil.Core.Authority from one actually
-- possessed capability occurrence. Extra catalog entries are harmless: this
-- function proves only the requested finite set and cannot manufacture labels
-- from ambient declarations, effect permissions, runtime handles, or names.
derivePossessedCallableAuthority
  :: Set CallableAuthorityRequirement
  -> Map CallableAuthorityRequirement CallableAuthorityPossessionBinding
  -> AuthorityState
  -> Either CallableAuthorityPossessionError
       (Set CallableAuthorityRequirement, [CheckedCallableAuthorityPossession])
derivePossessedCallableAuthority required bindings authorityState = do
  checked <- mapM checkOne (Set.toAscList required)
  pure (Set.fromList (map checkedCallableAuthorityRequirement checked), checked)
  where
    checkOne requirement = do
      binding <- maybe
        (Left (CallableAuthorityBindingMissing requirement))
        Right
        (Map.lookup requirement bindings)
      if callableAuthorityBindingRequirement binding == requirement
        then pure ()
        else Left
          (CallableAuthorityBindingKeyMismatch
            requirement
            (callableAuthorityBindingRequirement binding))
      exercise <- mapLeft (CallableAuthorityExerciseRejected requirement) $
        checkAuthorityExercise
          (callableAuthorityBindingExactRequirement binding)
          (PossessedCapability
            (callableAuthorityBindingCapabilityOccurrence binding))
          authorityState
      pure CheckedCallableAuthorityPossession
        { checkedCallableAuthorityRequirement = requirement
        , checkedCallableAuthorityExercise = exercise
        }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
