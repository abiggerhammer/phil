module Phil.Surface.GrammarV1.CapabilityContract
  ( GrammarV1CheckedCapabilityContract (..)
  , grammarV1CheckedClosedCapabilityContract
  ) where

import Data.Text (Text)
import Phil.Core.Authority
  ( AuthorityContractKey
  , AuthorityOperationKey (..)
  )
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Mode
  , Proposition
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  , grammarV1StructuralMode
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CapabilityDecl (..)
  , GrammarV1CapabilityItem (..)
  , GrammarV1StaticArgument (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Checked semantic surface of one closed capability declaration. Stable
-- authority-contract identity is supplied by lineage-aware declaration handling
-- above Grammar v1 rather than being derived from the source display name.
--
-- The declaration's structural mode is preserved exactly. Bare unspecialized
-- permit references become exact Core AuthorityOperationKey values. Capability
-- requirements and named laws are checked through the ordinary Core proposition
-- focusing path under an empty top-level term scope. Source item order controls
-- failure precedence; successful values preserve order within each semantic
-- category.
--
-- This is deliberately a contract descriptor, not a possessed capability:
-- occurrence identity and authority subject are runtime/architecture semantic
-- inputs and are not manufactured from a declaration. Generic parameters,
-- generic requirements, specialized operation references, and proposition forms
-- outside current checked competence remain fail-closed.
data GrammarV1CheckedCapabilityContract = GrammarV1CheckedCapabilityContract
  { checkedCapabilityContractKey :: AuthorityContractKey
  , checkedCapabilityContractMode :: Mode
  , checkedCapabilityContractOperations :: [AuthorityOperationKey]
  , checkedCapabilityContractRequirements :: [(Proposition, [FocusStep])]
  , checkedCapabilityContractLaws :: [(Text, Proposition, [FocusStep])]
  }
  deriving (Eq, Show)

grammarV1CheckedClosedCapabilityContract
  :: StaticContext
  -> AuthorityContractKey
  -> GrammarV1CapabilityDecl
  -> Maybe (Either FocusingError GrammarV1CheckedCapabilityContract)
grammarV1CheckedClosedCapabilityContract staticContext contractKey source
  | not (null (grammarV1CapabilityGenericParams source)) = Nothing
  | not (null (grammarV1CapabilityRequirements source)) = Nothing
  | otherwise =
      go (grammarV1CapabilityItems source) [] [] []
  where
    mode = grammarV1StructuralMode (grammarV1CapabilityMode source)

    go [] operations requirements laws = Just (Right GrammarV1CheckedCapabilityContract
      { checkedCapabilityContractKey = contractKey
      , checkedCapabilityContractMode = mode
      , checkedCapabilityContractOperations = reverse operations
      , checkedCapabilityContractRequirements = reverse requirements
      , checkedCapabilityContractLaws = reverse laws
      })
    go (Located _ item : rest) operations requirements laws = case item of
      GrammarV1CapabilityPermits (Located _ reference) -> do
        operation <- bareOperationKey reference
        go rest (operation : operations) requirements laws
      GrammarV1CapabilityRequires (Located _ proposition) -> do
        checked <- grammarV1CheckedProposition
          staticContext
          emptySurfaceState
          proposition
        case checked of
          Left err -> Just (Left err)
          Right accepted -> go rest operations (accepted : requirements) laws
      GrammarV1CapabilityLaw (Located _ lawName) (Located _ proposition) -> do
        checked <- grammarV1CheckedProposition
          staticContext
          emptySurfaceState
          proposition
        case checked of
          Left err -> Just (Left err)
          Right (accepted, steps) ->
            go rest operations requirements ((lawName, accepted, steps) : laws)

bareOperationKey :: GrammarV1StaticReference -> Maybe AuthorityOperationKey
bareOperationKey reference =
  case grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference) of
    Just (ReferencedGenericStaticActual identity) ->
      Just (AuthorityOperationKey identity)
    _ -> Nothing
