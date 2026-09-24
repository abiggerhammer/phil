module Phil.Core.Checker
  ( CheckState (..)
  , LogicalSubjectSupport (..)
  , CheckerError (..)
  , emptyCheckState
  , emitObligation
  , withObligationLogicalSubjects
  , completeComponent
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , emptyContext
  , ensureComplete
  )
import Phil.Core.Syntax
  ( Name
  , Obligation (..)
  , ObligationId
  , Proposition (..)
  , RefTerm (..)
  , Ty
  )

data LogicalSubjectSupport = LogicalSubjectSupport
  { logicalSupportObligation :: Obligation
  , logicalSupportBindings :: Map Name Ty
  , logicalSupportUnrestrictedBindings :: Map Name Ty
  }
  deriving (Eq, Show)

data CheckState = CheckState
  { resourceContext :: ResourceContext
  , residualObligations :: Map ObligationId Obligation
  , residualLogicalSubjects :: Map ObligationId LogicalSubjectSupport
  , logicalTypingContext :: Map Name Ty
  }
  deriving (Eq, Show)

data CheckerError
  = ResourceError CheckError
  | ConflictingObligationId Obligation Obligation
  | ConflictingLogicalSubjectSupport
      ObligationId
      LogicalSubjectSupport
      LogicalSubjectSupport
  deriving (Eq, Show)

emptyCheckState :: CheckState
emptyCheckState = CheckState
  { resourceContext = emptyContext
  , residualObligations = Map.empty
  , residualLogicalSubjects = Map.empty
  , logicalTypingContext = Map.empty
  }

-- | Emit an obligation together with the exact refinement-visible resource
-- bindings needed to interpret variables in its proposition.  The support is
-- keyed by the obligation identity and retains the complete obligation record,
-- so a later same-spelled resource cannot silently stand in for the original
-- logical subject.  Referenced unrestricted bindings are recorded separately:
-- unlike affine and linear bindings, the public ResourceContext transitions do
-- not consume or replace them, so a still-present exact binding can retain its
-- original fact authority without restoring any consumed resource.
emitObligation :: Obligation -> CheckState -> Either CheckerError CheckState
emitObligation obligation state =
  case Map.lookup obligationId' (residualObligations state) of
    Nothing -> Right (state
      { residualObligations =
          Map.insert obligationId' obligation (residualObligations state)
      , residualLogicalSubjects =
          Map.insert obligationId' support (residualLogicalSubjects state)
      })
    Just existing
      | existing /= obligation -> Left (ConflictingObligationId existing obligation)
      | otherwise ->
          case Map.lookup obligationId' (residualLogicalSubjects state) of
            Nothing -> Right (state
              { residualLogicalSubjects =
                  Map.insert obligationId' support (residualLogicalSubjects state)
              })
            Just existingSupport
              | existingSupport == support -> Right state
              | otherwise -> Left
                  (ConflictingLogicalSubjectSupport
                    obligationId'
                    existingSupport
                    support)
  where
    obligationId' = obligationId obligation
    support = LogicalSubjectSupport
      { logicalSupportObligation = obligation
      , logicalSupportBindings = referencedResourceBindings obligation state
      , logicalSupportUnrestrictedBindings =
          referencedUnrestrictedBindings obligation state
      }

-- | Activate only the durable logical typing support captured for this exact
-- obligation.  It is deliberately separate from ResourceContext: it grants no
-- ownership, loan, or proof-evidence authority.  A mismatched obligation record
-- receives no support even when its id or variable spelling happens to match.
withObligationLogicalSubjects :: Obligation -> CheckState -> CheckState
withObligationLogicalSubjects obligation state =
  state
    { logicalTypingContext =
        case Map.lookup (obligationId obligation) (residualLogicalSubjects state) of
          Just support
            | logicalSupportObligation support == obligation ->
                logicalSupportBindings support
          _ -> Map.empty
    }

completeComponent :: CheckState -> Either CheckerError CheckState
completeComponent state =
  case ensureComplete (resourceContext state) of
    Left err -> Left (ResourceError err)
    Right () -> Right state

referencedResourceBindings :: Obligation -> CheckState -> Map Name Ty
referencedResourceBindings obligation state =
  Map.fromList
    [ (name, ty)
    | name <- referencedNames obligation
    , Just ty <- [lookupResourceBinding name (resourceContext state)]
    ]

referencedUnrestrictedBindings :: Obligation -> CheckState -> Map Name Ty
referencedUnrestrictedBindings obligation state =
  Map.fromList
    [ (name, ty)
    | name <- referencedNames obligation
    , Just ty <- [Map.lookup name (unrestrictedBindings (resourceContext state))]
    ]

referencedNames :: Obligation -> [Name]
referencedNames obligation =
  Set.toAscList (propositionVariables (obligationProposition obligation))

lookupResourceBinding :: Name -> ResourceContext -> Maybe Ty
lookupResourceBinding name context =
  Map.lookup name (unrestrictedBindings context)
    `orElse` Map.lookup name (affineBindings context)
    `orElse` Map.lookup name (linearBindings context)

propositionVariables :: Proposition -> Set.Set Name
propositionVariables proposition =
  case proposition of
    Truth -> Set.empty
    Falsehood -> Set.empty
    Equal left right -> termVariables left `Set.union` termVariables right
    NotEqual left right -> termVariables left `Set.union` termVariables right
    LessThan left right -> termVariables left `Set.union` termVariables right
    LessEqual left right -> termVariables left `Set.union` termVariables right
    Member value collection -> termVariables value `Set.union` termVariables collection
    Disjoint left right -> termVariables left `Set.union` termVariables right
    Conjunction left right -> propositionVariables left `Set.union` propositionVariables right
    Disjunction left right -> propositionVariables left `Set.union` propositionVariables right
    Negation inner -> propositionVariables inner
    Atom _ arguments -> Set.unions (map termVariables arguments)

termVariables :: RefTerm -> Set.Set Name
termVariables term =
  case term of
    RefVar name -> Set.singleton name
    RefField base _ _ -> termVariables base
    RefLen value -> termVariables value
    RefToNat value -> termVariables value
    RefAdd left right -> termVariables left `Set.union` termVariables right
    RefSub left right -> termVariables left `Set.union` termVariables right
    RefScale _ value -> termVariables value
    _ -> Set.empty

orElse :: Maybe a -> Maybe a -> Maybe a
orElse Nothing right = right
orElse left _ = left
