{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Phil.Compiler.CallableSurfaceSemantics
  ( SurfaceCallableInvocationWitness (..)
  , SurfaceSemanticCheckResult (..)
  , checkSurfaceComponentWithCallableSemantics
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Core.CallableSemanticContract
  ( SourceCallableSemanticContract
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCallableSignature (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult
  , SurfaceEnvironment (..)
  , checkSurfaceComponent
  )
import Phil.Surface.Syntax
  ( Block (..)
  , BranchValue (..)
  , CaseArm (..)
  , Component (..)
  , FailureTarget (..)
  , Fallback (..)
  , Located (..)
  , Statement (..)
  , SurfaceExpression (..)
  , pattern InvokeExpression
  , SurfaceProposition (..)
  , SurfaceType (..)
  )

-- | Exact semantic contract retained for one ordinary source invocation after
-- the surface checker has accepted lookup, arity, type, and structural transfer.
-- The display spelling is diagnostic only; declaration identity and the complete
-- semantic contract are the authority.
data SurfaceCallableInvocationWitness = SurfaceCallableInvocationWitness
  { surfaceInvocationDisplayName :: Text
  , surfaceInvocationDeclarationKey :: DeclarationKey
  , surfaceInvocationSemanticContract :: SourceCallableSemanticContract
  }
  deriving (Eq, Ord, Show)

-- | CALL-019 semantic enrichment of an ordinary successful surface check.
-- Surface checking remains responsible for syntax, type, and resource shape;
-- this compiler-side bridge binds every explicit `invoke` to its exact semantic
-- contract without forcing the newer callable subsystem into the legacy surface
-- package boundary.
data SurfaceSemanticCheckResult = SurfaceSemanticCheckResult
  { checkedSurfaceResult :: SurfaceCheckResult
  , checkedCallableInvocations :: Set SurfaceCallableInvocationWitness
  }
  deriving (Eq, Show)

-- | Check a component normally, then require a complete semantic contract for
-- every explicit source invocation. Contracts are keyed by exact DeclarationKey,
-- never by display spelling. Missing semantic authority fails closed instead of
-- silently degrading to the shape-only call surface.
checkSurfaceComponentWithCallableSemantics
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceSemanticCheckResult
checkSurfaceComponentWithCallableSemantics contracts environment component = do
  checked <- checkSurfaceComponent environment component
  invocations <- collectBlock contracts environment
    (componentBody (locatedValue component))
  pure SurfaceSemanticCheckResult
    { checkedSurfaceResult = checked
    , checkedCallableInvocations = invocations
    }

collectBlock
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located Block
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectBlock contracts environment block =
  unionsM
    (map
      (collectStatement contracts environment)
      (blockStatements (locatedValue block)))

collectStatement
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located Statement
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectStatement contracts environment statement = case locatedValue statement of
  LetStatement _ expression -> collectExpression contracts environment expression
  ReturnStatement expression -> collectExpression contracts environment expression
  ExpressionStatement expression -> collectExpression contracts environment expression

collectExpression
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectExpression contracts environment expression = case locatedValue expression of
  InvokeExpression name arguments -> do
    nested <- unionsM (map (collectExpression contracts environment) arguments)
    signature <- maybe
      (Left SurfaceCheckError
        { surfaceErrorSpan = locatedSpan expression
        , surfaceErrorClass = UnknownCallable
        , surfaceErrorDetail =
            "callable disappeared before semantic invocation composition: " <> name
        })
      Right
      (Map.lookup name (surfaceCallables environment))
    let declarationKey = surfaceCallableDeclarationKey signature
    contract <- maybe
      (Left SurfaceCheckError
        { surfaceErrorSpan = locatedSpan expression
        , surfaceErrorClass = UnknownCallable
        , surfaceErrorDetail =
            "callable semantic contract missing for exact declaration identity"
        })
      Right
      (Map.lookup declarationKey contracts)
    Right (Set.insert
      SurfaceCallableInvocationWitness
        { surfaceInvocationDisplayName = name
        , surfaceInvocationDeclarationKey = declarationKey
        , surfaceInvocationSemanticContract = contract
        }
      nested)
  VariableExpression _ -> empty
  IntegerExpression _ -> empty
  BooleanExpression _ -> empty
  UnitExpression -> empty
  TupleExpression values -> expressions values
  CallExpression _ arguments -> expressions arguments
  FieldExpression base _ -> collectExpression contracts environment base
  BinaryExpression _ left right -> expressions [left, right]
  ConstructExpression _ fields -> expressions (map snd fields)
  ReceiveExpression messageType endpoint -> unionsM
    [ collectType contracts environment messageType
    , collectExpression contracts environment endpoint
    ]
  ReceiveFrameExpression endpoint -> collectExpression contracts environment endpoint
  RecognizeExpression _ raw -> collectExpression contracts environment raw
  ValidateExpression _ context subject -> unionsM
    ( collectExpression contracts environment subject
      : maybe [] (pure . collectExpression contracts environment) context)
  SendExpression value endpoint -> expressions [value, endpoint]
  SendExactExpression value endpoint -> expressions [value, endpoint]
  ReceiveExactExpression count endpoint evidence -> unionsM
    ( [ collectExpression contracts environment count
      , collectExpression contracts environment endpoint
      ]
      <> maybe [] (pure . collectExpression contracts environment) evidence)
  SelectExpression branch endpoint evidence -> unionsM
    ( collectBranchValue contracts environment branch
      : collectExpression contracts environment endpoint
      : maybe [] (pure . collectExpression contracts environment) evidence)
  CommitReceiveExpression pending evidence -> expressions [pending, evidence]
  BorrowExpression owner _ body -> unionsM
    [ collectExpression contracts environment owner
    , collectBlock contracts environment body
    ]
  DecideExpression scrutinee arms -> unionsM
    ( collectExpression contracts environment scrutinee
      : map (collectArm contracts environment) arms)
  OfferExpression endpoint arms -> unionsM
    ( collectExpression contracts environment endpoint
      : map (collectArm contracts environment) arms)
  FailExpression target resource -> unionsM
    [ collectFailureTarget contracts environment target
    , collectExpression contracts environment resource
    ]
  CloseExpression endpoint -> collectExpression contracts environment endpoint
  ReleaseExpression owner -> collectExpression contracts environment owner
  AcceptExpression value acceptedType -> unionsM
    [ collectExpression contracts environment value
    , collectType contracts environment acceptedType
    ]
  ProveExpression proposition -> collectProposition contracts environment proposition
  FallbackExpression primary fallback -> unionsM
    [ collectExpression contracts environment primary
    , collectFallback contracts environment fallback
    ]
  where
    empty = Right Set.empty
    expressions = unionsM . map (collectExpression contracts environment)

collectType
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceType
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectType contracts environment surfaceType = case locatedValue surfaceType of
  SurfaceBytesType index -> collectExpression contracts environment index
  SurfaceProofType proposition -> collectProposition contracts environment proposition
  SurfaceValidatedType _ context subject -> unionsM
    [ collectExpression contracts environment context
    , collectExpression contracts environment subject
    ]
  SurfaceNamedType _ arguments ->
    unionsM (map (collectExpression contracts environment) arguments)
  _ -> Right Set.empty

collectProposition
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceProposition
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectProposition contracts environment proposition = case locatedValue proposition of
  PropositionEqual left right -> binary left right
  PropositionNotEqual left right -> binary left right
  PropositionLessThan left right -> binary left right
  PropositionLessEqual left right -> binary left right
  PropositionGreaterThan left right -> binary left right
  PropositionGreaterEqual left right -> binary left right
  PropositionAtom _ arguments ->
    unionsM (map (collectExpression contracts environment) arguments)
  PropositionConjunction left right -> propositions left right
  PropositionDisjunction left right -> propositions left right
  PropositionNegation inner -> collectProposition contracts environment inner
  _ -> Right Set.empty
  where
    binary left right = unionsM
      [ collectExpression contracts environment left
      , collectExpression contracts environment right
      ]
    propositions left right = unionsM
      [ collectProposition contracts environment left
      , collectProposition contracts environment right
      ]

collectArm
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located CaseArm
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectArm contracts environment arm =
  collectBlock contracts environment (caseArmBody (locatedValue arm))

collectBranchValue
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> BranchValue
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectBranchValue contracts environment =
  unionsM
    . map (collectExpression contracts environment)
    . branchValueArguments

collectFailureTarget
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> FailureTarget
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectFailureTarget contracts environment =
  unionsM
    . map (collectExpression contracts environment)
    . failureTargetArguments

collectFallback
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Fallback
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
collectFallback contracts environment fallback = case fallback of
  FailFallback _ -> Right Set.empty
  RejectFallback expression -> collectExpression contracts environment expression

unionsM
  :: [Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)]
  -> Either SurfaceCheckError (Set SurfaceCallableInvocationWitness)
unionsM = fmap Set.unions . sequence
