{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Phil.Compiler.CallableSurfaceSemantics
  ( SurfaceCallableInvocationWitness (..)
  , SurfaceSemanticCheckResult (..)
  , checkSurfaceComponentWithCallableSemantics
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
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
  , SourceSpan
  , Statement (..)
  , SurfaceExpression (..)
  , pattern InvokeExpression
  , SurfaceProposition (..)
  , SurfaceType (..)
  )

-- | Exact semantic contract retained for one ordinary source invocation after
-- the surface checker has accepted lookup, arity, type, and structural transfer.
-- The source span is part of the witness so repeated calls to the same callable
-- remain distinct occurrences for later lifecycle/effect/outcome composition.
data SurfaceCallableInvocationWitness = SurfaceCallableInvocationWitness
  { surfaceInvocationSpan :: SourceSpan
  , surfaceInvocationDisplayName :: Text
  , surfaceInvocationDeclarationKey :: DeclarationKey
  , surfaceInvocationSemanticContract :: SourceCallableSemanticContract
  }
  deriving (Eq, Ord, Show)

-- | CALL-019 semantic enrichment of an ordinary successful surface check.
-- Surface checking remains responsible for syntax, type, and resource shape;
-- this compiler-side bridge binds every explicit `invoke` occurrence to its
-- exact semantic contract without forcing the newer callable subsystem into the
-- legacy surface package boundary. Occurrence order follows source evaluation
-- order within each expression: nested argument invocations precede the caller.
data SurfaceSemanticCheckResult = SurfaceSemanticCheckResult
  { checkedSurfaceResult :: SurfaceCheckResult
  , checkedCallableInvocations :: [SurfaceCallableInvocationWitness]
  , checkedCallableInvocationPaths :: [[SurfaceCallableInvocationWitness]]
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
  let body = componentBody (locatedValue component)
  invocations <- collectBlock contracts environment body
  invocationPaths <- collectBlockPaths contracts environment body
  pure SurfaceSemanticCheckResult
    { checkedSurfaceResult = checked
    , checkedCallableInvocations = invocations
    , checkedCallableInvocationPaths = invocationPaths
    }

collectBlock
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located Block
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectBlock contracts environment block =
  concatM
    (map
      (collectStatement contracts environment)
      (blockStatements (locatedValue block)))

collectStatement
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located Statement
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectStatement contracts environment statement = case locatedValue statement of
  LetStatement _ expression -> collectExpression contracts environment expression
  ReturnStatement expression -> collectExpression contracts environment expression
  ExpressionStatement expression -> collectExpression contracts environment expression

collectExpression
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectExpression contracts environment expression = case locatedValue expression of
  InvokeExpression name arguments -> do
    nested <- concatM (map (collectExpression contracts environment) arguments)
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
    Right (nested <>
      [ SurfaceCallableInvocationWitness
          { surfaceInvocationSpan = locatedSpan expression
          , surfaceInvocationDisplayName = name
          , surfaceInvocationDeclarationKey = declarationKey
          , surfaceInvocationSemanticContract = contract
          }
      ])
  VariableExpression _ -> empty
  IntegerExpression _ -> empty
  BooleanExpression _ -> empty
  UnitExpression -> empty
  TupleExpression values -> expressions values
  CallExpression _ arguments -> expressions arguments
  FieldExpression base _ -> collectExpression contracts environment base
  BinaryExpression _ left right -> expressions [left, right]
  ConstructExpression _ fields -> expressions (map snd fields)
  ReceiveExpression messageType endpoint -> concatM
    [ collectType contracts environment messageType
    , collectExpression contracts environment endpoint
    ]
  ReceiveFrameExpression endpoint -> collectExpression contracts environment endpoint
  RecognizeExpression _ raw -> collectExpression contracts environment raw
  ValidateExpression _ context subject -> concatM
    ( collectExpression contracts environment subject
      : maybe [] (pure . collectExpression contracts environment) context)
  SendExpression value endpoint -> expressions [value, endpoint]
  SendExactExpression value endpoint -> expressions [value, endpoint]
  ReceiveExactExpression count endpoint evidence -> concatM
    ( [ collectExpression contracts environment count
      , collectExpression contracts environment endpoint
      ]
      <> maybe [] (pure . collectExpression contracts environment) evidence)
  SelectExpression branch endpoint evidence -> concatM
    ( collectBranchValue contracts environment branch
      : collectExpression contracts environment endpoint
      : maybe [] (pure . collectExpression contracts environment) evidence)
  CommitReceiveExpression pending evidence -> expressions [pending, evidence]
  BorrowExpression owner _ body -> concatM
    [ collectExpression contracts environment owner
    , collectBlock contracts environment body
    ]
  DecideExpression scrutinee arms -> concatM
    ( collectExpression contracts environment scrutinee
      : map (collectArm contracts environment) arms)
  OfferExpression endpoint arms -> concatM
    ( collectExpression contracts environment endpoint
      : map (collectArm contracts environment) arms)
  FailExpression target resource -> concatM
    [ collectFailureTarget contracts environment target
    , collectExpression contracts environment resource
    ]
  CloseExpression endpoint -> collectExpression contracts environment endpoint
  ReleaseExpression owner -> collectExpression contracts environment owner
  AcceptExpression value acceptedType -> concatM
    [ collectExpression contracts environment value
    , collectType contracts environment acceptedType
    ]
  ProveExpression proposition -> collectProposition contracts environment proposition
  FallbackExpression primary fallback -> concatM
    [ collectExpression contracts environment primary
    , collectFallback contracts environment fallback
    ]
  where
    empty = Right []
    expressions = concatM . map (collectExpression contracts environment)

collectType
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceType
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectType contracts environment surfaceType = case locatedValue surfaceType of
  SurfaceBytesType index -> collectExpression contracts environment index
  SurfaceProofType proposition -> collectProposition contracts environment proposition
  SurfaceValidatedType _ context subject -> concatM
    [ collectExpression contracts environment context
    , collectExpression contracts environment subject
    ]
  SurfaceNamedType _ arguments ->
    concatM (map (collectExpression contracts environment) arguments)
  _ -> Right []

collectProposition
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceProposition
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectProposition contracts environment proposition = case locatedValue proposition of
  PropositionEqual left right -> binary left right
  PropositionNotEqual left right -> binary left right
  PropositionLessThan left right -> binary left right
  PropositionLessEqual left right -> binary left right
  PropositionGreaterThan left right -> binary left right
  PropositionGreaterEqual left right -> binary left right
  PropositionAtom _ arguments ->
    concatM (map (collectExpression contracts environment) arguments)
  PropositionConjunction left right -> propositions left right
  PropositionDisjunction left right -> propositions left right
  PropositionNegation inner -> collectProposition contracts environment inner
  _ -> Right []
  where
    binary left right = concatM
      [ collectExpression contracts environment left
      , collectExpression contracts environment right
      ]
    propositions left right = concatM
      [ collectProposition contracts environment left
      , collectProposition contracts environment right
      ]

collectArm
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located CaseArm
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectArm contracts environment arm =
  collectBlock contracts environment (caseArmBody (locatedValue arm))

collectBranchValue
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> BranchValue
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectBranchValue contracts environment =
  concatM
    . map (collectExpression contracts environment)
    . branchValueArguments

collectFailureTarget
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> FailureTarget
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectFailureTarget contracts environment =
  concatM
    . map (collectExpression contracts environment)
    . failureTargetArguments

collectFallback
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Fallback
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
collectFallback contracts environment fallback = case fallback of
  FailFallback _ -> Right []
  RejectFallback expression -> collectExpression contracts environment expression

-- | Feasible callable-invocation traces through the source control-flow tree.
-- The existing flat invocation list remains the conservative may-occurrence
-- inventory used by effect/authority/failure aggregation. These paths are the
-- separate concrete execution relation used by lifecycle composition.
collectBlockPaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located Block
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectBlockPaths contracts environment block =
  sequencePathResults
    (map
      (collectStatementPaths contracts environment)
      (blockStatements (locatedValue block)))

collectStatementPaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located Statement
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectStatementPaths contracts environment statement = case locatedValue statement of
  LetStatement _ expression -> collectExpressionPaths contracts environment expression
  ReturnStatement expression -> collectExpressionPaths contracts environment expression
  ExpressionStatement expression -> collectExpressionPaths contracts environment expression

collectExpressionPaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectExpressionPaths contracts environment expression = case locatedValue expression of
  InvokeExpression _ arguments -> do
    nested <- sequencePathResults
      (map (collectExpressionPaths contracts environment) arguments)
    flattened <- collectExpression contracts environment expression
    witness <- case reverse flattened of
      value : _ -> Right value
      [] -> Left SurfaceCheckError
        { surfaceErrorSpan = locatedSpan expression
        , surfaceErrorClass = UnknownCallable
        , surfaceErrorDetail =
            "callable invocation produced no semantic witness"
        }
    Right [path <> [witness] | path <- nested]
  VariableExpression _ -> empty
  IntegerExpression _ -> empty
  BooleanExpression _ -> empty
  UnitExpression -> empty
  TupleExpression values -> expressions values
  CallExpression _ arguments -> expressions arguments
  FieldExpression base _ -> collectExpressionPaths contracts environment base
  BinaryExpression _ left right -> expressions [left, right]
  ConstructExpression _ fields -> expressions (map snd fields)
  ReceiveExpression messageType endpoint -> sequencePathResults
    [ collectTypePaths contracts environment messageType
    , collectExpressionPaths contracts environment endpoint
    ]
  ReceiveFrameExpression endpoint -> collectExpressionPaths contracts environment endpoint
  RecognizeExpression _ raw -> collectExpressionPaths contracts environment raw
  ValidateExpression _ context subject -> sequencePathResults
    ( collectExpressionPaths contracts environment subject
      : maybe [] (pure . collectExpressionPaths contracts environment) context)
  SendExpression value endpoint -> expressions [value, endpoint]
  SendExactExpression value endpoint -> expressions [value, endpoint]
  ReceiveExactExpression count endpoint evidence -> sequencePathResults
    ( [ collectExpressionPaths contracts environment count
      , collectExpressionPaths contracts environment endpoint
      ]
      <> maybe [] (pure . collectExpressionPaths contracts environment) evidence)
  SelectExpression branch endpoint evidence -> sequencePathResults
    ( collectBranchValuePaths contracts environment branch
      : collectExpressionPaths contracts environment endpoint
      : maybe [] (pure . collectExpressionPaths contracts environment) evidence)
  CommitReceiveExpression pending evidence -> expressions [pending, evidence]
  BorrowExpression owner _ body -> sequencePathResults
    [ collectExpressionPaths contracts environment owner
    , collectBlockPaths contracts environment body
    ]
  DecideExpression scrutinee arms -> do
    prefix <- collectExpressionPaths contracts environment scrutinee
    alternatives <- alternativePathResults
      (map (collectArmPaths contracts environment) arms)
    Right (combinePathSets prefix alternatives)
  OfferExpression endpoint arms -> do
    prefix <- collectExpressionPaths contracts environment endpoint
    alternatives <- alternativePathResults
      (map (collectArmPaths contracts environment) arms)
    Right (combinePathSets prefix alternatives)
  FailExpression target resource -> sequencePathResults
    [ collectFailureTargetPaths contracts environment target
    , collectExpressionPaths contracts environment resource
    ]
  CloseExpression endpoint -> collectExpressionPaths contracts environment endpoint
  ReleaseExpression owner -> collectExpressionPaths contracts environment owner
  AcceptExpression value acceptedType -> sequencePathResults
    [ collectExpressionPaths contracts environment value
    , collectTypePaths contracts environment acceptedType
    ]
  ProveExpression proposition -> collectPropositionPaths contracts environment proposition
  FallbackExpression primary fallback -> do
    primaryPaths <- collectExpressionPaths contracts environment primary
    fallbackPaths <- collectFallbackPaths contracts environment fallback
    -- A fallback can be reached only after evaluating the primary expression.
    -- Retain both the successful primary trace and the primary-then-fallback
    -- trace instead of treating the two expressions as sequential unconditionally.
    Right (primaryPaths <> combinePathSets primaryPaths fallbackPaths)
  where
    empty = Right [[]]
    expressions = sequencePathResults
      . map (collectExpressionPaths contracts environment)

collectTypePaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceType
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectTypePaths contracts environment surfaceType = case locatedValue surfaceType of
  SurfaceBytesType index -> collectExpressionPaths contracts environment index
  SurfaceProofType proposition -> collectPropositionPaths contracts environment proposition
  SurfaceValidatedType _ context subject -> sequencePathResults
    [ collectExpressionPaths contracts environment context
    , collectExpressionPaths contracts environment subject
    ]
  SurfaceNamedType _ arguments ->
    sequencePathResults (map (collectExpressionPaths contracts environment) arguments)
  _ -> Right [[]]

collectPropositionPaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located SurfaceProposition
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectPropositionPaths contracts environment proposition = case locatedValue proposition of
  PropositionEqual left right -> binary left right
  PropositionNotEqual left right -> binary left right
  PropositionLessThan left right -> binary left right
  PropositionLessEqual left right -> binary left right
  PropositionGreaterThan left right -> binary left right
  PropositionGreaterEqual left right -> binary left right
  PropositionAtom _ arguments ->
    sequencePathResults (map (collectExpressionPaths contracts environment) arguments)
  PropositionConjunction left right -> propositions left right
  PropositionDisjunction left right -> propositions left right
  PropositionNegation inner -> collectPropositionPaths contracts environment inner
  _ -> Right [[]]
  where
    binary left right = sequencePathResults
      [ collectExpressionPaths contracts environment left
      , collectExpressionPaths contracts environment right
      ]
    propositions left right = sequencePathResults
      [ collectPropositionPaths contracts environment left
      , collectPropositionPaths contracts environment right
      ]

collectArmPaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Located CaseArm
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectArmPaths contracts environment arm =
  collectBlockPaths contracts environment (caseArmBody (locatedValue arm))

collectBranchValuePaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> BranchValue
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectBranchValuePaths contracts environment =
  sequencePathResults
    . map (collectExpressionPaths contracts environment)
    . branchValueArguments

collectFailureTargetPaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> FailureTarget
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectFailureTargetPaths contracts environment =
  sequencePathResults
    . map (collectExpressionPaths contracts environment)
    . failureTargetArguments

collectFallbackPaths
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceEnvironment
  -> Fallback
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
collectFallbackPaths contracts environment fallback = case fallback of
  FailFallback _ -> Right [[]]
  RejectFallback expression -> collectExpressionPaths contracts environment expression

sequencePathResults
  :: [Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]]
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
sequencePathResults results =
  sequence results >>= Right . foldl combinePathSets [[]]

alternativePathResults
  :: [Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]]
  -> Either SurfaceCheckError [[SurfaceCallableInvocationWitness]]
alternativePathResults results = fmap concat (sequence results)

combinePathSets
  :: [[SurfaceCallableInvocationWitness]]
  -> [[SurfaceCallableInvocationWitness]]
  -> [[SurfaceCallableInvocationWitness]]
combinePathSets left right =
  [ leftPath <> rightPath
  | leftPath <- left
  , rightPath <- right
  ]

concatM
  :: [Either SurfaceCheckError [SurfaceCallableInvocationWitness]]
  -> Either SurfaceCheckError [SurfaceCallableInvocationWitness]
concatM = fmap concat . sequence
