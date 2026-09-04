module Phil.Surface.GrammarV1.GenericTermScope
  ( GrammarV1CheckedGenericTermScope (..)
  , GrammarV1GenericTermScopeError (..)
  , grammarV1CheckedFunctionGenericTermScope
  , grammarV1CheckedCallableGenericTermScope
  , grammarV1CheckedClaimGenericTermScope
  , grammarV1CheckedComponentGenericTermScope
  , grammarV1CheckedProviderImplementationGenericTermScope
  , grammarV1CheckedProtocolGenericTermScope
  , grammarV1TermBinderSitesInBlock
  ) where

import Data.Text (Text)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.GenericBinderScope
  ( GrammarV1GenericBinderScope
  , GrammarV1GenericBinderScopeError (..)
  , GrammarV1ResolvedGenericParameter
  , grammarV1BindGenericParameters
  , grammarV1ResolveGenericParameter
  , grammarV1RootGenericBinderScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1BranchValue (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1CaseBinders (..)
  , GrammarV1CasePattern (..)
  , GrammarV1ClaimDecl (..)
  , GrammarV1Closure (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1Fallback (..)
  , GrammarV1FieldBinder (..)
  , GrammarV1FieldPattern (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1GenericParam
  , GrammarV1JoinClause (..)
  , GrammarV1MatchArm (..)
  , GrammarV1MatchArmBody (..)
  , GrammarV1Pattern (..)
  , GrammarV1ProtocolDecl (..)
  , GrammarV1ProviderImplementationDecl (..)
  , GrammarV1ProviderImplementationItem (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StateBinding (..)
  , GrammarV1StateSlot (..)
  , GrammarV1Statement (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Cross-domain scope evidence for one declaration. Generic-static parameters
-- retain their exact GenericStaticParameterKey identities from GenericBinderScope;
-- term binder sites retain only source locations here because their semantic
-- BinderKey/Core Name allocation remains owned by the existing term-scope modules.
data GrammarV1CheckedGenericTermScope = GrammarV1CheckedGenericTermScope
  { grammarV1CheckedGenericTermParameters :: [GrammarV1ResolvedGenericParameter]
  , grammarV1CheckedGenericTermBinderSites :: [Located Text]
  }
  deriving (Eq, Show)

data GrammarV1GenericTermScopeError
  = GrammarV1GenericTermGenericBinderError GrammarV1GenericBinderScopeError
  | GrammarV1GenericTermActiveStaticShadowing
      (Located Text)
      GrammarV1ResolvedGenericParameter
  deriving (Eq, Show)

-- | Compose a function's declaration-wide static telescope with every runtime
-- binder site reachable in its term body. A static generic binder remains active
-- throughout the declaration, so a same-spelled term parameter, nested pattern,
-- arm binder, borrow view, join/loop state slot, or closure parameter rejects.
grammarV1CheckedFunctionGenericTermScope
  :: DeclarationKey
  -> GrammarV1FunctionDecl
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
grammarV1CheckedFunctionGenericTermScope declarationKey source =
  checkedGenericTermScope
    declarationKey
    (grammarV1FunctionGenericParams source)
    ( termParameterSites (grammarV1FunctionTermParams source)
      <> grammarV1TermBinderSitesInBlock (grammarV1FunctionBody source)
    )

-- | Callable contracts have a static telescope and a term-parameter telescope
-- but no implementation body. The two namespaces remain semantically distinct
-- and a term parameter may not hide an active generic parameter.
grammarV1CheckedCallableGenericTermScope
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
grammarV1CheckedCallableGenericTermScope declarationKey source =
  checkedGenericTermScope
    declarationKey
    (grammarV1CallableGenericParams source)
    (termParameterSites (grammarV1CallableTermParams source))

-- | Claim term parameters share the declaration with generic-static parameters
-- and therefore obey the same no-active-shadowing boundary.
grammarV1CheckedClaimGenericTermScope
  :: DeclarationKey
  -> GrammarV1ClaimDecl
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
grammarV1CheckedClaimGenericTermScope declarationKey source =
  checkedGenericTermScope
    declarationKey
    (grammarV1ClaimGenericParams source)
    (maybe [] termParameterSites (grammarV1ClaimTermParams source))

-- | Component term parameters and all body-local binder families are checked
-- against the component's still-active generic telescope.
grammarV1CheckedComponentGenericTermScope
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
grammarV1CheckedComponentGenericTermScope declarationKey source =
  checkedGenericTermScope
    declarationKey
    (grammarV1ComponentGenericParams source)
    ( maybe [] termParameterSites (grammarV1ComponentTermParams source)
      <> grammarV1TermBinderSitesInBlock (grammarV1ComponentBody source)
    )

-- | Generic provider implementations may contain operation bodies. Their local
-- runtime binders may not hide declaration-static parameters; laws/lifecycle
-- propositions are not runtime term-binder regions and are deliberately absent.
grammarV1CheckedProviderImplementationGenericTermScope
  :: DeclarationKey
  -> GrammarV1ProviderImplementationDecl
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
grammarV1CheckedProviderImplementationGenericTermScope declarationKey source =
  checkedGenericTermScope
    declarationKey
    (grammarV1ProviderImplementationGenericParams source)
    (concatMap providerItemBinderSites (grammarV1ProviderImplementationItems source))

-- | Protocol send/receive parameters and select/offer branch payloads are runtime
-- session binders. They remain a separate identity domain from protocol generic
-- parameters but may not shadow an active declaration-static spelling.
grammarV1CheckedProtocolGenericTermScope
  :: DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
grammarV1CheckedProtocolGenericTermScope declarationKey source =
  checkedGenericTermScope
    declarationKey
    (grammarV1ProtocolGenericParams source)
    (concatMap roleBinderSites (grammarV1ProtocolRoles source))

checkedGenericTermScope
  :: DeclarationKey
  -> [Located GrammarV1GenericParam]
  -> [Located Text]
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
checkedGenericTermScope declarationKey genericParameters termSites = do
  (resolvedGenerics, genericScope) <- mapLeft
    GrammarV1GenericTermGenericBinderError
    ( grammarV1BindGenericParameters
        genericParameters
        (grammarV1RootGenericBinderScope declarationKey)
    )
  mapM_ (rejectStaticShadowing genericScope) termSites
  Right GrammarV1CheckedGenericTermScope
    { grammarV1CheckedGenericTermParameters = resolvedGenerics
    , grammarV1CheckedGenericTermBinderSites = termSites
    }

rejectStaticShadowing
  :: GrammarV1GenericBinderScope
  -> Located Text
  -> Either GrammarV1GenericTermScopeError ()
rejectStaticShadowing genericScope sourceName =
  case grammarV1ResolveGenericParameter sourceName genericScope of
    Right previous -> Left
      (GrammarV1GenericTermActiveStaticShadowing sourceName previous)
    Left (GrammarV1GenericBinderNotInScope _) -> Right ()
    Left other -> Left (GrammarV1GenericTermGenericBinderError other)

termParameterSites :: [Located GrammarV1TermParam] -> [Located Text]
termParameterSites = map (grammarV1TermParamName . locatedValue)

providerItemBinderSites :: Located GrammarV1ProviderImplementationItem -> [Located Text]
providerItemBinderSites (Located _ item) = case item of
  GrammarV1ProviderImplementationOperation _ _ body ->
    grammarV1TermBinderSitesInBlock body
  GrammarV1ProviderImplementationLaw {} -> []
  GrammarV1ProviderImplementationLifecycle {} -> []

roleBinderSites :: Located GrammarV1RoleSessionDecl -> [Located Text]
roleBinderSites (Located _ role) =
  sessionBinderSites (grammarV1RoleSessionExpression role)

sessionBinderSites :: Located GrammarV1SessionExpression -> [Located Text]
sessionBinderSites (Located _ source) = case source of
  GrammarV1SessionReference {} -> []
  GrammarV1SessionSend parameter _ _ continuation ->
    grammarV1TermParamName (locatedValue parameter) : sessionBinderSites continuation
  GrammarV1SessionReceive parameter _ _ continuation ->
    grammarV1TermParamName (locatedValue parameter) : sessionBinderSites continuation
  GrammarV1SessionSelect branches -> concatMap sessionBranchBinderSites branches
  GrammarV1SessionOffer branches -> concatMap sessionBranchBinderSites branches
  GrammarV1SessionEnd _ -> []
  GrammarV1SessionRecursive _ continuation -> sessionBinderSites continuation
  GrammarV1SessionContinue _ -> []

sessionBranchBinderSites :: Located GrammarV1SessionBranch -> [Located Text]
sessionBranchBinderSites (Located _ branch) =
  maybe [] termParameterSites (grammarV1SessionBranchParams branch)
    <> sessionBinderSites (grammarV1SessionBranchContinuation branch)

-- | Inventory every SURF-009 runtime binder site in one block, including nested
-- closures/control forms, in semantic-introduction order where that differs from
-- punctuation order (for example branch-local binders before post-join slots).
-- This function does not allocate term BinderKeys; it is the cross-domain gate
-- that prevents a static generic spelling from being hidden before the existing
-- per-family term-scope authority runs.
grammarV1TermBinderSitesInBlock :: Located GrammarV1Block -> [Located Text]
grammarV1TermBinderSitesInBlock (Located _ block) =
  concatMap statementBinderSites (grammarV1BlockStatements block)

statementBinderSites :: Located GrammarV1Statement -> [Located Text]
statementBinderSites (Located _ statement) = case statement of
  GrammarV1LetStatement patternSource initializer ->
    expressionBinderSites initializer <> patternBinderSites patternSource
  GrammarV1ReturnStatement expression -> expressionBinderSites expression
  GrammarV1ExpressionStatement expression -> expressionBinderSites expression

patternBinderSites :: Located GrammarV1Pattern -> [Located Text]
patternBinderSites (Located _ patternSource) = case patternSource of
  GrammarV1IdentifierPattern name -> [name]
  GrammarV1TuplePattern patterns -> concatMap patternBinderSites patterns
  GrammarV1RecordPattern _ fields -> concatMap fieldPatternBinderSites fields

fieldPatternBinderSites :: Located GrammarV1FieldPattern -> [Located Text]
fieldPatternBinderSites (Located _ field) =
  case grammarV1FieldPatternValue field of
    Nothing -> [grammarV1FieldPatternName field]
    Just nested -> patternBinderSites nested

casePatternBinderSites :: Located GrammarV1CasePattern -> [Located Text]
casePatternBinderSites (Located _ patternSource) =
  case grammarV1CasePatternBinders patternSource of
    Nothing -> []
    Just (GrammarV1TupleCaseBinders names) -> names
    Just (GrammarV1RecordCaseBinders fields) -> map fieldBinderName fields
  where
    fieldBinderName (Located _ field) =
      case grammarV1FieldBinderAlias field of
        Just alias -> alias
        Nothing -> grammarV1FieldBinderField field

matchArmBinderSites :: Located GrammarV1MatchArm -> [Located Text]
matchArmBinderSites (Located _ arm) =
  casePatternBinderSites (grammarV1MatchArmPattern arm)
    <> matchArmBodyBinderSites (grammarV1MatchArmBody arm)

matchArmBodyBinderSites :: GrammarV1MatchArmBody -> [Located Text]
matchArmBodyBinderSites body = case body of
  GrammarV1MatchArmBlock block -> grammarV1TermBinderSitesInBlock block
  GrammarV1MatchArmStatement statement -> statementBinderSites statement

joinBinderSites :: Maybe (Located GrammarV1JoinClause) -> [Located Text]
joinBinderSites Nothing = []
joinBinderSites (Just (Located _ joinClause)) =
  map (grammarV1StateSlotName . locatedValue) (grammarV1JoinState joinClause)

stateBindingSites :: [Located GrammarV1StateBinding] -> [Located Text]
stateBindingSites = concatMap stateBindingSite
  where
    stateBindingSite (Located _ binding) =
      expressionBinderSites (grammarV1StateBindingInitializer binding)
        <> [grammarV1StateBindingName binding]

branchValueBinderSites :: Located GrammarV1BranchValue -> [Located Text]
branchValueBinderSites (Located _ branchValue) =
  concatMap expressionBinderSites (grammarV1BranchValueArguments branchValue)

failureTargetBinderSites :: Located GrammarV1FailureTarget -> [Located Text]
failureTargetBinderSites (Located _ failureTarget) =
  concatMap expressionBinderSites (grammarV1FailureTargetArguments failureTarget)

fallbackBinderSites :: Located GrammarV1Fallback -> [Located Text]
fallbackBinderSites (Located _ fallback) = case fallback of
  GrammarV1FailFallback target -> failureTargetBinderSites target
  GrammarV1RejectFallback expression -> expressionBinderSites expression

expressionBinderSites :: Located GrammarV1Expression -> [Located Text]
expressionBinderSites (Located _ expression) = case expression of
  GrammarV1NameExpression _ arguments -> concatMap expressionBinderSites arguments
  GrammarV1BoolExpression _ -> []
  GrammarV1UnitExpression -> []
  GrammarV1IntegerExpression _ -> []
  GrammarV1ProjectionExpression receiver _ -> expressionBinderSites receiver
  GrammarV1BinaryExpression left _ right ->
    expressionBinderSites left <> expressionBinderSites right
  GrammarV1FallbackExpression primary fallback ->
    expressionBinderSites primary <> fallbackBinderSites fallback
  GrammarV1ConstructExpression _ fields ->
    concatMap (expressionBinderSites . snd) fields
  GrammarV1BorrowExpression owner viewName body ->
    expressionBinderSites owner
      <> [viewName]
      <> grammarV1TermBinderSitesInBlock body
  GrammarV1MatchExpression scrutinee joinClause arms ->
    expressionBinderSites scrutinee
      <> concatMap matchArmBinderSites arms
      <> joinBinderSites joinClause
  GrammarV1DecideExpression scrutinee arms ->
    expressionBinderSites scrutinee <> concatMap matchArmBinderSites arms
  GrammarV1BreakExpression actuals -> concatMap expressionBinderSites actuals
  GrammarV1ReceiveFrameExpression endpoint -> expressionBinderSites endpoint
  GrammarV1ReceiveExactExpression endpoint target maybeLength ->
    expressionBinderSites endpoint
      <> expressionBinderSites target
      <> maybe [] expressionBinderSites maybeLength
  GrammarV1ReceiveExpression _ endpoint -> expressionBinderSites endpoint
  GrammarV1RecognizeExpression _ input -> expressionBinderSites input
  GrammarV1ValidateExpression _ maybeContext subject ->
    maybe [] expressionBinderSites maybeContext <> expressionBinderSites subject
  GrammarV1SendExactExpression endpoint payload ->
    expressionBinderSites endpoint <> expressionBinderSites payload
  GrammarV1SendExpression endpoint payload ->
    expressionBinderSites endpoint <> expressionBinderSites payload
  GrammarV1SelectExpression branchValue endpoint maybeEvidence ->
    branchValueBinderSites branchValue
      <> expressionBinderSites endpoint
      <> maybe [] expressionBinderSites maybeEvidence
  GrammarV1CommitReceiveExpression endpoint value ->
    expressionBinderSites endpoint <> expressionBinderSites value
  GrammarV1FailExpression target resource ->
    failureTargetBinderSites target <> expressionBinderSites resource
  GrammarV1CloseExpression endpoint -> expressionBinderSites endpoint
  GrammarV1ReleaseExpression resource -> expressionBinderSites resource
  GrammarV1AcceptExpression value _ -> expressionBinderSites value
  GrammarV1ProveExpression _ -> []
  GrammarV1TransportExpression value _ evidence ->
    expressionBinderSites value <> expressionBinderSites evidence
  GrammarV1TupleExpression values -> concatMap expressionBinderSites values
  GrammarV1ParenthesizedExpression inner -> expressionBinderSites inner
  GrammarV1OfferExpression endpoint arms ->
    expressionBinderSites endpoint <> concatMap matchArmBinderSites arms
  GrammarV1IfExpression condition joinClause thenBlock maybeElse ->
    expressionBinderSites condition
      <> grammarV1TermBinderSitesInBlock thenBlock
      <> maybe [] grammarV1TermBinderSitesInBlock maybeElse
      <> joinBinderSites joinClause
  GrammarV1LoopExpression stateBindings _ body ->
    stateBindingSites stateBindings <> grammarV1TermBinderSitesInBlock body
  GrammarV1ContinueExpression actuals -> concatMap expressionBinderSites actuals
  GrammarV1ClosureExpression closure ->
    termParameterSites (grammarV1ClosureTermParams closure)
      <> grammarV1TermBinderSitesInBlock (grammarV1ClosureBody closure)
  GrammarV1RejectExpression value -> expressionBinderSites value

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
