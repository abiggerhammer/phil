{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.CallableRefinement (CallableAuthorityRequirement (..))
import Phil.Core.Effect
  ( CheckedSemanticEffect (..)
  , SemanticEffectCheckError (..)
  , SemanticEffectRelationRevision (..)
  , SemanticEffectSubjectKey (..)
  , checkedSemanticEffect
  , checkedSemanticEffectSubjectCorrespondence
  , retargetCheckedSemanticEffectSubject
  )
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  , grammarV1CallableParameterBinderScope
  )
import Phil.Surface.GrammarV1.CallableAuthority
  ( grammarV1CallableAuthorityBounds
  )
import Phil.Surface.GrammarV1.CallableCost
  ( GrammarV1CallableCostClause (..)
  , grammarV1CallableCostClauses
  )
import Phil.Surface.GrammarV1.CallableEffects
  ( GrammarV1CallableEffectBoundTemplate (..)
  , GrammarV1CallableEffectReferenceError (..)
  , GrammarV1CheckedSubjectIndexedEffect (..)
  , GrammarV1ResolvedCallableEffectUse (..)
  , GrammarV1ResolvedCallableEffectsParameter (..)
  , GrammarV1SubjectIndexedEffectError (..)
  , grammarV1CallableEffectBounds
  , grammarV1CheckedSubjectIndexedCallableEffectBounds
  , grammarV1CheckedSubjectIndexedSemanticEffect
  , grammarV1ResolvedCallableEffectBounds
  )
import Phil.Surface.GrammarV1.CallableResources
  ( GrammarV1CallableResourceClause (..)
  , GrammarV1CallableResourceDisposition (..)
  , grammarV1CallableResourceClauses
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticEffectSubjects
  ( GrammarV1ResolvedEffectSubjectError (..)
  , GrammarV1ResolvedExternalEffectSubject (..)
  , grammarV1CheckedResolvedSubjectCallableEffectBounds
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-002 callable/effects slice preserves all callable clauses" callableClausesPreserved
    , test "SURF-002 effect-set references remain distinct from literals" effectSetReferencePreserved
    , test "SURF-008 simple callable effect literals preserve exact Core identities"
        simpleEffectSemantics
    , test "SURF-008 resolved callable Effects references preserve stable parameter identity"
        resolvedEffectParameterSemantics
    , test "EFF-001 subject-indexed effects use exact semantic subjects"
        subjectIndexedEffectSemantics
    , test "EFF-002 effect subject retargeting requires exact checked correspondence"
        effectSubjectCorrespondenceSemantics
    , test "EFF-001 nonlocal effect subjects consume exact resolver evidence"
        externalEffectSubjectSemantics
    , test "SURF-008 simple callable authority types preserve exact Core identities"
        simpleAuthoritySemantics
    , test "SURF-008 callable consumes and borrows preserve exact unresolved resource intent"
        callableResourceSemantics
    , test "SURF-008 callable cost clauses preserve exact cost-model handoff intent"
        callableCostSemantics
    , test "SURF-002 effect-set trailing comma rejects at syntax" $
        expectReject "callable C() -> Unit { effects {IO,}; }"
    , test "SURF-002 name-set trailing comma rejects at syntax" $
        expectReject "callable C() -> Unit { consumes {x,}; }"
    , test "SURF-002 effects requirement requires within" $
        expectReject "callable C[E : Effects] requires { effects E {IO}; } () -> Unit {}"
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

callableClausesPreserved :: Either String ()
callableClausesPreserved = do
  callable <- onlyCallable fullCallableSource
  case grammarV1CallableRequirements callable of
    [Located _ (GrammarV1EffectsRequirement effectParam effectBound)] -> do
      assert (locatedValue effectParam == "E") "effects requirement parameter was not E"
      assertEffectLiteral ["IO", "Audit"] effectBound
    requirements -> Left ("expected one effects requirement, got " <> show requirements)
  case grammarV1CallableClauses callable of
    [ Located _ (GrammarV1CallableRequires requires)
      , Located _ (GrammarV1CallableConsumes consumes)
      , Located _ (GrammarV1CallableBorrows borrows)
      , Located _ (GrammarV1CallableAuthority authority)
      , Located _ (GrammarV1CallableEffects effects)
      , Located _ (GrammarV1CallableOutcomes outcomes)
      , Located _ (GrammarV1CallableOutcomeResidue residue)
      , Located _ (GrammarV1CallableEnsures ensures)
      , Located _ (GrammarV1CallableObligation obligation)
      , Located _ (GrammarV1CallableAssumes assumes)
      , Located _ (GrammarV1CallableCost cost)
      , Located _ (GrammarV1CallableCallee callee)
      ] -> do
        assertTrue requires
        assertQualifiedNames ["x", "store.slot"] consumes
        assertQualifiedNames ["loan"] borrows
        assertTypes ["Cap", "OtherCap"] authority
        assertEffectLiteralWithArguments effects
        assert (length outcomes == 1) "expected one callable outcome"
        case outcomes of
          [Located _ spec] -> do
            assert (locatedValue (grammarV1OutcomeSpecKind spec) == GrammarV1SuccessOutcome)
              "callable outcome kind was not success"
            assertNamedType "Unit" (grammarV1OutcomeSpecType spec)
          _ -> Left "internal one-outcome assertion mismatch"
        assert (locatedValue (grammarV1OutcomeResidueKind (locatedValue residue)) == GrammarV1SuccessOutcome)
          "outcome residue kind was not success"
        assertNamedType "Unit" (grammarV1OutcomeResidueType (locatedValue residue))
        assert (null (grammarV1OutcomeResidueClauses (locatedValue residue)))
          "empty outcome residue acquired clauses"
        assertTrue ensures
        assertTrue obligation
        assertTrue assumes
        assertInteger "7" cost
        assert (locatedValue callee == GrammarV1CalleePreserve)
          "callee transition was not preserve"
    clauses -> Left ("unexpected callable clauses " <> show clauses)

fullCallableSource :: Text.Text
fullCallableSource = Text.unlines
  [ "callable C[E : Effects] requires { effects E within {IO, Audit}; } (x : U32) -> Unit {"
  , "  requires true;"
  , "  consumes {x, store.slot};"
  , "  borrows {loan};"
  , "  authority {Cap, OtherCap};"
  , "  effects {IO, Audit(x)};"
  , "  outcomes {success Unit};"
  , "  outcome success Unit {}"
  , "  ensures true;"
  , "  obligation true;"
  , "  assumes true;"
  , "  cost 7;"
  , "  callee preserve;"
  , "}"
  ]

effectSetReferencePreserved :: Either String ()
effectSetReferencePreserved = do
  callable <- onlyCallable "callable C() -> Unit { effects E; }"
  case grammarV1CallableClauses callable of
    [Located _ (GrammarV1CallableEffects (Located _ effectSet))] ->
      case effectSet of
        GrammarV1EffectSetReference reference ->
          assertStaticReference "E" reference
        other -> Left ("expected effect-set reference, got " <> show other)
    clauses -> Left ("expected one effects clause, got " <> show clauses)

simpleEffectSemantics :: Either String ()
simpleEffectSemantics = do
  literal <- onlyCallable $ Text.unlines
    [ "callable EffectCarrier() -> Unit {"
    , "  effects {IO, pkg.Audit, IO};"
    , "  effects {};"
    , "}"
    ]
  assert
    (grammarV1CallableEffectBounds literal ==
      Just
        [ Set.fromList [SemanticEffect "IO", SemanticEffect "pkg.Audit"]
        , Set.empty
        ])
    "simple callable effect routing changed exact identity, clause order, or Set normalization"

  argumentBearing <- onlyCallable
    "callable ArgumentEffect(x : U8) -> Unit { effects {Audit(x)}; }"
  assert
    (grammarV1CallableEffectBounds argumentBearing == Nothing)
    "argument-bearing effect was flattened into a SemanticEffect identity"

  referenced <- onlyCallable
    "callable ReferencedEffects() -> Unit { effects E; }"
  assert
    (grammarV1CallableEffectBounds referenced == Nothing)
    "effect-set reference was treated as a concrete Core effect set"

resolvedEffectParameterSemantics :: Either String ()
resolvedEffectParameterSemantics = do
  callable <- onlyCallable $ Text.unlines
    [ "callable GenericEffects[E : Effects, T : Type]() -> Unit {"
    , "  effects E;"
    , "  effects {IO, IO};"
    , "  effects E;"
    , "}"
    ]
  sourceParameter <- case
      [ parameter
      | parameter@(Located _ genericParameter) <- grammarV1CallableGenericParams callable
      , locatedValue (grammarV1GenericParamKind genericParameter) == GrammarV1EffectsKind
      ] of
    [parameter] -> Right parameter
    parameters -> Left
      ("expected one Effects parameter, got " <> show (length parameters))
  effectClauses <- case
      [ effectSet
      | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses callable
      ] of
    [firstUse, literalUse, secondUse] -> Right (firstUse, literalUse, secondUse)
    clauses -> Left ("expected three effects clauses, got " <> show (length clauses))
  let (firstUse, literalUse, secondUse) = effectClauses
      parameterKey = GenericStaticParameterKey "callable.effects.parameter.E"
      parameterEvidence = GrammarV1ResolvedCallableEffectsParameter
        { resolvedCallableEffectsSourceParameter = sourceParameter
        , resolvedCallableEffectsParameter = GenericStaticParameter
            parameterKey
            GenericEffectsKind
        }
      use sourceUse = GrammarV1ResolvedCallableEffectUse
        { resolvedCallableEffectSourceUse = sourceUse
        , resolvedCallableEffectUseParameterKey = parameterKey
        }
      uses = [use firstUse, use secondUse]
      expected =
        [ GrammarV1CallableEffectsParameterBound parameterKey
        , GrammarV1ConcreteCallableEffectBound (Set.singleton (SemanticEffect "IO"))
        , GrammarV1CallableEffectsParameterBound parameterKey
        ]
  assert
    (grammarV1ResolvedCallableEffectBounds [parameterEvidence] uses callable
      == Just (Right expected))
    "resolved Effects parameter references did not preserve stable key and literal order"
  assert
    ( grammarV1ResolvedCallableEffectBounds
        [parameterEvidence]
        [use firstUse]
        callable
        == Just
          (Left (GrammarV1MissingCallableEffectUseEvidence secondUse))
    )
    "missing second Effects use evidence was not rejected explicitly"
  let wrongKindEvidence = parameterEvidence
        { resolvedCallableEffectsParameter = GenericStaticParameter
            parameterKey
            GenericTypeKind
        }
  assert
    ( grammarV1ResolvedCallableEffectBounds [wrongKindEvidence] uses callable
        == Just
          (Left
            (GrammarV1CallableEffectsParameterKindMismatch
              parameterKey
              GenericTypeKind))
    )
    "wrong-kind Effects parameter evidence was accepted"
  let foreignKey = GenericStaticParameterKey "callable.effects.parameter.foreign"
      foreignUse = GrammarV1ResolvedCallableEffectUse
        { resolvedCallableEffectSourceUse = firstUse
        , resolvedCallableEffectUseParameterKey = foreignKey
        }
  assert
    ( grammarV1ResolvedCallableEffectBounds
        [parameterEvidence]
        [foreignUse, use secondUse]
        callable
        == Just
          (Left (GrammarV1CallableEffectUseUndeclaredParameter foreignKey))
    )
    "foreign Effects parameter key was accepted at a callable effect use"
  let extraUse = GrammarV1ResolvedCallableEffectUse
        { resolvedCallableEffectSourceUse = literalUse
        , resolvedCallableEffectUseParameterKey = parameterKey
        }
  assert
    ( grammarV1ResolvedCallableEffectBounds
        [parameterEvidence]
        (uses <> [extraUse])
        callable
        == Just
          (Left (GrammarV1UnexpectedCallableEffectUseEvidence literalUse))
    )
    "extra Effects use evidence for a literal clause was silently ignored"

subjectIndexedEffectSemantics :: Either String ()
subjectIndexedEffectSemantics = do
  original <- onlyCallable $ Text.unlines
    [ "callable SubjectEffects(store : U8, peer : U8) -> Unit {"
    , "  effects {IO, Read(store), Read(peer), Read(store)};"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.EffectSubjectIdentity"
  (binders, lexicalScope) <- mapLeft show
    (grammarV1CallableParameterBinderScope declarationKey original)
  (effectSet, references) <- case
      grammarV1CheckedSubjectIndexedCallableEffectBounds lexicalScope original of
    Just (Right [checked]) -> Right checked
    other -> Left ("expected one checked subject-indexed effect set, got " <> show other)
  sourceEffects <- callableLiteralEffects original
  checkedEffects <- mapM (checkedEffect lexicalScope) sourceEffects
  case (binders, checkedEffects) of
    ( [storeBinder, peerBinder]
      , [ioEffect, readStore, readPeer, readStoreAgain]
      ) -> do
        let storeName = grammarV1ResolvedBinderCoreName storeBinder
            peerName = grammarV1ResolvedBinderCoreName peerBinder
            referenceNames = map
              ( grammarV1ResolvedBinderCoreName
                . grammarV1CheckedLexicalReferenceBinder
              )
              references
        assert
          (checkedSubjectIndexedEffectCore ioEffect == SemanticEffect "IO")
          "argument-free effect identity changed on the subject-indexed path"
        assert
          (checkedSubjectIndexedEffectCore readStore
            == checkedSubjectIndexedEffectCore readStoreAgain)
          "repeated use of the same exact subject changed effect identity"
        assert
          (checkedSubjectIndexedEffectCore readStore
            /= checkedSubjectIndexedEffectCore readPeer)
          "same effect label collapsed two distinct semantic subjects"
        assert (Set.size effectSet == 3)
          "subject-indexed Set did not preserve IO plus two distinct Read subjects"
        assert
          (referenceNames == [storeName, peerName, storeName])
          "effect subject evidence did not retain exact source-occurrence binder identity"
        assert
          ( all
              (/= SemanticEffect "Read")
              [ checkedSubjectIndexedEffectCore readStore
              , checkedSubjectIndexedEffectCore readPeer
              ]
          )
          "argument-bearing Read effect collapsed to its presentation label"
    other -> Left ("unexpected subject-indexed binder/effect shape: " <> show other)

  renamed <- onlyCallable $ Text.unlines
    [ "callable SubjectEffects(cell : U8, other : U8) -> Unit {"
    , "  effects {IO, Read(cell), Read(other), Read(cell)};"
    , "}"
    ]
  (renamedBinders, renamedScope) <- mapLeft show
    (grammarV1CallableParameterBinderScope declarationKey renamed)
  renamedBounds <- case
      grammarV1CheckedSubjectIndexedCallableEffectBounds renamedScope renamed of
    Just (Right checked) -> Right checked
    other -> Left ("expected alpha-renamed checked effect bounds, got " <> show other)
  assert
    ( map grammarV1ResolvedBinderCoreName binders
        == map grammarV1ResolvedBinderCoreName renamedBinders )
    "alpha-renaming changed callable subject Core identities"
  assert
    (map fst renamedBounds == [effectSet])
    "alpha-renaming changed subject-indexed semantic effect identity"

  unbound <- onlyCallable
    "callable UnboundEffect(store : U8) -> Unit { effects {Read(missing)}; }"
  (_, unboundScope) <- mapLeft show
    (grammarV1CallableParameterBinderScope
      (DeclarationKey "decl.UnboundEffectSubject")
      unbound)
  case grammarV1CheckedSubjectIndexedCallableEffectBounds unboundScope unbound of
    Just (Left (GrammarV1EffectSubjectNotLocal _)) -> Right ()
    other -> Left
      ("unbound source spelling was not rejected as a non-semantic effect subject: "
        <> show other)
  where
    checkedEffect scope source = case
        grammarV1CheckedSubjectIndexedSemanticEffect scope source of
      Just (Right checked) -> Right checked
      other -> Left ("expected checked subject-indexed effect, got " <> show other)

effectSubjectCorrespondenceSemantics :: Either String ()
effectSubjectCorrespondenceSemantics = do
  let storeA = SemanticEffectSubjectKey "semantic.subject.store-a"
      storeB = SemanticEffectSubjectKey "semantic.subject.store-b"
      peer = SemanticEffectSubjectKey "semantic.subject.peer"
  readA <- mapLeft show (checkedSemanticEffect ["Read"] [storeA])
  readB <- mapLeft show (checkedSemanticEffect ["Read"] [storeB])
  io <- mapLeft show (checkedSemanticEffect ["IO"] [])
  assert
    (checkedSemanticEffectCore io == SemanticEffect "IO")
    "Core subject checker changed the established zero-subject effect identity"
  assert
    (checkedSemanticEffectCore readA /= checkedSemanticEffectCore readB)
    "Core effect identity collapsed distinct exact semantic subject keys"
  same <- mapLeft show
    (retargetCheckedSemanticEffectSubject 0 storeA Nothing readA)
  assert (same == readA)
    "exact same-subject substitution unexpectedly required correspondence"
  case retargetCheckedSemanticEffectSubject 0 storeB Nothing readA of
    Left (SemanticEffectSubjectRetargetRequiresCorrespondence source target) -> do
      assert (source == storeA) "missing-correspondence error lost exact source subject"
      assert (target == storeB) "missing-correspondence error lost exact target subject"
    other -> Left
      ("cross-subject retargeting without correspondence was not rejected: " <> show other)
  relation <- mapLeft show
    (checkedSemanticEffectSubjectCorrespondence
      storeA storeB (SemanticEffectRelationRevision "relation.store-a-to-b.v1"))
  retargeted <- mapLeft show
    (retargetCheckedSemanticEffectSubject 0 storeB (Just relation) readA)
  assert
    (checkedSemanticEffectCore retargeted == checkedSemanticEffectCore readB)
    "accepted exact correspondence did not reconstruct the target semantic effect"
  wrongSource <- mapLeft show
    (checkedSemanticEffectSubjectCorrespondence
      peer storeB (SemanticEffectRelationRevision "relation.peer-to-b.v1"))
  case retargetCheckedSemanticEffectSubject 0 storeB (Just wrongSource) readA of
    Left (SemanticEffectSubjectCorrespondenceSourceMismatch expected actual) -> do
      assert (expected == storeA) "wrong-source error lost current exact subject"
      assert (actual == peer) "wrong-source error lost correspondence source"
    other -> Left
      ("mismatched-source correspondence was accepted: " <> show other)
  wrongTarget <- mapLeft show
    (checkedSemanticEffectSubjectCorrespondence
      storeA peer (SemanticEffectRelationRevision "relation.store-a-to-peer.v1"))
  case retargetCheckedSemanticEffectSubject 0 storeB (Just wrongTarget) readA of
    Left (SemanticEffectSubjectCorrespondenceTargetMismatch expected actual) -> do
      assert (expected == storeB) "wrong-target error lost requested target subject"
      assert (actual == peer) "wrong-target error lost correspondence target"
    other -> Left
      ("mismatched-target correspondence was accepted: " <> show other)
  assert
    ( checkedSemanticEffectSubjectCorrespondence
        storeA storeB (SemanticEffectRelationRevision "")
        == Left EmptySemanticEffectRelationRevision
    )
    "empty/fabricated correspondence revision was accepted"
  assert
    ( retargetCheckedSemanticEffectSubject 1 storeB Nothing readA
        == Left (SemanticEffectSubjectIndexOutOfRange 1)
    )
    "out-of-range effect subject retarget did not fail closed"

externalEffectSubjectSemantics :: Either String ()
externalEffectSubjectSemantics = do
  callable <- onlyCallable $ Text.unlines
    [ "callable ExternalSubjectEffects(local : U8) -> Unit {"
    , "  effects {Read(local), Read(pkg.store), Read(alias.store)};"
    , "}"
    ]
  (_, lexicalScope) <- mapLeft show
    (grammarV1CallableParameterBinderScope
      (DeclarationKey "decl.ExternalEffectSubjects")
      callable)
  effects <- callableLiteralEffects callable
  case effects of
    [localEffect, packageEffect, aliasEffect] -> do
      localArg <- oneEffectArgument localEffect
      packageArg <- oneEffectArgument packageEffect
      aliasArg <- oneEffectArgument aliasEffect
      let globalKey = SemanticEffectSubjectKey "semantic.subject.global-store"
          packageEvidence = GrammarV1ResolvedExternalEffectSubject
            packageArg globalKey
          aliasEvidence = GrammarV1ResolvedExternalEffectSubject
            aliasArg globalKey
          evidence = [packageEvidence, aliasEvidence]
      (effectSet, lexicalReferences, usedExternal) <- case
          grammarV1CheckedResolvedSubjectCallableEffectBounds
            lexicalScope evidence callable of
        Just (Right [checked]) -> Right checked
        other -> Left
          ("expected mixed local/external effect subjects, got " <> show other)
      assert (Set.size effectSet == 2)
        "different global spellings with one semantic key failed to collapse identity"
      assert (length lexicalReferences == 1)
        "local effect subject did not retain exactly one lexical witness"
      assert (usedExternal == evidence)
        "external effect subject evidence lost exact source occurrence order"
      case grammarV1CheckedResolvedSubjectCallableEffectBounds
          lexicalScope [packageEvidence] callable of
        Just (Left (GrammarV1MissingExternalEffectSubjectEvidence missing)) ->
          assert (missing == aliasArg)
            "missing external subject diagnostic did not name the exact occurrence"
        other -> Left
          ("missing external subject evidence was not rejected: " <> show other)
      case grammarV1CheckedResolvedSubjectCallableEffectBounds
          lexicalScope [packageEvidence, packageEvidence, aliasEvidence] callable of
        Just (Left (GrammarV1DuplicateExternalEffectSubjectEvidence duplicate)) ->
          assert (duplicate == packageArg)
            "duplicate external subject diagnostic lost exact source occurrence"
        other -> Left
          ("duplicate external subject evidence was not rejected: " <> show other)
      let strayLocalEvidence = GrammarV1ResolvedExternalEffectSubject
            localArg (SemanticEffectSubjectKey "semantic.subject.fake-local")
      case grammarV1CheckedResolvedSubjectCallableEffectBounds
          lexicalScope (evidence <> [strayLocalEvidence]) callable of
        Just (Left (GrammarV1UnexpectedExternalEffectSubjectEvidence stray)) ->
          assert (stray == localArg)
            "stray evidence rejection did not preserve lexical-precedence occurrence"
        other -> Left
          ("external evidence overrode or escaped an active lexical binder: " <> show other)
    other -> Left
      ("expected three source effects in external-subject fixture, got " <> show other)

oneEffectArgument
  :: Located GrammarV1EffectExpression
  -> Either String (Located GrammarV1Expression)
oneEffectArgument (Located _ effect) = case grammarV1EffectArguments effect of
  [argument] -> Right argument
  arguments -> Left ("expected exactly one effect argument, got " <> show arguments)

callableLiteralEffects
  :: GrammarV1CallableContractDecl
  -> Either String [Located GrammarV1EffectExpression]
callableLiteralEffects callable = case
    [ effectSet
    | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses callable
    ] of
  [Located _ (GrammarV1EffectSetLiteral effects)] -> Right effects
  other -> Left ("expected one literal effects clause, got " <> show other)

simpleAuthoritySemantics :: Either String ()
simpleAuthoritySemantics = do
  literal <- onlyCallable $ Text.unlines
    [ "callable AuthorityCarrier() -> Unit {"
    , "  authority {Cap, pkg.ReadCap, Cap};"
    , "  authority {};"
    , "}"
    ]
  assert
    (grammarV1CallableAuthorityBounds literal ==
      Just
        [ Set.fromList
            [ CallableAuthorityRequirement "Cap"
            , CallableAuthorityRequirement "pkg.ReadCap"
            ]
        , Set.empty
        ])
    "simple callable authority routing changed exact identity, clause order, or Set normalization"

  specialized <- onlyCallable
    "callable SpecializedAuthority() -> Unit { authority {Cap[U8]}; }"
  assert
    (grammarV1CallableAuthorityBounds specialized == Nothing)
    "specialized authority type was flattened into a textual authority identity"

  structured <- onlyCallable
    "callable StructuredAuthority() -> Unit { authority {(U8, Bool)}; }"
  assert
    (grammarV1CallableAuthorityBounds structured == Nothing)
    "structured authority type was flattened into a textual authority identity"

callableResourceSemantics :: Either String ()
callableResourceSemantics = do
  callable <- onlyCallable $ Text.unlines
    [ "callable ResourceCarrier() -> Unit {"
    , "  consumes {owner, store.slot, owner};"
    , "  borrows {loan};"
    , "  consumes {};"
    , "  borrows {pkg.shared, loan};"
    , "}"
    ]
  case grammarV1CallableResourceClauses callable of
    [ GrammarV1CallableResourceClause
        GrammarV1CallableConsumesResource firstConsumes
      , GrammarV1CallableResourceClause
        GrammarV1CallableBorrowsResource firstBorrows
      , GrammarV1CallableResourceClause
        GrammarV1CallableConsumesResource emptyConsumes
      , GrammarV1CallableResourceClause
        GrammarV1CallableBorrowsResource secondBorrows
      ] -> do
        assertQualifiedNames ["owner", "store.slot", "owner"] firstConsumes
        assertQualifiedNames ["loan"] firstBorrows
        assert (null emptyConsumes) "explicit empty consumes clause was not preserved"
        assertQualifiedNames ["pkg.shared", "loan"] secondBorrows
    clauses -> Left
      ("callable resource clauses lost category, grouping, or source order: "
        <> show clauses)

  empty <- onlyCallable "callable NoResources() -> Unit {}"
  assert
    (null (grammarV1CallableResourceClauses empty))
    "callable without resource clauses acquired implicit resource behavior"

  generic <- onlyCallable
    "callable GenericResource[T : Type](x : T) -> Unit { consumes {x}; }"
  case grammarV1CallableResourceClauses generic of
    [GrammarV1CallableResourceClause GrammarV1CallableConsumesResource names] ->
      assertQualifiedNames ["x"] names
    clauses -> Left
      ("generic callable resource intent was reinterpreted before binder resolution: "
        <> show clauses)

callableCostSemantics :: Either String ()
callableCostSemantics = do
  callable <- onlyCallable $ Text.unlines
    [ "callable CostCarrier[T : Type]() -> Unit {"
    , "  cost 7;"
    , "  cost model;"
    , "  cost 7;"
    , "}"
    ]
  case grammarV1CallableCostClauses callable of
    [ GrammarV1CallableCostClause firstCost
      , GrammarV1CallableCostClause modelCost
      , GrammarV1CallableCostClause secondCost
      ] -> do
        assertInteger "7" firstCost
        assertSimpleName "model" modelCost
        assertInteger "7" secondCost
        assert (firstCost /= secondCost)
          "duplicate cost expressions collapsed distinct source occurrences"
    clauses -> Left
      ("callable cost clauses lost exact source order or multiplicity: "
        <> show clauses)

  empty <- onlyCallable "callable NoCost() -> Unit {}"
  assert
    (null (grammarV1CallableCostClauses empty))
    "callable without cost clauses acquired implicit cost semantics"

assertEffectLiteral :: [Text.Text] -> Located GrammarV1EffectSetExpression -> Either String ()
assertEffectLiteral expected (Located _ effectSet) = case effectSet of
  GrammarV1EffectSetLiteral effects -> do
    assert (length effects == length expected) "unexpected effect-set literal arity"
    sequence_ (zipWith assertEffectName expected effects)
  other -> Left ("expected effect-set literal, got " <> show other)

assertEffectLiteralWithArguments :: Located GrammarV1EffectSetExpression -> Either String ()
assertEffectLiteralWithArguments (Located _ effectSet) = case effectSet of
  GrammarV1EffectSetLiteral
    [ Located _ firstEffect
      , Located _ secondEffect
      ] -> do
        assertStaticReference "IO" (grammarV1EffectReference firstEffect)
        assert (null (grammarV1EffectArguments firstEffect)) "IO effect unexpectedly had arguments"
        assertStaticReference "Audit" (grammarV1EffectReference secondEffect)
        case grammarV1EffectArguments secondEffect of
          [argument] -> assertSimpleName "x" argument
          arguments -> Left ("expected Audit(x), got " <> show arguments)
  other -> Left ("expected two-effect literal, got " <> show other)

assertEffectName :: Text.Text -> Located GrammarV1EffectExpression -> Either String ()
assertEffectName expected (Located _ effect) =
  assertStaticReference expected (grammarV1EffectReference effect)

assertQualifiedNames :: [Text.Text] -> [Located GrammarV1QualifiedName] -> Either String ()
assertQualifiedNames expected actual =
  assert
    (map (Text.intercalate "." . grammarV1QualifiedNameParts . locatedValue) actual == expected)
    ("unexpected qualified-name set " <> show actual)

assertTypes :: [Text.Text] -> [Located GrammarV1Type] -> Either String ()
assertTypes expected actual = do
  assert (length expected == length actual) "unexpected authority type-set arity"
  sequence_ (zipWith assertNamedType expected actual)

assertNamedType :: Text.Text -> Located GrammarV1Type -> Either String ()
assertNamedType expected (Located _ ty) = case ty of
  GrammarV1UnitType ->
    assert (expected == "Unit") ("expected named type " <> Text.unpack expected <> ", got Unit")
  GrammarV1NamedType reference -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected named type " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "named type unexpectedly had static arguments"
  other -> Left ("expected type " <> Text.unpack expected <> ", got " <> show other)

assertStaticReference :: Text.Text -> Located GrammarV1StaticReference -> Either String ()
assertStaticReference expected (Located _ reference) = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
    ("expected static reference " <> Text.unpack expected)
  assert (null (grammarV1StaticReferenceArguments reference))
    "static reference unexpectedly had static arguments"

assertTrue :: Located GrammarV1Proposition -> Either String ()
assertTrue proposition =
  assert (locatedValue proposition == GrammarV1TrueProposition)
    ("expected true proposition, got " <> show (locatedValue proposition))

assertInteger :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertInteger expected (Located _ expression) = case expression of
  GrammarV1IntegerExpression actual ->
    assert (actual == expected) ("expected integer " <> Text.unpack expected <> ", got " <> Text.unpack actual)
  other -> Left ("expected integer expression, got " <> show other)

assertSimpleName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleName expected (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments -> do
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected name " <> Text.unpack expected)
    assert (null (grammarV1StaticReferenceArguments reference))
      "simple name unexpectedly had static arguments"
    assert (null arguments) "simple name unexpectedly had term arguments"
  other -> Left ("expected simple name expression, got " <> show other)

onlyCallable :: Text.Text -> Either String GrammarV1CallableContractDecl
onlyCallable source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "callable-effects" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CallableContractDeclaration callable -> Right callable
      other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "callable-effects-reject" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
