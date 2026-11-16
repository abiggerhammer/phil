{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 J-6A: groundwork ONLY. This verifies actual parsed source lexical
-- identity, independent nominal Affine mode admission and a concrete Core
-- two-distinct-owner move/join/fresh-slot model. It does NOT invoke or extend
-- production Surface join-state typing. The J-6B Engine adapter is gated on
-- the separately owned P9 checker work.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (ReferencedGenericStaticActual)
  , GenericStaticKind (GenericTypeKind) )
import Phil.Core.NominalDataMode
  ( NominalModeError (..), NominalRestrictionJustification (..) )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), emptyStaticContext )
import Phil.Core.Syntax
  ( Mode (..), Name (..), RefTerm (..), Ty (..) )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  , grammarV1ResolveLocal )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..)
  , GrammarV1CheckedTypeModeResolutionError
  , GrammarV1ResolvedNamedTypeMode (..)
  , grammarV1CheckedTypeModeWithNamedResolutions )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataMode (..)
  , GrammarV1CheckedDataModeError (..)
  , grammarV1CheckedClosedDataMode )
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1CheckedIfBranch (..)
  , GrammarV1CheckedJoinClause (..)
  , GrammarV1CheckedJoinExpression (..)
  , GrammarV1CheckedJoinSlot (..)
  , GrammarV1JoinStateScopeError (..)
  , grammarV1CheckedJoinExpressionInScope )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..) )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1DataDecl (..)
  , GrammarV1Declaration (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1JoinClause (..)
  , GrammarV1Proposition (..), GrammarV1QualifiedName (..)
  , GrammarV1RelationOperator (..), GrammarV1StaticReference (..)
  , GrammarV1SourceFile (..), GrammarV1StateSlot (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..)
  , GrammarV1TopLevelDecl (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

dataRoot, fnRoot :: DeclarationKey
dataRoot = DeclarationKey "decl.fsem01.j6.Permit"
fnRoot = DeclarationKey "decl.fsem01.j6.choose"

revision :: InterfaceRevision
revision = InterfaceRevision "iface.fsem01.j6.Permit.v1"

permitTy, bytes8 :: Ty
permitTy = TyOpaque "Permit"
bytes8 = TyBytes (RefNat 8)

-- This is a CALLER-SUPPLIED ADMITTED lifecycle obligation, not a new
-- independently established right to discard the nominal Permit.
lifecycle :: Maybe NominalRestrictionJustification
lifecycle = Just (AdmittedLifecycleObligation
  "external reviewed lifecycle premise for nominal Permit")

data J6Error
  = J6NominalError GrammarV1CheckedDataModeError
  | J6TypeError GrammarV1CheckedTypeModeResolutionError
  | J6BinderError GrammarV1BinderScopeError
  | J6ScopeError GrammarV1JoinStateScopeError
  deriving (Eq, Show)

data J6Invariant = InvariantTrue | InvariantReflexive | InvariantUnproved
  deriving (Eq, Show)

data J6Admission = J6Admission
  { j6Flag :: GrammarV1ResolvedBinder
  , j6OwnerA :: GrammarV1ResolvedBinder
  , j6OwnerB :: GrammarV1ResolvedBinder
  , j6Payload :: GrammarV1ResolvedBinder
  , j6LeftActual :: GrammarV1ResolvedBinder
  , j6RightActual :: GrammarV1ResolvedBinder
  , j6Slot :: GrammarV1ResolvedBinder
  , j6Return :: GrammarV1ResolvedBinder
  , j6CheckedSlotMode :: CheckedTypeMode
  , j6CheckedNominalOrigin :: GrammarV1CheckedTypeModeOrigin
  , j6Invariant :: J6Invariant
  } deriving (Eq, Show)

same :: GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder -> Bool
same a b = grammarV1ResolvedBinderKey a == grammarV1ResolvedBinderKey b

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

assert :: Bool -> String -> Either String ()
assert passed why = if passed then Right () else Left why

directory :: FilePath
directory = "test/fixtures/fsem01-j6-two-affine-source-v1/"

parsePair :: Text -> Either String (GrammarV1DataDecl,GrammarV1FunctionDecl)
parsePair source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-j6a" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ dataTop,Located _ functionTop] ->
      case (locatedValue (grammarV1Declaration dataTop),
            locatedValue (grammarV1Declaration functionTop)) of
        (GrammarV1DataDeclaration dat,GrammarV1FunctionDeclaration fn) ->
          Right (dat,fn)
        _ -> Left "expected nominal Permit data declaration and one function"
    other -> Left ("expected two source declarations, found " ++ show (length other))

-- The only admission performed here is parser + lexical + nominal type/mode
-- resolution. NO claim is made that this is the production checked if-join.
sourceAdmission
  :: Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl -> GrammarV1FunctionDecl
  -> Maybe (Either J6Error J6Admission)
sourceAdmission admitted dat fn
  | grammarV1FunctionRecursive fn = Nothing
  | not (null (grammarV1FunctionGenericParams fn)) = Nothing
  | not (null (grammarV1FunctionRequirements fn)) = Nothing
  | otherwise = do
      [Located _ flagParam,Located _ aParam,
       Located _ bParam,Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams fn)
      resultSource <- grammarV1FunctionResultType fn
      dataMode <- grammarV1CheckedClosedDataMode emptyStaticContext admitted dat
      case dataMode of
        Left err -> Just (Left (J6NominalError err))
        Right mode
          | checkedDataStructuralMode mode /= Affine -> Nothing
          | otherwise -> do
              let dataName = locatedValue (grammarV1DataName dat)
                  nominal = TyOpaque dataName
                  reference = ReferencedGenericStaticActual dataName
                  named = GrammarV1ResolvedNamedTypeMode
                    { resolvedNamedTypeReference = reference
                    , resolvedNamedTypeKind = GenericTypeKind
                    , resolvedNamedTypeDeclarationKey = dataRoot
                    , resolvedNamedTypeInterfaceRevision = revision
                    , resolvedNamedTypeCheckedMode =
                        CheckedTypeMode nominal Affine }
                  origin = GrammarV1NamedTypeModeOrigin
                    reference dataRoot revision
                  checkType x = grammarV1CheckedTypeModeWithNamedResolutions
                    emptyStaticContext emptySurfaceState [named]
                    (locatedValue x)
                  types = mapM checkType
                    [grammarV1TermParamType flagParam,
                     grammarV1TermParamType aParam,
                     grammarV1TermParamType bParam,
                     grammarV1TermParamType payloadParam,resultSource]
              checkedTypes <- types
              case sequence checkedTypes of
                Left err -> Just (Left (J6TypeError err))
                Right [(flag,_),(a,_),(b,_),(payload,_),(result,_)]
                  | checkedResolvedTypeMode flag ==
                        CheckedTypeMode TyBool Unrestricted
                  , checkedResolvedTypeMode a ==
                        CheckedTypeMode nominal Affine
                  , checkedResolvedTypeMode b ==
                        CheckedTypeMode nominal Affine
                  , checkedResolvedTypeMode payload ==
                        CheckedTypeMode bytes8 Linear
                  , checkedResolvedTypeMode result ==
                        CheckedTypeMode bytes8 Linear
                  , checkedResolvedTypeModeOrigin a == origin
                  , checkedResolvedTypeModeOrigin b == origin ->
                      inspectBody named origin nominal
                _ -> Nothing
  where
    inspectBody named origin nominal = do
      [ Located _ (GrammarV1ExpressionStatement sourceIf)
        , Located _ (GrammarV1ReturnStatement sourceReturn) ] <-
          pure (grammarV1BlockStatements
            (locatedValue (grammarV1FunctionBody fn)))
      GrammarV1IfExpression _ (Just joinSource) _ (Just _) <-
        pure (locatedValue sourceIf)
      [locatedSlot] <- pure
        (grammarV1JoinState (locatedValue joinSource))
      slotChecked <- grammarV1CheckedTypeModeWithNamedResolutions
        emptyStaticContext emptySurfaceState [named]
        (locatedValue
          (grammarV1StateSlotType (locatedValue locatedSlot)))
      case slotChecked of
        Left err -> Just (Left (J6TypeError err))
        Right (resolvedSlot,_)
          | checkedResolvedTypeMode resolvedSlot /=
                CheckedTypeMode nominal Affine
            || checkedResolvedTypeModeOrigin resolvedSlot /= origin -> Nothing
          | otherwise ->
            case grammarV1FunctionParameterScope fnRoot fn of
              Left err -> Just (Left (J6BinderError err))
              Right ([flag,a,b,payload],initialScope) -> do
                checked <- grammarV1CheckedJoinExpressionInScope
                  initialScope sourceIf
                case checked of
                  Left err -> Just (Left (J6ScopeError err))
                  Right (GrammarV1CheckedIfJoinExpression condition
                          left (Just right) joinClause, successorScope) -> do
                    if not (same
                        (grammarV1CheckedLocalValueBinder condition) flag)
                      then Nothing
                      else do
                        [slot] <- pure (grammarV1CheckedJoinSlots joinClause)
                        let selected = grammarV1CheckedJoinSlotBinder slot
                        if not (null (grammarV1CheckedJoinSlotTypeReferences slot))
                          then Nothing
                          else do
                            leftActual <- branchActual left a b
                            rightActual <- branchActual right a b
                            if same leftActual rightActual
                              then Nothing
                              else do
                                returned <-
                                  grammarV1CheckedLocalValueOccurrenceInScope
                                    successorScope sourceReturn
                                if not (same
                                    (grammarV1CheckedLocalValueBinder returned)
                                    payload)
                                  then Nothing
                                  else do
                                    proof <- invariantClass successorScope
                                      selected joinSource
                                      (grammarV1CheckedJoinInvariantReferences joinClause)
                                    Just (Right J6Admission
                                      { j6Flag = flag
                                      , j6OwnerA = a
                                      , j6OwnerB = b
                                      , j6Payload = payload
                                      , j6LeftActual = leftActual
                                      , j6RightActual = rightActual
                                      , j6Slot = selected
                                      , j6Return =
                                          grammarV1CheckedLocalValueBinder returned
                                      , j6CheckedSlotMode =
                                          checkedResolvedTypeMode resolvedSlot
                                      , j6CheckedNominalOrigin = origin
                                      , j6Invariant = proof })
                  Right _ -> Nothing
              Right _ -> Nothing

    branchActual branch a b = do
      [GrammarV1CheckedLetOccurrenceStep
        (Located _ (GrammarV1ExpressionStatement _)) occurrence] <-
          pure (grammarV1CheckedIfBranchSteps branch)
      let checkedBinder = grammarV1CheckedLocalValueBinder occurrence
      case filter (same checkedBinder) [a,b] of
        [one] -> Just one
        _ -> Nothing

    invariantClass scope selected joinSource references = do
      source <- grammarV1JoinInvariant (locatedValue joinSource)
      case locatedValue source of
        GrammarV1TrueProposition
          | null references -> Just InvariantTrue
        GrammarV1FalseProposition
          | null references -> Just InvariantUnproved
        GrammarV1RelationProposition lhs (Located _ GrammarV1EqualRelation) rhs -> do
          left <- grammarV1CheckedLocalValueOccurrenceInScope scope lhs
          right <- grammarV1CheckedLocalValueOccurrenceInScope scope rhs
          if same (grammarV1CheckedLocalValueBinder left) selected &&
             same (grammarV1CheckedLocalValueBinder right) selected
            then Just InvariantReflexive
            else Just InvariantUnproved
        _ -> Nothing

admitText :: Maybe NominalRestrictionJustification -> Text
  -> Maybe (Either J6Error J6Admission)
admitText admitted source = do
  (dat,fn) <- either (const Nothing) Just (parsePair source)
  sourceAdmission admitted dat fn

expectAdmitted :: Text -> J6Invariant -> Bool -> Either String ()
expectAdmitted source expectedInvariant swapped = do
  (dat,fn) <- parsePair source
  evidence <- case sourceAdmission lifecycle dat fn of
    Just (Right valid) -> Right valid
    other -> Left ("real source nominal/lexical admission failed: " ++ show other)
  let ns = map name [j6Flag evidence,j6OwnerA evidence,
            j6OwnerB evidence,j6Payload evidence,j6Slot evidence]
      firstOwner = if swapped then j6OwnerB evidence else j6OwnerA evidence
      secondOwner = if swapped then j6OwnerA evidence else j6OwnerB evidence
      expectedOrigin = GrammarV1NamedTypeModeOrigin
        (ReferencedGenericStaticActual "Permit") dataRoot revision
  assert (Set.size (Set.fromList ns) == 5 &&
          not (same (j6OwnerA evidence) (j6OwnerB evidence)) &&
          same (j6LeftActual evidence) firstOwner &&
          same (j6RightActual evidence) secondOwner &&
          same (j6Return evidence) (j6Payload evidence) &&
          j6CheckedSlotMode evidence == CheckedTypeMode permitTy Affine &&
          j6CheckedNominalOrigin evidence == expectedOrigin &&
          j6Invariant evidence == expectedInvariant)
    "checked source-rooted names, two different branch owners or nominal mode changed"
  assert (grammarV1ResolvedBinderDisplayName (j6Slot evidence) == "selected")
    "post-join slot lexical binder unexpectedly changed"
  -- The Core result is an independent model computed from THESE exact
  -- source-derived names; no production source join is claimed at J-6A.
  checkNativeTwoOwnerMove evidence

checkNativeTwoOwnerMove :: J6Admission -> Either String ()
checkNativeTwoOwnerMove evidence = do
  let flag = name (j6Flag evidence)
      a = name (j6OwnerA evidence)
      b = name (j6OwnerB evidence)
      selected = name (j6Slot evidence)
      payload = name (j6Payload evidence)
      firstName = name (j6LeftActual evidence)
      secondName = name (j6RightActual evidence)
      start = Core.ResourceContext
        { Core.unrestrictedBindings = Map.singleton flag TyBool
        , Core.affineBindings = Map.fromList [(a,permitTy),(b,permitTy)]
        , Core.linearBindings = Map.singleton payload bytes8
        , Core.sharedLoans = Set.empty }
  (leftTy,left) <- either (Left . show) Right
    (Core.consumeAffine firstName start)
  (rightTy,right) <- either (Left . show) Right
    (Core.consumeAffine secondName start)
  assert (leftTy == permitTy && rightTy == permitTy &&
          Core.affineBindings left == Map.singleton secondName permitTy &&
          Core.affineBindings right == Map.singleton firstName permitTy &&
          left /= right)
    "distinct source owner moves did not create asymmetric native affine maps"
  joined <- either (Left . show) Right (Core.joinContinuing [left,right])
  assert (Core.affineBindings joined == Map.empty &&
          Core.unrestrictedBindings joined == Core.unrestrictedBindings start &&
          Core.linearBindings joined == Core.linearBindings start &&
          Core.sharedLoans joined == Set.empty)
    "native affine intersection resurrected a source owner or lost a spectator"
  bound <- either (Left . show) Right
    (Core.insertBinding Affine selected permitTy joined)
  assert (Core.affineBindings bound == Map.singleton selected permitTy &&
          Core.consumeAffine firstName bound == Left (Core.UnknownBinding firstName) &&
          Core.consumeAffine secondName bound == Left (Core.UnknownBinding secondName) &&
          Core.insertBinding Affine selected permitTy bound ==
            Left (Core.DuplicateBinding selected) &&
          Core.consumeAffine selected bound == Right (permitTy, joined))
    "new affine result slot duplicated or original source owner resurrected"
  (returnedTy,afterReturn) <- either (Left . show) Right
    (Core.consumeLinear payload bound)
  assert (returnedTy == bytes8 &&
          Core.ensureComplete afterReturn == Right () &&
          Core.sharedLoans afterReturn == Set.empty)
    "independent linear spectator return or affine completion failed"
  borrowed <- either (Left . show) Right (Core.startSharedLoan firstName start)
  borrowedRight <- either (Left . show) Right
    (Core.startSharedLoan firstName right)
  assert (Core.consumeAffine firstName borrowed ==
            Left (Core.OwnerBorrowed firstName) &&
          Core.joinContinuing [left,borrowedRight] ==
            Left (Core.EscapingLoans (Set.singleton firstName)) &&
          Core.joinContinuing
            [left,right { Core.linearBindings = Map.empty }] ==
            Left (Core.LinearBranchMismatch
              (Core.linearBindings left) Map.empty) &&
          Core.joinContinuing
            [left { Core.unrestrictedBindings = Map.empty },right] ==
            Left (Core.UnrestrictedBranchMismatch
              Map.empty (Core.unrestrictedBindings right)))
    "core loan, linear or unrestricted mismatch was silently accepted"

expectOutside :: Text -> String -> Either String ()
expectOutside source why = do
  _ <- parsePair source
  assert (admitText lifecycle source == Nothing)
    ("out-of-fragment shape improperly admitted: " ++ why)

expectNominalRejections :: Text -> Text -> Either String ()
expectNominalRejections positive badPayload = do
  _ <- parsePair positive
  let noLifecycle = admitText Nothing positive
      unadmitted = admitText
        (Just (UnadmittedNominalRestriction "not independently admitted"))
        positive
      badMode = admitText lifecycle badPayload
  assert (noLifecycle == Just (Left (J6NominalError
    (GrammarV1DataModeNominalError
      (StrongerModeMissingJustification Unrestricted Affine)))))
    ("absent external lifecycle admission was accepted: " ++ show noLifecycle)
  assert (unadmitted == Just (Left (J6NominalError
    (GrammarV1DataModeNominalError
      (StrongerModeUnadmittedJustification "not independently admitted")))))
    "unadmitted nominal lifecycle premise became a checked mode"
  assert (badMode == Just (Left (J6NominalError
    (GrammarV1DataModeNominalError
      (DeclaredModeWeakensDerived Linear Affine)))))
    ("source illegally weakened a Linear data payload: " ++ show badMode)

expectScopeFailure :: Text -> String -> Either String ()
expectScopeFailure source why = do
  _ <- parsePair source
  case admitText lifecycle source of
    Just (Left (J6ScopeError _)) -> Right ()
    other -> Left ("scope failure bypassed: " ++ why ++ " => " ++ show other)

-- A source predecessor using a POST-join state-slot spelling is not a
-- resolvable parameter-local occurrence. The shared bounded lexical checker
-- therefore returns Nothing (outside competence), not a typed ScopeError:
-- such a name may also be a static/global reference in general Grammar-v1.
-- Check the real source AST, the precise pre-join lexical absence and the
-- independent checker's actual refusal; never manufacture a production error.
expectForwardSlotRefusal :: Text -> Either String ()
expectForwardSlotRefusal source = do
  (_,fn) <- parsePair source
  (_,preJoin) <- either (Left . show) Right
    (grammarV1FunctionParameterScope fnRoot fn)
  sourceIf <- case grammarV1BlockStatements
      (locatedValue (grammarV1FunctionBody fn)) of
    [Located _ (GrammarV1ExpressionStatement sourceIf),_] -> Right sourceIf
    _ -> Left "forward-ref negative lost its one-if source-body shape"
  (predecessor,slotName) <- case locatedValue sourceIf of
    GrammarV1IfExpression _ (Just joinClause) left (Just _) ->
      case (grammarV1JoinState (locatedValue joinClause),
            grammarV1BlockStatements (locatedValue left)) of
        ([Located _ slot],[Located _ (GrammarV1ExpressionStatement value)]) ->
          Right (value,grammarV1StateSlotName slot)
        _ -> Left "forward-ref negative lost its source slot or predecessor"
    _ -> Left "forward-ref negative lost its declared if/join"
  let isExactlyFutureSlot = case locatedValue predecessor of
        GrammarV1NameExpression reference args ->
          null args &&
          null (grammarV1StaticReferenceArguments reference) &&
          grammarV1QualifiedNameParts
            (grammarV1StaticReferenceName reference) == [locatedValue slotName]
        _ -> False
  assert isExactlyFutureSlot
    "forward-ref negative no longer refers to its own future join slot"
  case grammarV1ResolveLocal slotName preJoin of
    Left (GrammarV1BinderNotInScope _) -> Right ()
    other -> Left ("post-join state slot unexpectedly visible before join: " ++
                   show other)
  assert (grammarV1CheckedLocalValueOccurrenceInScope preJoin predecessor == Nothing &&
          grammarV1CheckedJoinExpressionInScope preJoin sourceIf == Nothing &&
          admitText lifecycle source == Nothing)
    "unavailable post-join slot incorrectly acquired pre-join local authority"

main :: IO ()
main = do
  let fixture name' = TextIO.readFile (directory ++ name' ++ ".phil")
  positive <- fixture "accepted-distinct-owners"
  reflexive <- fixture "accepted-reflexive"
  swapped <- fixture "accepted-swapped-arms"
  unproved <- fixture "unproved-false"
  shadow <- fixture "shadow-parameter"
  future <- fixture "future-slot-reference"
  weakened <- fixture "wrong-permit-payload-mode"
  unsupported <- mapM fixture
    [ "same-source-owner","wrong-then-bool","wrong-else-bool"
    , "wrong-slot-bool","missing-invariant","missing-else"
    , "two-state-slots","wrong-return-owner","wrong-result-width"
    , "wrong-condition","wrong-permit-declaration-mode" ]
  let result = do
        expectAdmitted positive InvariantTrue False
        expectAdmitted reflexive InvariantReflexive False
        expectAdmitted swapped InvariantTrue True
        -- Only the source logical proof shape is classified here. This is
        -- NOT an Engine MissingEvidence check or a source-validity theorem.
        evidence <- case admitText lifecycle unproved of
          Just (Right valid) -> Right valid
          other -> Left ("false invariant lexical class not observed: " ++ show other)
        assert (j6Invariant evidence == InvariantUnproved)
          "false invariant was accidentally given a proof"
        checkNativeTwoOwnerMove evidence
        expectNominalRejections positive weakened
        expectScopeFailure shadow "join state shadows existing parameter"
        expectForwardSlotRefusal future
        mapM_ (uncurry expectOutside) (zip unsupported
          [ "both arms move the same source owner"
          , "then arm Bool is not Affine Permit"
          , "else arm Bool is not Affine Permit"
          , "Bool state slot is not Permit"
          , "missing invariant proof form"
          , "one-arm source shape"
          , "more than one join-state slot"
          , "return is wrong source owner"
          , "declared Linear result width mismatch"
          , "non-Bool condition source binder"
          , "Permit declaration has no checked affine mode" ])
        assert (Text.replace "  } else {\n    permitB;"
                   "  } else {\n    permitA;" positive ==
                head unsupported)
          "same-owner negative differs by more than one source operand"
  case result of
    Left err -> putStrLn ("FAIL J-6A: " ++ err) >> exitFailure
    Right () -> putStrLn
      "PASS J-6A: 18 parsed source nominal/lexical fixtures, exact two-owner identity and native Affine move/join/slot adversaries; production Surface join-state integration remains open"
