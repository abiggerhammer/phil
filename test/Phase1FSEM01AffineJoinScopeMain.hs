{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: checked nominal affine owners, real production scope pruning,
-- continuing join intersection and exact linear branch-local rejection.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.NominalDataMode
  ( NominalModeError (..), NominalRestrictionJustification (..) )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), emptyStaticContext )
import Phil.Core.Syntax (Control (..), Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine (SourceScopedIfJoinRun (..))
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.CheckedType (GrammarV1CheckedTypeModeOrigin (..))
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataModeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl, GrammarV1FunctionDecl
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..), parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceAffineIfJoinResource
  ( GrammarV1AffineIfJoinError (..)
  , GrammarV1AffineIfJoinTrace (..)
  , grammarV1CheckedAffineIfJoinTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

dataRoot, functionRoot :: DeclarationKey
dataRoot = DeclarationKey "decl.fsem01.join.Permit"
functionRoot = DeclarationKey "decl.fsem01.join.choose"

revision :: InterfaceRevision
revision = InterfaceRevision "iface.fsem01.join.v1"

lifecycle :: Maybe NominalRestrictionJustification
lifecycle = Just (AdmittedLifecycleObligation
  "external independently reviewed permission to abandon Permit")

permitTy, bytes8 :: Ty
permitTy = TyOpaque "Permit"
bytes8 = TyBytes (RefNat 8)

directory :: FilePath
directory = "test/fixtures/fsem01-affine-join-scope-v1/"

assert :: Bool -> String -> Either String ()
assert yes why = if yes then Right () else Left why

parsePair :: Text -> Either String (GrammarV1DataDecl, GrammarV1FunctionDecl)
parsePair source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "source-affine-join-scope" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ dataTop, Located _ fnTop] ->
      case ( locatedValue (grammarV1Declaration dataTop)
           , locatedValue (grammarV1Declaration fnTop)) of
        (GrammarV1DataDeclaration dat, GrammarV1FunctionDeclaration fn) ->
          Right (dat, fn)
        other -> Left ("not nominal data + function: " ++ show other)
    other -> Left ("expected exactly two declarations, got " ++ show (length other))

check
  :: Maybe NominalRestrictionJustification
  -> Text
  -> Maybe (Either GrammarV1AffineIfJoinError GrammarV1AffineIfJoinTrace)
check attestation source =
  case parsePair source of
    Left _ -> Nothing
    Right (dat, fn) ->
      grammarV1CheckedAffineIfJoinTrace
        emptyStaticContext dataRoot revision attestation dat functionRoot fn

checked :: Text -> Either String GrammarV1AffineIfJoinTrace
checked source = do
  (dat, fn) <- parsePair source
  case grammarV1CheckedAffineIfJoinTrace
      emptyStaticContext dataRoot revision lifecycle dat functionRoot fn of
    Just (Right record) -> Right record
    other -> Left ("no admitted source if/join: " ++ show other)

flagName, permitName, payloadName :: GrammarV1AffineIfJoinTrace -> Name
flagName = grammarV1ResolvedBinderCoreName . affineIfJoinFlagBinder
permitName = grammarV1ResolvedBinderCoreName . affineIfJoinPermitBinder
payloadName = grammarV1ResolvedBinderCoreName . affineIfJoinPayloadBinder

initial :: GrammarV1AffineIfJoinTrace -> Core.ResourceContext
initial t = Core.ResourceContext
  { Core.unrestrictedBindings = Map.singleton (flagName t) TyBool
  , Core.affineBindings = Map.singleton (permitName t) permitTy
  , Core.linearBindings = Map.singleton (payloadName t) bytes8
  , Core.sharedLoans = Set.empty }

baseChecks :: GrammarV1AffineIfJoinTrace -> Either String SourceScopedIfJoinRun
baseChecks t = do
  let run = affineIfJoinRun t
      before = initial t
      names = [flagName t, permitName t, payloadName t]
  assert (length (Set.fromList names) == 3)
    "source parameter ordinals collapsed distinct semantic identities"
  assert (affineIfJoinDataKey t == dataRoot &&
          affineIfJoinInterfaceRevision t == revision)
    "source declaration key/interface revision lost"
  assert (affineIfJoinPermitMode t == CheckedTypeMode permitTy Affine &&
          affineIfJoinPayloadMode t == CheckedTypeMode bytes8 Linear &&
          affineIfJoinPermitOrigin t ==
            GrammarV1NamedTypeModeOrigin
              (ReferencedGenericStaticActual "Permit") dataRoot revision)
    "source checked nominal affine provenance/mode or linear mode is wrong"
  assert (scopedIfJoinBefore run == Just before &&
          scopedIfJoinOutcome run == affineIfJoinOutcome t)
    "initial native state or independent ordinary/traced outcome mismatch"
  let observed = scopedIfJoinThenRaw run ++ scopedIfJoinThenPruned run ++
        scopedIfJoinElseRaw run ++ scopedIfJoinElsePruned run
  assert (all (\c -> Core.sharedLoans c == Set.empty &&
          Core.linearBindings c == Map.singleton (payloadName t) bytes8 ||
          Core.sharedLoans c == Set.empty &&
          Map.size (Core.linearBindings c) == 1) observed)
    "unrecognized loan/linear resource state in branch trace"
  Right run

expectReturned :: GrammarV1AffineIfJoinTrace -> Either String ()
expectReturned t = assert
  (affineIfJoinOutcome t ==
    Right (SurfaceCheckResult "choose" [Return bytes8]))
  ("actual production return was not exact linear Bytes: " ++
    show (affineIfJoinOutcome t))

checkAsymmetric :: Text -> Either String ()
checkAsymmetric source = do
  t <- checked source
  run <- baseChecks t
  spare <- case affineIfJoinLocalBinders t of
    [one] -> Right (grammarV1ResolvedBinderCoreName one)
    _ -> Left "expected one exact branch-local affine binder"
  let before = initial t
      thenRaw = before { Core.affineBindings = Map.singleton spare permitTy }
      thenClean = before { Core.affineBindings = Map.empty }
  assert (spare /= permitName t && spare /= payloadName t &&
          scopedIfJoinThenRaw run == [thenRaw] &&
          scopedIfJoinThenPruned run == [thenClean] &&
          scopedIfJoinElseRaw run == [before] &&
          scopedIfJoinElsePruned run == [before] &&
          scopedIfJoinJoined run == Just thenClean)
    "affine move/prune/join did not produce the exact observed four-zone maps"
  assert (Core.joinContinuing [thenClean,before] == Right thenClean)
    "native Core affine intersection did not match the real source contexts"
  assert (Core.consumeAffine (permitName t) thenClean ==
          Left (Core.UnknownBinding (permitName t)))
    "an affine owner consumed in one branch was silently resurrected"
  expectReturned t

checkRetained :: Text -> Either String ()
checkRetained source = do
  t <- checked source
  run <- baseChecks t
  let before = initial t
  assert (null (affineIfJoinLocalBinders t) &&
          scopedIfJoinThenRaw run == [before] &&
          scopedIfJoinThenPruned run == [before] &&
          scopedIfJoinElseRaw run == [before] &&
          scopedIfJoinElsePruned run == [before] &&
          scopedIfJoinJoined run == Just before)
    "two unchanged affine predecessors did not retain owner at join"
  assert (Core.joinContinuing [before,before] == Right before)
    "native Core join changed a shared affine owner"
  expectReturned t

checkBothLocals :: Text -> Either String ()
checkBothLocals source = do
  t <- checked source
  run <- baseChecks t
  case affineIfJoinLocalBinders t of
    [a,b] -> do
      let leftName = grammarV1ResolvedBinderCoreName a
          rightName = grammarV1ResolvedBinderCoreName b
          before = initial t
          after = before { Core.affineBindings = Map.empty }
      assert (grammarV1ResolvedBinderDisplayName a == "spare" &&
              grammarV1ResolvedBinderDisplayName b == "spare" &&
              leftName /= rightName &&
              leftName /= permitName t &&
              rightName /= permitName t)
        "same-spelling sibling affine locals did not receive distinct Core names"
      assert (scopedIfJoinThenRaw run ==
                [before { Core.affineBindings = Map.singleton leftName permitTy }] &&
              scopedIfJoinElseRaw run ==
                [before { Core.affineBindings = Map.singleton rightName permitTy }] &&
              scopedIfJoinThenPruned run == [after] &&
              scopedIfJoinElsePruned run == [after] &&
              scopedIfJoinJoined run == Just after)
        "branch-local affine resources escaped or were conflated at join"
      expectReturned t
    _ -> Left "expected two independent source-local affine binders"

checkUnrestrictedLocal :: Text -> Either String ()
checkUnrestrictedLocal source = do
  t <- checked source
  run <- baseChecks t
  scratch <- case affineIfJoinLocalBinders t of
    [one] -> Right (grammarV1ResolvedBinderCoreName one)
    _ -> Left "expected one unrestricted local binding"
  let before = initial t
      raw = before { Core.unrestrictedBindings =
        Map.insert scratch TyBool (Core.unrestrictedBindings before) }
  assert (scopedIfJoinThenRaw run == [raw] &&
          scopedIfJoinThenPruned run == [before] &&
          scopedIfJoinElseRaw run == [before] &&
          scopedIfJoinElsePruned run == [before] &&
          scopedIfJoinJoined run == Just before)
    "branch-local unrestricted binder was not pruned before the join"
  expectReturned t

checkLinearLeak :: Text -> Either String ()
checkLinearLeak source = do
  t <- checked source
  run <- baseChecks t
  scratch <- case affineIfJoinLocalBinders t of
    [one] -> Right (grammarV1ResolvedBinderCoreName one)
    _ -> Left "expected one live linear branch-local"
  let before = initial t
      raw = before { Core.linearBindings = Map.singleton scratch bytes8 }
  assert (scopedIfJoinThenRaw run == [raw] &&
          null (scopedIfJoinThenPruned run) &&
          null (scopedIfJoinElseRaw run) &&
          null (scopedIfJoinElsePruned run) &&
          scopedIfJoinJoined run == Nothing)
    "failed local linear cleanup fabricated a prune/join successor"
  case affineIfJoinOutcome t of
    Left err -> assert
      (surfaceErrorClass err == LinearCompletion &&
       surfaceErrorDetail err ==
         "linear branch-local binding remains live: " <> unName scratch)
      ("wrong exact native scoped-linear error: " ++ show err)
    Right _ -> Left "live branch-local Linear Bytes was silently discarded"

checkStaleAfterJoin :: Text -> Either String ()
checkStaleAfterJoin source = do
  t <- checked source
  run <- baseChecks t
  let before = initial t
      joined = before { Core.affineBindings = Map.empty }
  assert (scopedIfJoinJoined run == Just joined)
    "post-join stale-affine negative never reached the actual join"
  case affineIfJoinOutcome t of
    Left err -> assert
      (surfaceErrorClass err == StructuralUse &&
       surfaceErrorDetail err ==
         "unknown or consumed binding: " <> unName (permitName t))
      ("wrong exact stale affine source error: " ++ show err)
    Right _ -> Left "affine owner absent in one predecessor was resurrected"

checkNominalRejections :: Text -> Text -> Text -> Either String ()
checkNominalRejections missing unadmitted weakened = do
  let noJust = check Nothing missing
      unadmittedClaim = check
        (Just (UnadmittedNominalRestriction "text is not admitted")) unadmitted
      wrongMode = check Nothing weakened
  assert (noJust == Just (Left (AffineIfJoinNominalError
    (GrammarV1DataModeNominalError
      (StrongerModeMissingJustification Unrestricted Affine)))))
    ("source spelling silently admitted affine mode: " ++ show noJust)
  assert (unadmittedClaim == Just (Left (AffineIfJoinNominalError
    (GrammarV1DataModeNominalError
      (StrongerModeUnadmittedJustification "text is not admitted")))))
    "unadmitted external lifecycle text became affine authority"
  assert (wrongMode == Just (Left (AffineIfJoinNominalError
    (GrammarV1DataModeNominalError
      (DeclaredModeWeakensDerived Linear Unrestricted)))))
    "declared unrestricted mode illegally weakened a linear data payload"

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source label = do
  _ <- parsePair source
  assert (check lifecycle source == Nothing)
    ("unsupported source shape was not rejected by bounded adapter: " ++ label)

main :: IO ()
main = do
  let fixture name =
        TextIO.readFile (directory ++ name ++ ".phil")
  asymmetric <- fixture "accepted-asymmetric"
  retained <- fixture "retained-affine"
  siblings <- fixture "both-local-affine"
  unrestricted <- fixture "unrestricted-local"
  stranded <- fixture "unreleased-linear-local"
  stale <- fixture "stale-after-join"
  unjustified <- fixture "unjustified"
  unadmitted <- fixture "unadmitted"
  weakened <- fixture "mode-weakening"
  wrongWidth <- fixture "wrong-result-width"
  wrongCondition <- fixture "wrong-condition"
  joinSlot <- fixture "nonempty-join"
  unknownInitializer <- fixture "unknown-branch-initializer"
  escapedName <- fixture "out-of-scope-local"
  borrowed <- fixture "borrowed-branch-unsupported"
  let result = do
        checkAsymmetric asymmetric
        checkRetained retained
        checkBothLocals siblings
        checkUnrestrictedLocal unrestricted
        checkLinearLeak stranded
        checkStaleAfterJoin stale
        checkNominalRejections unjustified unadmitted weakened
        checkUnsupported wrongWidth "wrong declared result width"
        checkUnsupported wrongCondition "non-Bool source condition"
        checkUnsupported joinSlot "nonempty join-state telescope"
        checkUnsupported unknownInitializer "unknown branch-local initializer"
        checkUnsupported escapedName "out-of-scope branch-local spelling"
        checkUnsupported borrowed "nested borrow without source scope projection"
        assert (Text.replace "    let spare = permit;" "    let spare = payload;"
                  asymmetric == stranded)
          "linear scope failure is not exactly one changed source statement"
        assert (Text.replace "  return payload;" "  permit;\n  return payload;"
                  asymmetric == stale)
          "post-join stale reuse is not exactly one added source statement"
  case result of
    Right () -> putStrLn
      "PASS: source-declared affine branch asymmetry, real scope prune, linear failure, exact Core join"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
