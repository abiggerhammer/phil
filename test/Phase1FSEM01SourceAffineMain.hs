{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.NominalDataMode
  ( NominalModeError (..), NominalRestrictionJustification (..) )
import Phil.Core.Static
  ( DeclarationKey (..), InterfaceRevision (..), emptyStaticContext )
import Phil.Core.Syntax (Control (..), Mode (..), Name, Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckResult (..)
  , SurfaceCheckError (..) )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedTypeModeOrigin (..) )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataModeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl, GrammarV1FunctionDecl
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..), parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceAffineResource
  ( GrammarV1AffineSourceError (..), GrammarV1AffineSourceTrace (..)
  , grammarV1CheckedAffineFunctionTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.affine.Permit"

functionRoot :: DeclarationKey
functionRoot = DeclarationKey "decl.fsem01.affine.use"

revision :: InterfaceRevision
revision = InterfaceRevision "iface.fsem01.affine.v1"

lifecycle :: Maybe NominalRestrictionJustification
lifecycle = Just (AdmittedLifecycleObligation
  "reviewed external nominal lifecycle: Permit can be dropped")

permitTy :: Ty
permitTy = TyOpaque "Permit"

sourceDir :: FilePath
sourceDir = "test/fixtures/fsem01-source-affine-v1/"

assert :: Bool -> String -> Either String ()
assert yes detail = if yes then Right () else Left detail

parsePair :: Text -> Either String (GrammarV1DataDecl,GrammarV1FunctionDecl)
parsePair source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-affine" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ dat,Located _ fn] ->
      case (locatedValue (grammarV1Declaration dat),
            locatedValue (grammarV1Declaration fn)) of
        (GrammarV1DataDeclaration a,GrammarV1FunctionDeclaration b) ->
          Right (a,b)
        _ -> Left "source is not data declaration followed by function"
    _ -> Left "expected one data and one source function"

check :: Maybe NominalRestrictionJustification -> Text
  -> Maybe (Either GrammarV1AffineSourceError GrammarV1AffineSourceTrace)
check justification input =
  case parsePair input of
    Left _ -> Nothing
    Right (dat,fn) ->
      grammarV1CheckedAffineFunctionTrace
        emptyStaticContext root revision justification dat functionRoot fn

runAccepted :: Text -> Bool -> Either String ()
runAccepted source consumes = do
  (dat,fn) <- parsePair source
  result <- case grammarV1CheckedAffineFunctionTrace
    emptyStaticContext root revision lifecycle dat functionRoot fn of
      Just (Right success) -> Right success
      other -> Left ("source not admitted through checked affine route: " ++ show other)
  let binder = affineSourceBinder result
      owner = grammarV1ResolvedBinderCoreName binder
      view = grammarV1ResolvedBinderCoreName (affineSourceViewBinder result)
      cuts = affineSourceCheckpoints result
      contextOf cut = Core.ResourceContext
        { Core.unrestrictedBindings = traceUnrestrictedOwners cut
        , Core.affineBindings = traceAffineOwners cut
        , Core.linearBindings = traceLinearOwners cut
        , Core.sharedLoans = traceActiveLoans cut
        }
      expectedReturn = if consumes then permitTy else TyUnit
      expectedOutcome = SurfaceCheckResult "use" [Return expectedReturn]
  assert (affineSourceDeclarationKey result == root &&
          affineSourceInterfaceRevision result == revision)
    "lost stable source data identity"
  assert (affineSourceCheckedMode result ==
          CheckedTypeMode permitTy Affine)
    "parameter acquired guessed or mutated structural mode"
  assert (affineSourceTypeOrigin result ==
          GrammarV1NamedTypeModeOrigin
            (ReferencedGenericStaticActual "Permit")
            root revision)
    "parameter lost resolved nominal declaration/interface provenance"
  assert (null (affineSourceFocusingSteps result))
    "nominal Permit acquired an unrelated focusing trace"
  assert (affineSourceOutcome result == Right expectedOutcome)
    ("unexpected production result: " ++ show (affineSourceOutcome result))
  assert (map tracePhase cuts ==
    [ TraceBeforeLoan,TraceLoanStarted,TraceBodyResult False,
      TraceLoanClosed,TraceOwnerReturned ])
    "affine borrow lifecycle did not produce exact production checkpoints"
  case map contextOf cuts of
    [before,started,body,closed,terminal] -> do
      assert (Core.affineBindings before == Map.singleton owner permitTy)
        "source-derived owner not in Core's affine map"
      assert (Core.linearBindings before == Map.empty &&
              Core.unrestrictedBindings before == Map.empty &&
              Core.sharedLoans before == Set.empty)
        "source-derived affine owner was inserted into wrong Core domain"
      assert (Core.startSharedLoan owner before == Right started &&
              Core.sharedLoans started == Set.singleton owner &&
              Core.affineBindings started == Map.singleton owner permitTy)
        "production borrow did not match exact Core affine loan start"
      assert (started == body)
        "borrow view use changed owner's affine map"
      assert (Core.consumeAffine owner started ==
        Left (Core.OwnerBorrowed owner))
        "borrowed source-derived affine owner was consumable"
      assert (Core.endSharedLoan owner body == Right closed)
        "production borrow end lost exact source-derived affine owner"
      assert (traceOwnerName (cuts !! 0) == owner &&
              traceViewName (cuts !! 0) == view)
        "checkpoint does not retain source-resolved binder identities"
      assert (Core.ensureComplete closed == Right ())
        "unconsumed affine owner wrongly required linear completion"
      if consumes then do
        assert (Core.consumeAffine owner closed ==
          Right (permitTy,terminal))
          "affine return did not consume exact source owner"
        assert (Core.consumeAffine owner terminal ==
          Left (Core.UnknownBinding owner))
          "affine owner reused after consumption"
        assert (Core.affineBindings terminal == Map.empty &&
                Core.sharedLoans terminal == Set.empty)
          "affine consumption had a residual owner or loan"
      else do
        assert (terminal == closed &&
                Core.affineBindings terminal == Map.singleton owner permitTy)
          "legally droppable affine owner unexpectedly consumed"
        assert (Core.ensureComplete terminal == Right ())
          "terminal affine resource is not droppable"
    _ -> Left "wrong number of source-derived affine checkpoints"

runEscape :: Text -> Either String ()
runEscape source = do
  (dat,fn) <- parsePair source
  result <- case grammarV1CheckedAffineFunctionTrace
    emptyStaticContext root revision lifecycle dat functionRoot fn of
      Just (Right trace) -> Right trace
      other -> Left ("affine BorrowEscape not traced: " ++ show other)
  let owner = grammarV1ResolvedBinderCoreName (affineSourceBinder result)
      cuts = affineSourceCheckpoints result
  case affineSourceOutcome result of
    Left err -> assert
      (surfaceErrorClass err == BorrowEscape &&
       surfaceErrorDetail err == "shared view escapes its lexical scope")
      ("wrong rejection class for affine escape: " ++ show err)
    other -> Left ("borrowed view unexpectedly escaped: " ++ show other)
  assert (map tracePhase cuts ==
    [TraceBeforeLoan,TraceLoanStarted,TraceBodyResult True,
     TraceEscapeRejected])
    "escape invented post-rejection resource states"
  assert (all (\cut ->
    traceAffineOwners cut == Map.singleton owner permitTy &&
    traceLinearOwners cut == Map.empty) cuts)
    "failed affine source escaped the affine map"
  assert (Core.consumeAffine owner
    (Core.ResourceContext Map.empty
      (traceAffineOwners (last cuts)) Map.empty
      (traceActiveLoans (last cuts))) ==
      Left (Core.OwnerBorrowed owner))
    "rejected borrow released an active owner's loan"

runNominalFailures :: Text -> Text -> Either String ()
runNominalFailures noJust weakened = do
  let missing = check Nothing noJust
      unadmitted = check (Just (UnadmittedNominalRestriction
        "source spelling is not proof")) noJust
      weakenedAttempt = check Nothing weakened
  assert (missing ==
    Just (Left (AffineSourceNominalError
      (GrammarV1DataModeNominalError
        (StrongerModeMissingJustification Unrestricted Affine)))))
    ("source mode was enough without lifecycle attestation: " ++ show missing)
  assert (unadmitted ==
    Just (Left (AffineSourceNominalError
      (GrammarV1DataModeNominalError
        (StrongerModeUnadmittedJustification "source spelling is not proof")))))
    "unadmitted external mode-strengthening attestation was accepted"
  assert (weakenedAttempt ==
    Just (Left (AffineSourceNominalError
      (GrammarV1DataModeNominalError
        (DeclaredModeWeakensDerived Linear Unrestricted)))))
    "source mode weakening bypassed Core nominal authority"

main :: IO ()
main = do
  consume <- TextIO.readFile (sourceDir ++ "consume.phil")
  dropSource <- TextIO.readFile (sourceDir ++ "drop.phil")
  escape <- TextIO.readFile (sourceDir ++ "escape.phil")
  unjustified <- TextIO.readFile (sourceDir ++ "unjustified.phil")
  weakened <- TextIO.readFile (sourceDir ++ "weakened.phil")
  let result = do
        runAccepted consume True
        runAccepted dropSource False
        runEscape escape
        runNominalFailures unjustified weakened
        assert (Text.replace "view; unit;" "view;" consume == escape)
          "BorrowEscape is not the minimal source body mutation"
  case result of
    Right () -> putStrLn
      "PASS: source-declared affine nominal owner, production loan/consume/drop, exact errors"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
