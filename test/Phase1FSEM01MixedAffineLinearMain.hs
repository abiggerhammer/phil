{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: one genuinely parsed source function with simultaneous affine and
-- linear owners. The source-derived nominal admission is externally trusted;
-- production errors and all four native resource domains are observed directly.
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
import Phil.Core.Syntax
  ( Control (..), Mode (..), RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedTypeModeOrigin (..) )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataModeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl, GrammarV1FunctionDecl
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..), parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceAffineResource
  ( GrammarV1AffineSourceError (..), GrammarV1MixedAffineLinearTrace (..)
  , grammarV1CheckedMixedAffineLinearFunctionTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.mixed.Permit"

functionRoot :: DeclarationKey
functionRoot = DeclarationKey "decl.fsem01.mixed.use"

revision :: InterfaceRevision
revision = InterfaceRevision "iface.fsem01.mixed.v1"

lifecycle :: Maybe NominalRestrictionJustification
lifecycle = Just (AdmittedLifecycleObligation
  "external reviewed permission to abandon Permit")

permitTy :: Ty
permitTy = TyOpaque "Permit"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

sourceDir :: FilePath
sourceDir = "test/fixtures/fsem01-mixed-affine-linear-v1/"

assert :: Bool -> String -> Either String ()
assert yes detail = if yes then Right () else Left detail

parsePair :: Text -> Either String (GrammarV1DataDecl, GrammarV1FunctionDecl)
parsePair source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "mixed-affine-linear-v1" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ dat, Located _ fn] ->
      case (locatedValue (grammarV1Declaration dat),
            locatedValue (grammarV1Declaration fn)) of
        (GrammarV1DataDeclaration a, GrammarV1FunctionDeclaration b) ->
          Right (a, b)
        _ -> Left "source is not one nominal data declaration and function"
    _ -> Left "expected exactly one data declaration and one function"

check :: Maybe NominalRestrictionJustification -> Text
  -> Maybe (Either GrammarV1AffineSourceError GrammarV1MixedAffineLinearTrace)
check attestation input =
  case parsePair input of
    Left _ -> Nothing
    Right (dat, fn) ->
      grammarV1CheckedMixedAffineLinearFunctionTrace
        emptyStaticContext root revision attestation dat functionRoot fn

checked :: Text -> Either String GrammarV1MixedAffineLinearTrace
checked source =
  case check lifecycle source of
    Just (Right result) -> Right result
    other -> Left ("mixed source was not admitted into production checker: "
      ++ show other)

contextOf :: BorrowTraceCheckpoint -> Core.ResourceContext
contextOf cut = Core.ResourceContext
  { Core.unrestrictedBindings = traceUnrestrictedOwners cut
  , Core.affineBindings = traceAffineOwners cut
  , Core.linearBindings = traceLinearOwners cut
  , Core.sharedLoans = traceActiveLoans cut
  }

checkInitial :: GrammarV1MixedAffineLinearTrace -> Either String ()
checkInitial result = do
  let permit = grammarV1ResolvedBinderCoreName (mixedAffineBinder result)
      payload = grammarV1ResolvedBinderCoreName (mixedLinearBinder result)
      view = grammarV1ResolvedBinderCoreName (mixedViewBinder result)
      cuts = mixedCheckpoints result
  assert (permit /= payload && permit /= view && payload /= view)
    "binder identities from one parsed function collide"
  assert (mixedDeclarationKey result == root &&
          mixedInterfaceRevision result == revision)
    "mixed nominal identity or interface revision lost"
  assert (mixedAffineCheckedMode result == CheckedTypeMode permitTy Affine &&
          mixedLinearCheckedMode result == CheckedTypeMode bytes8 Linear)
    "mixed source parameters were not checked in their separate modes"
  assert (mixedAffineTypeOrigin result ==
          GrammarV1NamedTypeModeOrigin
            (ReferencedGenericStaticActual "Permit") root revision)
    "the affine binding was installed without exact named-type provenance"
  assert (not (null cuts)) "no real production resource checkpoints"
  let before = contextOf (head cuts)
  assert (traceOwnerName (head cuts) == permit &&
          traceViewName (head cuts) == view)
    "production loan used a different semantic source binder"
  assert (Core.affineBindings before == Map.singleton permit permitTy &&
          Core.linearBindings before == Map.singleton payload bytes8 &&
          Core.unrestrictedBindings before == Map.empty &&
          Core.sharedLoans before == Set.empty)
    "source failed to install exact affine/linear four-zone context"

checkSuccessful :: Text -> Either String ()
checkSuccessful input = do
  result <- checked input
  checkInitial result
  let permit = grammarV1ResolvedBinderCoreName (mixedAffineBinder result)
      payload = grammarV1ResolvedBinderCoreName (mixedLinearBinder result)
      cuts = mixedCheckpoints result
  assert (mixedOutcome result ==
          Right (SurfaceCheckResult "use" [Return bytes8]))
    ("actual production mixed return was not Bytes[8]: "
      ++ show (mixedOutcome result))
  assert (map tracePhase cuts ==
    [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False
    , TraceLoanClosed, TraceOwnerReturned ])
    "mixed source accepted path emitted wrong production checkpoint sequence"
  case map contextOf cuts of
    [before, started, body, closed, finished] -> do
      assert (Core.startSharedLoan permit before == Right started)
        "native mixed affine loan start differs from production trace"
      assert (started == body)
        "borrow view read changed either owner or any resource zone"
      assert (Core.consumeAffine permit started ==
              Left (Core.OwnerBorrowed permit))
        "borrowed affine owner was consumable"
      assert (Core.endSharedLoan permit body == Right closed)
        "loan close changed linear spectator or lost affine owner"
      assert (Core.consumeLinear payload closed == Right (bytes8, finished))
        "linear source return did not consume exactly its own binding"
      assert (Core.affineBindings finished == Map.singleton permit permitTy &&
              Core.linearBindings finished == Map.empty &&
              Core.unrestrictedBindings finished == Map.empty &&
              Core.sharedLoans finished == Set.empty)
        "linear return damaged affine spectator or left a linear debt"
      assert (Core.ensureComplete finished == Right ())
        "optional affine owner improperly blocked terminal return"
      assert (Core.consumeLinear payload finished ==
              Left (Core.UnknownBinding payload))
        "linear owner was usable a second time"
      assert (Core.consumeAffine permit finished ==
              Right (permitTy, Core.emptyContext))
        "terminal affine owner could not be disposed independently"
      case Core.consumeLinear payload started of
        Right (ty, independent) -> do
          assert (ty == bytes8 &&
                  Core.affineBindings independent ==
                    Core.affineBindings started &&
                  Core.sharedLoans independent == Set.singleton permit &&
                  Core.unrestrictedBindings independent == Map.empty)
            "independent linear consumption disrupted an active affine loan"
          assert (Core.endSharedLoan permit independent ==
            Right finished)
            "independently consumed linear owner disturbed affine close"
        other -> Left ("linear spectator was blocked by affine loan: " ++ show other)
    _ -> Left "accepted production trace missing five real snapshots"

checkEscape :: Text -> Either String ()
checkEscape input = do
  result <- checked input
  checkInitial result
  let permit = grammarV1ResolvedBinderCoreName (mixedAffineBinder result)
      payload = grammarV1ResolvedBinderCoreName (mixedLinearBinder result)
      cuts = mixedCheckpoints result
  case mixedOutcome result of
    Left err ->
      assert (surfaceErrorClass err == BorrowEscape &&
              surfaceErrorDetail err == "shared view escapes its lexical scope")
        ("expected precise BorrowEscape, got " ++ show err)
    other -> Left ("borrowed view unexpectedly returned: " ++ show other)
  assert (map tracePhase cuts ==
    [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult True
    , TraceEscapeRejected ])
    "BorrowEscape invented a success or post-rejection successor"
  case map contextOf cuts of
    [before, started, body, rejected] -> do
      assert (Core.startSharedLoan permit before == Right started &&
              started == body && body == rejected)
        "failed affine borrow fabricated a resource-state transition"
      assert (Core.consumeAffine permit rejected ==
              Left (Core.OwnerBorrowed permit))
        "borrow failure silently released the affine loan"
      assert (Core.linearBindings rejected == Map.singleton payload bytes8 &&
              Core.affineBindings rejected == Map.singleton permit permitTy)
        "borrow failure lost one of the two source owners"
    _ -> Left "escape trace had unexpected resource checkpoints"

-- Return Unit or the affine owner instead of Bytes[8]. Both are rejected by
-- the actual production checker because the linear Bytes remains live.
checkLinearDebt :: Text -> Either String ()
checkLinearDebt input = do
  result <- checked input
  checkInitial result
  let permit = grammarV1ResolvedBinderCoreName (mixedAffineBinder result)
      payload = grammarV1ResolvedBinderCoreName (mixedLinearBinder result)
      cuts = mixedCheckpoints result
      expectedDebt = Core.UnconsumedLinearResources (Map.singleton payload bytes8)
  case mixedOutcome result of
    Left err ->
      assert (surfaceErrorClass err == LinearCompletion &&
              surfaceErrorDetail err == Text.pack (show expectedDebt))
        ("missing or wrong exact linear completion error: " ++ show err)
    other -> Left ("live linear owner was accepted at terminal: " ++ show other)
  assert (map tracePhase cuts ==
    [TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False, TraceLoanClosed])
    "linear failure fabricated a returned-owner success checkpoint"
  case map contextOf cuts of
    [before, started, body, closed] -> do
      assert (Core.startSharedLoan permit before == Right started &&
              started == body &&
              Core.endSharedLoan permit body == Right closed)
        "linear debt negative lost valid affine borrow prefix"
      assert (Core.ensureComplete closed == Left expectedDebt &&
              Core.affineBindings closed == Map.singleton permit permitTy)
        "affine optionality incorrectly discharged a linear obligation"
    _ -> Left "linear-debt trace had unexpected resource checkpoints"

checkNominalRejections :: Text -> Text -> Either String ()
checkNominalRejections noJust weakened = do
  let missing = check Nothing noJust
      unadmitted = check (Just (UnadmittedNominalRestriction
        "text is not nominal authority")) noJust
  assert (missing == Just (Left (AffineSourceNominalError
    (GrammarV1DataModeNominalError
      (StrongerModeMissingJustification Unrestricted Affine)))))
    ("source mode spelling admitted without lifecycle authority: " ++ show missing)
  assert (unadmitted == Just (Left (AffineSourceNominalError
    (GrammarV1DataModeNominalError
      (StrongerModeUnadmittedJustification "text is not nominal authority")))))
    "an unadmitted lifecycle statement became nominal authority"
  assert (check Nothing weakened == Just (Left (AffineSourceNominalError
    (GrammarV1DataModeNominalError
      (DeclaredModeWeakensDerived Linear Unrestricted)))))
    "unrestricted declaration weakened a linear payload"

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported input label =
  assert (check lifecycle input == Nothing)
    ("out-of-competence source silently accepted: " ++ label)

main :: IO ()
main = do
  positive <- TextIO.readFile (sourceDir ++ "accepted.phil")
  escaping <- TextIO.readFile (sourceDir ++ "escape.phil")
  leaked <- TextIO.readFile (sourceDir ++ "leak-linear.phil")
  returnedPermit <- TextIO.readFile (sourceDir ++ "return-affine.phil")
  unjustified <- TextIO.readFile (sourceDir ++ "unjustified.phil")
  weakened <- TextIO.readFile (sourceDir ++ "weakened.phil")
  wrongReturn <- TextIO.readFile (sourceDir ++ "wrong-return.phil")
  wrongBorrow <- TextIO.readFile (sourceDir ++ "wrong-borrow.phil")
  let outcome = do
        checkSuccessful positive
        checkEscape escaping
        checkLinearDebt leaked
        checkLinearDebt returnedPermit
        checkNominalRejections unjustified weakened
        checkUnsupported wrongReturn "mismatched Bytes return width"
        checkUnsupported wrongBorrow "borrow of linear owner not affine owner"
        assert (Text.replace "view; unit;" "view;" positive == escaping)
          "BorrowEscape witness is not the minimal source mutation"
  case outcome of
    Right () -> putStrLn
      "PASS: single-source mixed affine/linear ownership; exact production traces, debt and errors"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
