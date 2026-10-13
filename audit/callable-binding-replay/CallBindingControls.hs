{-# LANGUAGE OverloadedStrings #-}

-- Supplemental correctness controls for the original Phil Phase 1 candidate.
-- Prepared by source review. NOT compiled or executed in the audit environment.
-- Keep this driver outside the checkout; do not replace the permanent corpus.
module Main (main) where

import Control.Monad (forM, forM_)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.EffectPolymorphism
  ( CheckedEffectSetInstantiation (..)
  , EffectSetInstantiationError (..)
  , EffectSetParameterBound (..)
  , checkBoundedEffectSetInstantiation
  , effectSetSemanticForm
  )
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
  ( CheckedGenericStaticActual (..)
  , GenericStaticActual (..)
  , GenericStaticKind (..)
  , GenericStaticKindError (..)
  , GenericStaticParameter (..)
  , GenericStaticReferenceCandidate (..)
  , checkGenericStaticActuals
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , SemanticForm (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax (Control (..), Mode (..), Ty (..))
import Phil.Surface.Check
  ( InitialBinding (..)
  , PrimitiveSemantics (..)
  , RejectionClass (..)
  , SurfaceCallableSignature (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.GrammarV1.CallableEffects
  ( GrammarV1CallableEffectBoundTemplate (..)
  )
import Phil.Surface.GrammarV1.SemanticEffectPolymorphism
  ( GrammarV1CallableEffectInstantiationError (..)
  , grammarV1InstantiateCallableEffectBounds
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  outcomes <- forM cases $ \(caseId, description, result) ->
    case result of
      Right () -> do
        putStrLn (caseId <> " PASS " <> description)
        pure True
      Left detail -> do
        putStrLn (caseId <> " FAIL " <> description <> " -- " <> detail)
        pure False
  if and outcomes then pure () else exitFailure

cases :: [(String, String, Either String ())]
cases =
  [ ("C01", "all nine direct kinds retain exact key/kind/form", directKinds)
  , ("C02", "all unequal direct kind pairs reject", unequalDirectKinds)
  , ("C03", "duplicate parameter keys reject before arity", duplicateParameters)
  , ("C04", "too few and too many static actuals reject", staticArity)
  , ("C05", "unresolved and wrong-kind references remain distinct", referenceErrors)
  , ("C06", "expected-kind reference wins independently of ordering", referenceSelection)
  , ("C07", "same-kind candidate multiplicity is ambiguous", referenceAmbiguity)
  , ("C08", "ordered parameter-to-actual association is preserved", positionalActuals)
  , ("C09", "effect key/kind/representation guards are independent", effectAdmission)
  , ("C10", "narrower actual and unchanged upper remain distinct", effectSubset)
  , ("C11", "effect template binding domain is exact", templateDomain)
  , ("C12", "concrete and repeated parameter templates retain meaning", templateActual)
  , ("C13", "linear call arguments are consumed once", linearArgument)
  , ("C14", "call arity rejects before argument lookup", callableArity)
  , ("C15", "call argument type must match", callableType)
  , ("C16", "call argument structural mode must match", callableMode)
  , ("C17", "callable and provider namespaces remain distinct", namespaces)
  , ("C18", "restricted results survive binding or nested use, not discard", callableResult)
  , ("C19", "argument evaluation threads the actual resource state", argumentState)
  , ("C20", "only unrestricted Unit is a valid Unit result", unitResult)
  ]

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

expectLeft :: (Eq e, Show e, Show a) => e -> Either e a -> Either String ()
expectLeft expected result = case result of
  Left actual -> assert (actual == expected)
    ("expected " <> show expected <> ", got " <> show actual)
  Right value -> Left ("expected rejection " <> show expected <> ", got " <> show value)

keyA, keyB :: GenericStaticParameterKey
keyA = GenericStaticParameterKey "audit.parameter.a"
keyB = GenericStaticParameterKey "audit.parameter.b"

kinds :: [GenericStaticKind]
kinds =
  [ GenericTypeKind, GenericIndexKind, GenericSessionKind, GenericMessageKind
  , GenericEffectsKind, GenericProviderContractKind, GenericCallableContractKind
  , GenericBoundaryContractKind, GenericArchitectureDependencyKind
  ]

parameter :: GenericStaticParameterKey -> GenericStaticKind -> GenericStaticParameter
parameter = GenericStaticParameter

candidate :: Text -> GenericStaticKind -> SemanticForm -> GenericStaticReferenceCandidate
candidate = GenericStaticReferenceCandidate

checkedDirect
  :: GenericStaticParameterKey -> GenericStaticKind -> SemanticForm
  -> Either String CheckedGenericStaticActual
checkedDirect key kind form = do
  result <- mapLeft show $ checkGenericStaticActuals
    [parameter key kind] [DirectGenericStaticActual kind form] []
  case result of
    [checked] -> Right checked
    other -> Left ("single actual produced wrong result count: " <> show other)

directKinds :: Either String ()
directKinds = forM_ kinds $ \kind -> do
  let form = SemanticAtom "audit.opaque.semantic.form"
  actual <- checkedDirect keyA kind form
  assert
    ( actual == CheckedGenericStaticActual keyA kind form )
    ("direct actual changed key, kind, or form: " <> show actual)

unequalDirectKinds :: Either String ()
unequalDirectKinds = forM_ [(a, b) | a <- kinds, b <- kinds, a /= b] $ \(expected, actual) ->
  expectLeft (GenericStaticDirectKindMismatch keyA expected actual) $
    checkGenericStaticActuals [parameter keyA expected]
      [DirectGenericStaticActual actual (SemanticAtom "audit.form")] []

duplicateParameters :: Either String ()
duplicateParameters = expectLeft (DuplicateGenericStaticParameter keyA) $
  checkGenericStaticActuals
    [parameter keyA GenericTypeKind, parameter keyA GenericIndexKind] [] []

staticArity :: Either String ()
staticArity = do
  let p = parameter keyA GenericTypeKind
      a = DirectGenericStaticActual GenericTypeKind (SemanticAtom "audit.A")
  expectLeft (GenericStaticActualCountMismatch 1 0) $
    checkGenericStaticActuals [p] [] []
  expectLeft (GenericStaticActualCountMismatch 1 2) $
    checkGenericStaticActuals [p] [a, a] []

referenceErrors :: Either String ()
referenceErrors = do
  let ps = [parameter keyA GenericTypeKind]
      as = [ReferencedGenericStaticActual "Item"]
  expectLeft (GenericStaticReferenceUnresolved keyA GenericTypeKind "Item") $
    checkGenericStaticActuals ps as []
  expectLeft
    (GenericStaticReferenceKindMismatch keyA GenericTypeKind "Item"
      (Set.singleton GenericIndexKind)) $
    checkGenericStaticActuals ps as
      [candidate "Item" GenericIndexKind (SemanticAtom "audit.index")]

referenceSelection :: Either String ()
referenceSelection = do
  let form = SemanticAtom "audit.type"
      references =
        [ candidate "Item" GenericIndexKind (SemanticAtom "audit.index")
        , candidate "Other" GenericTypeKind (SemanticAtom "audit.other")
        , candidate "Item" GenericTypeKind form
        ]
      check refs = checkGenericStaticActuals [parameter keyA GenericTypeKind]
        [ReferencedGenericStaticActual "Item"] refs
      expected = [CheckedGenericStaticActual keyA GenericTypeKind form]
  forward <- mapLeft show (check references)
  backward <- mapLeft show (check (reverse references))
  assert (forward == expected && backward == expected)
    "reference selection changed with irrelevant candidates or ordering"

referenceAmbiguity :: Either String ()
referenceAmbiguity = do
  let a = SemanticAtom "audit.A"
      b = SemanticAtom "audit.B"
      check forms = checkGenericStaticActuals [parameter keyA GenericTypeKind]
        [ReferencedGenericStaticActual "Item"]
        (candidate "Item" GenericIndexKind (SemanticAtom "audit.index")
          : map (candidate "Item" GenericTypeKind) forms)
  forM_ [[a, b], [a, a]] $ \forms ->
    expectLeft (GenericStaticReferenceAmbiguous keyA GenericTypeKind "Item" forms)
      (check forms)

positionalActuals :: Either String ()
positionalActuals = do
  let a = SemanticAtom "audit.A"
      b = SemanticAtom "audit.B"
      ps = [parameter keyA GenericTypeKind, parameter keyB GenericTypeKind]
      check forms = checkGenericStaticActuals ps
        (map (DirectGenericStaticActual GenericTypeKind) forms) []
  ab <- mapLeft show (check [a, b])
  ba <- mapLeft show (check [b, a])
  assert
    ( ab == [CheckedGenericStaticActual keyA GenericTypeKind a,
             CheckedGenericStaticActual keyB GenericTypeKind b]
      && ba == [CheckedGenericStaticActual keyA GenericTypeKind b,
                CheckedGenericStaticActual keyB GenericTypeKind a]
      && ab /= ba )
    "positional association or ordered result was lost"

readEffect, writeEffect, extraEffect :: SemanticEffect
readEffect = SemanticEffect "effect:audit.read"
writeEffect = SemanticEffect "effect:audit.write"
extraEffect = SemanticEffect "effect:audit.extra"

upperEffects, narrowEffects :: Set.Set SemanticEffect
upperEffects = Set.fromList [readEffect, writeEffect]
narrowEffects = Set.singleton readEffect

checkedEffects :: GenericStaticParameterKey -> Either String CheckedEffectSetInstantiation
checkedEffects key = do
  actual <- checkedDirect key GenericEffectsKind (effectSetSemanticForm narrowEffects)
  mapLeft show $ checkBoundedEffectSetInstantiation
    (EffectSetParameterBound key upperEffects) actual

effectAdmission :: Either String ()
effectAdmission = do
  let bound = EffectSetParameterBound keyA upperEffects
  wrongKey <- checkedDirect keyB GenericEffectsKind (effectSetSemanticForm narrowEffects)
  wrongKind <- checkedDirect keyA GenericTypeKind (effectSetSemanticForm narrowEffects)
  malformed <- checkedDirect keyA GenericEffectsKind (SemanticAtom "not-a-finite-effect-set")
  expectLeft (EffectSetParameterKeyMismatch keyA keyB) $
    checkBoundedEffectSetInstantiation bound wrongKey
  expectLeft (EffectSetActualKindMismatch GenericTypeKind) $
    checkBoundedEffectSetInstantiation bound wrongKind
  expectLeft (EffectSetActualSemanticFormMalformed (SemanticAtom "not-a-finite-effect-set")) $
    checkBoundedEffectSetInstantiation bound malformed

effectSubset :: Either String ()
effectSubset = do
  accepted <- checkedEffects keyA
  assert
    ( checkedEffectSetParameterKey accepted == keyA
      && checkedEffectSetActual accepted == narrowEffects
      && checkedEffectSetUpper accepted == upperEffects )
    "accepted effect actual changed the public upper bound or lost its own value"
  wider <- checkedDirect keyA GenericEffectsKind
    (effectSetSemanticForm (Set.insert extraEffect narrowEffects))
  expectLeft (EffectSetBoundExceeded keyA (Set.singleton extraEffect) upperEffects) $
    checkBoundedEffectSetInstantiation (EffectSetParameterBound keyA upperEffects) wider

templateDomain :: Either String ()
templateDomain = do
  a <- checkedEffects keyA
  b <- checkedEffects keyB
  let template = GrammarV1CallableEffectsParameterBound keyA
  expectLeft (GrammarV1MissingCallableEffectInstantiation keyA) $
    grammarV1InstantiateCallableEffectBounds [] [template]
  expectLeft (GrammarV1DuplicateCallableEffectInstantiation keyA) $
    grammarV1InstantiateCallableEffectBounds [a, a] [template]
  expectLeft (GrammarV1UnexpectedCallableEffectInstantiation keyB) $
    grammarV1InstantiateCallableEffectBounds [a, b] [template]

templateActual :: Either String ()
templateActual = do
  accepted <- checkedEffects keyA
  let fixed = Set.singleton writeEffect
      ref = GrammarV1CallableEffectsParameterBound keyA
  actual <- mapLeft show $ grammarV1InstantiateCallableEffectBounds [accepted]
    [GrammarV1ConcreteCallableEffectBound fixed, ref, ref]
  assert (actual == [fixed, narrowEffects, narrowEffects])
    "concrete clause changed or parameter template substituted the upper bound"

blob :: Ty
blob = TyOpaque "Blob"

signature :: Text -> [(Mode, Ty)] -> Maybe (Mode, Ty) -> SurfaceCallableSignature
signature key parameters result = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = DeclarationKey key
  , surfaceCallableParameters = parameters
  , surfaceCallableResult = result
  }

baseEnvironment :: SurfaceEnvironment
baseEnvironment = emptySurfaceEnvironment emptyStaticContext

takeEnvironment :: Mode -> SurfaceEnvironment
takeEnvironment mode = baseEnvironment
  { surfaceInitialBindings = Map.singleton "candidate"
      (InitialBinding mode blob PlainShape)
  , surfaceCallables = Map.singleton "Take"
      (signature "audit.take" [(Linear, blob)] Nothing)
  }

checkSource :: SurfaceEnvironment -> Text -> Either String (Either SurfaceCheckError SurfaceCheckResult)
checkSource environment source = do
  parsed <- mapLeft (("PARSER FAILURE (not a semantic rejection): " <>) . show) $
    parseSurfaceFile "audit-call-binding" source
  case surfaceComponents parsed of
    [component] -> Right (checkSurfaceComponent environment component)
    components -> Left ("fixture expected one component, got " <> show (length components))

acceptSource :: SurfaceEnvironment -> Text -> [Control] -> Either String ()
acceptSource environment source expectedControls = do
  checked <- checkSource environment source
  result <- mapLeft show checked
  assert (checkedTerminalControls result == expectedControls)
    ("unexpected terminal controls: " <> show (checkedTerminalControls result))

rejectSource :: RejectionClass -> SurfaceEnvironment -> Text -> Either String ()
rejectSource expected environment source = do
  checked <- checkSource environment source
  case checked of
    Left err -> assert (surfaceErrorClass err == expected)
      ("expected " <> show expected <> ", got " <> show err)
    Right result -> Left ("expected semantic rejection, got " <> show result)

linearArgument :: Either String ()
linearArgument = do
  acceptSource (takeEnvironment Linear)
    "component Caller(candidate) { invoke Take(candidate) return unit }" [Return TyUnit]
  rejectSource StructuralUse (takeEnvironment Linear)
    "component Caller(candidate) { invoke Take(candidate) return candidate }"

callableArity :: Either String ()
callableArity = do
  rejectSource TypeMismatch (takeEnvironment Linear)
    "component Caller(candidate) { invoke Take() return unit }"
  rejectSource TypeMismatch (takeEnvironment Linear)
    "component Caller(candidate) { invoke Take(invoke Missing(), unit) return unit }"

callableType :: Either String ()
callableType = rejectSource TypeMismatch
  (baseEnvironment { surfaceCallables = surfaceCallables (takeEnvironment Linear) })
  "component Caller { invoke Take(true) return unit }"

callableMode :: Either String ()
callableMode = forM_ [Unrestricted, Affine] $ \mode ->
  rejectSource StructuralUse (takeEnvironment mode)
    "component Caller(candidate) { invoke Take(candidate) return unit }"

namespaces :: Either String ()
namespaces = do
  let environment = (takeEnvironment Linear)
        { surfaceCallables = Map.singleton "Worker" (signature "audit.worker" [] Nothing)
        , surfacePrimitives = Map.singleton "Worker" PrimitiveUse
        }
  rejectSource TypeMismatch environment
    "component Caller(candidate) { invoke Worker(candidate) return unit }"
  acceptSource environment
    "component Caller(candidate) { Worker(candidate) return unit }" [Return TyUnit]
  rejectSource UnknownCallable
    (baseEnvironment { surfacePrimitives = Map.singleton "Worker" PrimitiveUse })
    "component Caller { invoke Worker() return unit }"

callableResult :: Either String ()
callableResult = do
  let environment = baseEnvironment
        { surfaceCallables = Map.fromList
            [ ("Maker", signature "audit.maker" [] (Just (Linear, blob)))
            , ("Take", signature "audit.take" [(Linear, blob)] Nothing)
            ]
        }
  acceptSource environment
    "component Caller { let value = invoke Maker() return value }" [Return blob]
  rejectSource LinearCompletion environment
    "component Caller { invoke Maker() return unit }"
  acceptSource environment
    "component Caller { invoke Take(invoke Maker()) return unit }" [Return TyUnit]

argumentState :: Either String ()
argumentState = do
  let environment = (takeEnvironment Linear)
        { surfaceCallables = Map.insert "Pair"
            (signature "audit.pair" [(Unrestricted, TyUnit), (Linear, blob)] Nothing)
            (surfaceCallables (takeEnvironment Linear))
        }
  acceptSource environment
    "component Caller(candidate) { invoke Pair(unit, candidate) return unit }" [Return TyUnit]
  rejectSource StructuralUse environment
    "component Caller(candidate) { invoke Pair(invoke Take(candidate), candidate) return unit }"

unitResult :: Either String ()
unitResult = do
  let environment mode = baseEnvironment
        { surfaceCallables = Map.singleton "UnitMaker"
            (signature "audit.unit-maker" [] (Just (mode, TyUnit))) }
  acceptSource (environment Unrestricted)
    "component Caller { return invoke UnitMaker() }" [Return TyUnit]
  forM_ [Affine, Linear] $ \mode ->
    rejectSource TypeMismatch (environment mode)
      "component Caller { return invoke UnitMaker() }"
