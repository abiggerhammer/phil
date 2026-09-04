{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( ClaimDecl (..)
  , ClaimDefinition (..)
  , DeclarationKey (..)
  , StaticContext
  , StaticError (..)
  , declareOpaqueClaim
  , emptyStaticContext
  , lookupClaim
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  , moveVariable
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.BoundClaimApplication
  ( grammarV1BoundClaimApplication
  )
import Phil.Surface.GrammarV1.CheckedClaimApplication
  ( grammarV1CheckedClaimApplication
  )
import Phil.Surface.GrammarV1.ClaimDeclaration
  ( grammarV1ClaimDeclaration
  , grammarV1RegisterClaimDeclaration
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicClaimApplication)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticClaimDeclaration
  ( GrammarV1CheckedSemanticClaimDeclaration (..)
  , GrammarV1SemanticClaimDeclarationError (..)
  , grammarV1CheckedSemanticClaimDeclaration
  , grammarV1RegisterSemanticClaimDeclaration
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic claim applications preserve exact Core atoms"
        intrinsicClaimApplicationsPreserveMeaning
    , test "SURF-008 binding-aware claim arguments preserve richer verified term structure"
        boundClaimApplicationsPreserveMeaning
    , test "SURF-008 primitive Grammar-v1 claim declarations route to exact Core ClaimDecl semantics"
        claimDeclarationsPreserveMeaning
    , test "SURF-008 Grammar-v1 claims register only through Core StaticContext authority"
        claimRegistrationUsesCoreAuthority
    , test "SURF-008 Grammar-v1 claim applications delegate semantic checking to Core focusing"
        checkedClaimApplicationsUseCoreAuthority
    , test "SURF-009 semantic claim declarations use generated parameter identity"
        semanticClaimDeclarationsUseGeneratedNames
    , test "SURF-009 semantic claim declarations are alpha-stable and preserve optional parameter shape"
        semanticClaimDeclarationsAlphaStable
    , test "SURF-009 semantic claim registration substitutes generated formals through Core"
        semanticClaimRegistrationSubstitutesGeneratedFormals
    , test "SURF-009 semantic claim declaration diagnostics and competence remain explicit"
        semanticClaimDeclarationBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicClaimApplicationsPreserveMeaning :: Either String ()
intrinsicClaimApplicationsPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-claims" intrinsicSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1IntrinsicClaimApplication propositions
      expected =
        [ Just (Atom "Ready" [RefNat 7, RefNat 0])
        , Just (Atom "Flag" [RefBool True, RefBool False])
        , Just (Atom "Rules.Ready" [RefNat 1])
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "claim application elaboration changed identity/arguments or accepted contextual specialization: " <> show actual

boundClaimApplicationsPreserveMeaning :: Either String ()
boundClaimApplicationsPreserveMeaning = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "u" Unrestricted (TyUInt 32) state2
  state4 <- bind "flag" Unrestricted TyBool state3
  state5 <- bind "bytes" Unrestricted (TyBytes (RefNat 8)) state4
  state6 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state5
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state6
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-claims" boundSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls sourceFile)
  let n = RefVar (Name "n")
      m = RefVar (Name "m")
      u = RefVar (Name "u")
      bytes = RefVar (Name "bytes")
      actual = map (grammarV1BoundClaimApplication state) propositions
      expected =
        [ Just (Atom "Ready" [n, RefNat 1])
        , Just (Atom "Flag" [RefVar (Name "flag"), RefBool False])
        , Just (Atom "Rules.Ready" [n])
        , Just (Atom "Ready" [n])
        , Just (Atom "Ready" [RefAdd n (RefNat 1)])
        , Just (Atom "Ready" [RefSub n (RefNat 1)])
        , Just (Atom "Ready" [RefScale 2 n])
        , Just (Atom "Ready" [RefScale 2 n])
        , Just (Atom "Ready" [RefLen bytes])
        , Just (Atom "Ready" [RefToNat u])
        , Just (Atom "Ready" [RefAdd n u])
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "binding-aware claim application changed identity/arguments or invented an unsupported source form: " <> show actual
  assert (m /= n) "test fixture accidentally collapsed distinct bindings"

claimDeclarationsPreserveMeaning :: Either String ()
claimDeclarationsPreserveMeaning = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-claim-declarations" declarationSource
  declarations <- mapM claimDeclaration (grammarV1TopLevelDecls sourceFile)
  let x = RefVar (Name "x")
      ok = RefVar (Name "ok")
      actual = map grammarV1ClaimDeclaration declarations
      expected =
        [ Just
            ( "OpaqueFlag"
            , ClaimDecl
                { claimParameters = [(Name "flag", SortBool)]
                , claimDefinition = OpaqueClaim
                }
            )
        , Just
            ( "Positive"
            , ClaimDecl
                { claimParameters = [(Name "x", SortUInt 8)]
                , claimDefinition = TransparentClaim
                    (LessThan (RefNat 0) (RefToNat x))
                }
            )
        , Just
            ( "Mixed"
            , ClaimDecl
                { claimParameters =
                    [ (Name "x", SortUInt 8)
                    , (Name "ok", SortBool)
                    ]
                , claimDefinition = TransparentClaim
                    (Conjunction
                      (LessThan (RefToNat x) (RefNat 7))
                      (Atom "Ready" [ok]))
                }
            )
        , Just
            ( "NoParams"
            , ClaimDecl
                { claimParameters = []
                , claimDefinition = TransparentClaim Truth
                }
            )
        , Just
            ( "EmptyParams"
            , ClaimDecl
                { claimParameters = []
                , claimDefinition = TransparentClaim Truth
                }
            )
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "claim declaration routing changed name/parameter/body meaning or admitted a deferred declaration form: "
      <> show actual

claimRegistrationUsesCoreAuthority :: Either String ()
claimRegistrationUsesCoreAuthority = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-claim-registration" registrationSource
  declarations <- mapM claimDeclaration (grammarV1TopLevelDecls sourceFile)
  case declarations of
    [first, second, duplicate, deferred] -> do
      context1 <- requireRegistered "First" first emptyStaticContext
      context2 <- requireRegistered "Second" second context1
      let firstExpected = ClaimDecl
            { claimParameters = [(Name "x", SortUInt 8)]
            , claimDefinition = OpaqueClaim
            }
          secondExpected = ClaimDecl
            { claimParameters = [(Name "ok", SortBool)]
            , claimDefinition = TransparentClaim
                (Atom "Ready" [RefVar (Name "ok")])
            }
      assert (lookupClaim "First" context2 == Just firstExpected)
        "Core StaticContext did not preserve the exact first registered claim"
      assert (lookupClaim "Second" context2 == Just secondExpected)
        "Core StaticContext did not preserve the exact second registered claim"
      case grammarV1RegisterClaimDeclaration duplicate context2 of
        Just (Left (DuplicateClaim "First")) -> Right ()
        other -> Left
          ("duplicate claim did not reach Core's DuplicateClaim authority: " <> show other)
      case grammarV1RegisterClaimDeclaration deferred context2 of
        Nothing -> Right ()
        other -> Left
          ("deferred generic claim reached Core registration unexpectedly: " <> show other)
    other -> Left
      ("expected four claim declarations for registration pressure, got " <> show (length other))

checkedClaimApplicationsUseCoreAuthority :: Either String ()
checkedClaimApplicationsUseCoreAuthority = do
  declarationFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-checked-claim-declarations" checkedDeclarationSource
  declarations <- mapM claimDeclaration (grammarV1TopLevelDecls declarationFile)
  context0 <- case declarations of
    [positive, flagged] -> do
      context1 <- requireRegistered "Positive" positive emptyStaticContext
      requireRegistered "Flagged" flagged context1
    other -> Left
      ("expected two checked claim declarations, got " <> show (length other))
  context <- mapLeft show $
    declareOpaqueClaim "NeedsNat" [(Name "n", SortNat)] context0
  state1 <- bind "u" Unrestricted (TyUInt 8) emptySurfaceState
  state2 <- bind "ok" Unrestricted TyBool state1
  state <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state2
  applicationFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-checked-claim-applications" checkedApplicationSource
  propositions <- mapM claimProposition (grammarV1TopLevelDecls applicationFile)
  case map (grammarV1CheckedClaimApplication context state) propositions of
    [ positive
      , flagged
      , needsNat
      , unknown
      , wrongSort
      , wrongArity
      , reverseCoercion
      , specialized
      , unresolvedTerm
      ] -> do
        let u = RefVar (Name "u")
            ok = RefVar (Name "ok")
        positiveSteps <- expectCheckedRight
          "transparent Positive"
          (LessThan (RefNat 0) (RefToNat u))
          positive
        assert (ExpandedTransparentClaim "Positive" `elem` positiveSteps)
          "transparent claim application did not record Core expansion"
        _ <- expectCheckedRight "opaque Flagged" (Atom "Flagged" [ok]) flagged
        natSteps <- expectCheckedRight
          "NeedsNat UInt-to-Nat coercion"
          (Atom "NeedsNat" [RefToNat u])
          needsNat
        assert (InsertedUIntToNat u `elem` natSteps)
          "Core claim application did not record required UInt-to-Nat coercion"
        expectCheckedLeft "unknown claim" (UnknownClaim "Missing") unknown
        expectCheckedLeft
          "claim argument sort mismatch"
          (ClaimArgumentSortMismatch "Flagged" 0 SortBool (SortUInt 8))
          wrongSort
        expectCheckedLeft
          "claim arity mismatch"
          (ClaimArityMismatch "Flagged" 1 2)
          wrongArity
        expectCheckedLeft
          "unsupported Nat-to-UInt coercion"
          (ClaimArgumentSortMismatch "Positive" 0 (SortUInt 8) SortNat)
          reverseCoercion
        expectStructuralNothing "specialized claim reference" specialized
        expectStructuralNothing "unresolved claim argument" unresolvedTerm
    other -> Left
      ("expected nine checked claim application results, got " <> show (length other))

semanticClaimDeclarationsUseGeneratedNames :: Either String ()
semanticClaimDeclarationsUseGeneratedNames = do
  source <- onlyClaim "semantic-claim-generated" $
    "claim Mixed(x : U8, ok : Bool) = x < 7 and Ready(ok);"
  checked <- checkedSemanticClaim (DeclarationKey "decl.SemanticClaim") source
  case checkedSemanticClaimParameters checked of
    Just [(xBinder, SortUInt 8), (okBinder, SortBool)] -> do
      let xName@(Name xText) = grammarV1ResolvedBinderCoreName xBinder
          okName@(Name okText) = grammarV1ResolvedBinderCoreName okBinder
          expectedDefinition = TransparentClaim
            (Conjunction
              (LessThan (RefToNat (RefVar xName)) (RefNat 7))
              (Atom "Ready" [RefVar okName]))
          coreDeclaration = checkedSemanticClaimCoreDeclaration checked
      assert
        ( grammarV1ResolvedBinderKind xBinder == GrammarV1ClaimParameterBinder
          && grammarV1ResolvedBinderKind okBinder == GrammarV1ClaimParameterBinder )
        "semantic claim parameters did not retain their distinct binder family"
      assert (xText /= "x" && okText /= "ok")
        "semantic claim Core names collapsed to display spelling"
      assert
        (claimParameters coreDeclaration
          == [(xName, SortUInt 8), (okName, SortBool)])
        "semantic ClaimDecl did not use generated parameter names"
      assert
        (claimDefinition coreDeclaration == expectedDefinition)
        "transparent claim body did not use the generated parameter telescope"
      references <- case checkedSemanticClaimBodyReferences checked of
        Just refs -> Right refs
        Nothing -> Left "transparent semantic claim lost body reference evidence"
      case references of
        [xReference, okReference] -> do
          assert
            ( grammarV1ResolvedBinderKey
                (grammarV1CheckedLexicalReferenceBinder xReference)
              == grammarV1ResolvedBinderKey xBinder )
            "transparent claim lost exact x binder evidence"
          assert
            ( grammarV1ResolvedBinderKey
                (grammarV1CheckedLexicalReferenceBinder okReference)
              == grammarV1ResolvedBinderKey okBinder )
            "transparent claim lost exact ok binder evidence"
        other -> Left
          ("expected two semantic claim body references, got " <> show (length other))
    other -> Left ("unexpected semantic claim parameter shape: " <> show other)

semanticClaimDeclarationsAlphaStable :: Either String ()
semanticClaimDeclarationsAlphaStable = do
  original <- onlyClaim "semantic-claim-alpha-original" $
    "claim Alpha(x : U8, ok : Bool) = x < 7 and Ready(ok);"
  renamed <- onlyClaim "semantic-claim-alpha-renamed" $
    "claim Alpha(count : U8, ready : Bool) = count < 7 and Ready(ready);"
  let declarationKey = DeclarationKey "decl.SemanticClaimAlpha"
  originalChecked <- checkedSemanticClaim declarationKey original
  renamedChecked <- checkedSemanticClaim declarationKey renamed
  originalParameters <- presentSemanticClaimParameters originalChecked
  renamedParameters <- presentSemanticClaimParameters renamedChecked
  assert
    (map (grammarV1ResolvedBinderKey . fst) originalParameters
      == map (grammarV1ResolvedBinderKey . fst) renamedParameters)
    "alpha-renaming changed semantic claim binder keys"
  assert
    (map (grammarV1ResolvedBinderCoreName . fst) originalParameters
      == map (grammarV1ResolvedBinderCoreName . fst) renamedParameters)
    "alpha-renaming changed semantic claim Core names"
  assert
    (checkedSemanticClaimCoreDeclaration originalChecked
      == checkedSemanticClaimCoreDeclaration renamedChecked)
    "alpha-renaming changed semantic ClaimDecl meaning"
  noParams <- onlyClaim "semantic-claim-no-params" "claim NoParams = true;"
  emptyParams <- onlyClaim "semantic-claim-empty-params" "claim EmptyParams() = true;"
  noParamsChecked <- checkedSemanticClaim
    (DeclarationKey "decl.SemanticClaimNoParams") noParams
  emptyParamsChecked <- checkedSemanticClaim
    (DeclarationKey "decl.SemanticClaimEmptyParams") emptyParams
  assert (checkedSemanticClaimParameters noParamsChecked == Nothing)
    "omitted claim parameter syntax was not preserved"
  assert (checkedSemanticClaimParameters emptyParamsChecked == Just [])
    "explicit empty claim parameter syntax was not preserved"
  assert
    ( claimParameters (checkedSemanticClaimCoreDeclaration noParamsChecked) == []
      && claimParameters (checkedSemanticClaimCoreDeclaration emptyParamsChecked) == [] )
    "optional claim source shape leaked into Core parameter semantics"

semanticClaimRegistrationSubstitutesGeneratedFormals :: Either String ()
semanticClaimRegistrationSubstitutesGeneratedFormals = do
  positive <- onlyClaim "semantic-claim-register" $
    "claim Positive(x : U8) = x > 0;"
  let declarationKey = DeclarationKey "decl.SemanticRegisteredPositive"
  context <- case grammarV1RegisterSemanticClaimDeclaration
      declarationKey positive emptyStaticContext of
    Just (Right registered) -> Right registered
    other -> Left ("semantic claim did not register: " <> show other)
  registered <- case lookupClaim "Positive" context of
    Just declaration -> Right declaration
    Nothing -> Left "registered semantic claim was not in Core StaticContext"
  formalName <- case claimParameters registered of
    [(name, SortUInt 8)] -> Right name
    other -> Left ("unexpected registered semantic claim telescope: " <> show other)
  assert (formalName /= Name "x")
    "registered semantic claim retained source spelling as its Core formal"
  state <- bind "u" Unrestricted (TyUInt 8) emptySurfaceState
  application <- onlyClaim "semantic-claim-apply" "claim Apply = Positive(u);"
  proposition <- case grammarV1ClaimProposition application of
    Just located -> Right (locatedValue located)
    Nothing -> Left "semantic claim application fixture had no proposition"
  let u = RefVar (Name "u")
      actual = grammarV1CheckedClaimApplication context state proposition
  steps <- expectCheckedRight
    "semantic registered Positive"
    (LessThan (RefNat 0) (RefToNat u))
    actual
  assert (ExpandedTransparentClaim "Positive" `elem` steps)
    "semantic generated formal was not substituted through Core expansion"

semanticClaimDeclarationBoundaries :: Either String ()
semanticClaimDeclarationBoundaries = do
  duplicate <- onlyClaim "semantic-claim-duplicate" $
    "claim Duplicate(x : U8, x : Bool) = true;"
  let duplicateActual = grammarV1CheckedSemanticClaimDeclaration
        (DeclarationKey "decl.SemanticClaimDuplicate") duplicate
  case duplicateActual of
    Just (Left (GrammarV1SemanticClaimBinderScopeError
      (GrammarV1DuplicateBinder duplicateName previous))) -> do
        assert (locatedValue duplicateName == "x")
          "semantic claim duplicate diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "x")
          "semantic claim duplicate diagnostic lost previous binder"
    other -> Left
      ("expected semantic claim duplicate-binder rejection, got " <> show other)
  generic <- onlyClaim "semantic-claim-generic" $
    "claim Generic[T : Type](x : U8) = true;"
  named <- onlyClaim "semantic-claim-named" $
    "claim Named(x : Widget) = true;"
  let check source = grammarV1CheckedSemanticClaimDeclaration
        (DeclarationKey "decl.SemanticClaimBoundary") source
  assert (check generic == Nothing)
    "generic claim escaped semantic claim competence"
  assert (check named == Nothing)
    "nonprimitive claim parameter escaped semantic claim competence"

checkedSemanticClaim
  :: DeclarationKey
  -> GrammarV1ClaimDecl
  -> Either String GrammarV1CheckedSemanticClaimDeclaration
checkedSemanticClaim declarationKey source =
  case grammarV1CheckedSemanticClaimDeclaration declarationKey source of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked semantic claim declaration, got " <> show other)

presentSemanticClaimParameters
  :: GrammarV1CheckedSemanticClaimDeclaration
  -> Either String [(GrammarV1ResolvedBinder, RefSort)]
presentSemanticClaimParameters checked =
  case checkedSemanticClaimParameters checked of
    Just parameters -> Right parameters
    Nothing -> Left "expected a present semantic claim parameter telescope"

onlyClaim
  :: Text.Text
  -> Text.Text
  -> Either String GrammarV1ClaimDecl
onlyClaim label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [declaration] -> claimDeclaration declaration
    declarations -> Left
      ("expected one claim declaration, got " <> show (length declarations))

expectCheckedRight
  :: String
  -> Proposition
  -> Maybe (Either FocusingError (Proposition, [FocusStep]))
  -> Either String [FocusStep]
expectCheckedRight label expected result =
  case result of
    Just (Right (actual, steps))
      | actual == expected -> Right steps
      | otherwise -> Left
          (label <> " produced wrong canonical proposition: " <> show actual)
    other -> Left (label <> " did not succeed through Core focusing: " <> show other)

expectCheckedLeft
  :: String
  -> FocusingError
  -> Maybe (Either FocusingError (Proposition, [FocusStep]))
  -> Either String ()
expectCheckedLeft label expected result =
  case result of
    Just (Left actual)
      | actual == expected -> Right ()
      | otherwise -> Left (label <> " produced wrong Core rejection: " <> show actual)
    other -> Left (label <> " did not reject through Core focusing: " <> show other)

expectStructuralNothing
  :: String
  -> Maybe (Either FocusingError (Proposition, [FocusStep]))
  -> Either String ()
expectStructuralNothing label result =
  case result of
    Nothing -> Right ()
    other -> Left (label <> " unexpectedly reached Core focusing: " <> show other)

requireRegistered
  :: String
  -> GrammarV1ClaimDecl
  -> StaticContext
  -> Either String StaticContext
requireRegistered label declaration context =
  case grammarV1RegisterClaimDeclaration declaration context of
    Just (Right nextContext) -> Right nextContext
    other -> Left (label <> " did not register successfully: " <> show other)

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

claimProposition
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1Proposition
claimProposition (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl ->
      case grammarV1ClaimProposition claimDecl of
        Just proposition -> Right (locatedValue proposition)
        Nothing -> Left "claim had no proposition"
    other -> Left ("expected claim declaration, got " <> show other)

claimDeclaration
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1ClaimDecl
claimDeclaration (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ClaimDeclaration claimDecl -> Right claimDecl
    other -> Left ("expected claim declaration, got " <> show other)

intrinsicSource :: Text.Text
intrinsicSource = Text.unlines
  [ "claim IntClaim = Ready(7, 0);"
  , "claim BoolClaim = Flag(true, false);"
  , "claim QualifiedClaim = Rules.Ready(1);"
  , "claim ContextClaim(x : U32) = Ready(x);"
  , "claim SpecializedClaim = Ready[U32](1);"
  ]

boundSource :: Text.Text
boundSource = Text.unlines
  [ "claim BoundNat = Ready(n, 1);"
  , "claim BoundBool = Flag(flag, false);"
  , "claim QualifiedClaim = Rules.Ready(n);"
  , "claim GroupedArg = Ready((n));"
  , "claim ArithmeticArg = Ready(n + 1);"
  , "claim SubtractionArg = Ready(n - 1);"
  , "claim ScaleLeftArg = Ready(2 * n);"
  , "claim ScaleRightArg = Ready(n * 2);"
  , "claim LengthArg = Ready(len(bytes));"
  , "claim ExplicitToNatArg = Ready(toNat(u));"
  , "claim MixedSortRaw = Ready(n + u);"
  , "claim Unknown = Ready(missing);"
  , "claim Consumed = Ready(spent);"
  , "claim SpecializedClaim = Ready[U32](n);"
  , "claim CalledArg = Ready(f(1));"
  , "claim ProjectedArg = Ready((n).field);"
  , "claim QualifiedArg = Ready(pkg.n);"
  , "claim SymbolicMultiply = Ready(n * m);"
  , "claim NonClaim = n == 1;"
  ]

declarationSource :: Text.Text
declarationSource = Text.unlines
  [ "claim OpaqueFlag(flag : Bool);"
  , "claim Positive(x : U8) = x > 0;"
  , "claim Mixed(x : U8, ok : Bool) = x < 7 and Ready(ok);"
  , "claim NoParams = true;"
  , "claim EmptyParams() = true;"
  , "claim UnitParam(x : Unit);"
  , "claim BytesParam(x : Bytes[4]);"
  , "claim NamedParam(x : Widget);"
  , "claim Generic[T : Type](x : U8);"
  , "claim Required requires { proposition true; } (x : U8);"
  , "claim Duplicate(x : U8, x : U8);"
  , "claim BadBody(x : U8) = missing < x;"
  ]

registrationSource :: Text.Text
registrationSource = Text.unlines
  [ "claim First(x : U8);"
  , "claim Second(ok : Bool) = Ready(ok);"
  , "claim First(flag : Bool);"
  , "claim Deferred[T : Type](x : U8);"
  ]

checkedDeclarationSource :: Text.Text
checkedDeclarationSource = Text.unlines
  [ "claim Positive(x : U8) = x > 0;"
  , "claim Flagged(ok : Bool);"
  ]

checkedApplicationSource :: Text.Text
checkedApplicationSource = Text.unlines
  [ "claim ApplyPositive = Positive(u);"
  , "claim ApplyFlagged = Flagged(ok);"
  , "claim ApplyNeedsNat = NeedsNat(u);"
  , "claim ApplyMissing = Missing(u);"
  , "claim ApplyWrongSort = Flagged(u);"
  , "claim ApplyWrongArity = Flagged(ok, ok);"
  , "claim ApplyReverseCoercion = Positive(n);"
  , "claim ApplySpecialized = Flagged[Bool](ok);"
  , "claim ApplyUnresolvedTerm = Flagged(missing);"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right