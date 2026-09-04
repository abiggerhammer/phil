{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic (GenericStaticParameterKey)
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.CallableEffects
  ( GrammarV1CallableEffectBoundTemplate (..)
  , GrammarV1ResolvedCallableEffectUse (..)
  , GrammarV1ResolvedCallableEffectsParameter (..)
  , grammarV1ResolvedCallableEffectBounds
  )
import Phil.Surface.GrammarV1.GenericBinderScope
  ( GrammarV1GenericBinderScopeError (..)
  , GrammarV1ResolvedGenericParameter (..)
  , grammarV1BindGenericParameters
  , grammarV1CallableGenericParameterScope
  , grammarV1FunctionGenericParameterScope
  , grammarV1ResolveGenericParameter
  , grammarV1RootGenericBinderScope
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax
  ( Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 function generic keys are alpha- and source-span-stable"
        functionGenericIdentityIsAlphaStable
    , test "SURF-009 generic binder authority preserves every Core static kind"
        allGenericKindsAreExact
    , test "SURF-009 duplicate generic parameter spellings reject"
        duplicateGenericParameterRejects
    , test "SURF-009 declaration roots separate equal generic ordinals"
        declarationRootsSeparateGenericIdentity
    , test "SURF-009 generic lookup returns exact semantic parameter and rejects absence"
        genericLookupIsExact
    , test "SURF-009 resolved generic identity feeds callable Effects without spelling-derived keys"
        genericIdentityFeedsCallableEffects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

functionGenericIdentityIsAlphaStable :: Either String ()
functionGenericIdentityIsAlphaStable = do
  original <- onlyFunction $ Text.unlines
    [ "fn generic_scope[T : Type, n : Nat](x : U8) -> U8 satisfies C {"
    , "  return x;"
    , "}"
    ]
  renamed <- onlyFunction $ Text.unlines
    [ "fn generic_scope[Element : Type, count : Nat](x : U8) -> U8 satisfies C {"
    , "      return x;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.GenericScope"
  (originalBinders, _) <- mapLeft show $
    grammarV1FunctionGenericParameterScope declarationKey original
  (renamedBinders, _) <- mapLeft show $
    grammarV1FunctionGenericParameterScope declarationKey renamed
  assert
    (map genericKey originalBinders == map genericKey renamedBinders)
    "alpha-renaming/source movement changed GenericStaticParameterKeys"
  assert
    (map genericKind originalBinders == [GenericTypeKind, GenericIndexKind])
    "original generic kinds were not Type/Nat"
  assert
    (map genericKind renamedBinders == [GenericTypeKind, GenericIndexKind])
    "renamed generic kinds were not Type/Nat"
  assert
    (map genericDisplayName originalBinders == ["T", "n"])
    "original generic display spellings changed"
  assert
    (map genericDisplayName renamedBinders == ["Element", "count"])
    "renamed generic display spellings changed"

allGenericKindsAreExact :: Either String ()
allGenericKindsAreExact = do
  let sourceParameters =
        [ genericParameter 1 "T" GrammarV1TypeKind
        , genericParameter 2 "n" GrammarV1NatKind
        , genericParameter 3 "S" GrammarV1SessionKind
        , genericParameter 4 "M" GrammarV1MessageKind
        , genericParameter 5 "E" GrammarV1EffectsKind
        , genericParameter 6 "P" (GrammarV1ProviderKind GrammarV1UnitType)
        , genericParameter 7 "C" (GrammarV1CallableKind GrammarV1UnitType)
        , genericParameter 8 "B" (GrammarV1BoundaryKind GrammarV1UnitType)
        , genericParameter 9 "A" (GrammarV1ArchitectureKind GrammarV1UnitType)
        ]
      expectedKinds =
        [ GenericTypeKind
        , GenericIndexKind
        , GenericSessionKind
        , GenericMessageKind
        , GenericEffectsKind
        , GenericProviderContractKind
        , GenericCallableContractKind
        , GenericBoundaryContractKind
        , GenericArchitectureDependencyKind
        ]
  (resolved, _) <- mapLeft show $
    grammarV1BindGenericParameters
      sourceParameters
      (grammarV1RootGenericBinderScope (DeclarationKey "decl.AllKinds"))
  assert
    (map genericKind resolved == expectedKinds)
    "generic binder authority reinterpreted one or more Core static kinds"
  assert
    (length (unique (map genericKey resolved)) == length expectedKinds)
    "distinct telescope positions reused a GenericStaticParameterKey"

duplicateGenericParameterRejects :: Either String ()
duplicateGenericParameterRejects = do
  functionDecl <- onlyFunction
    "fn duplicate[T : Type, T : Nat](x : U8) -> U8 satisfies C { return x; }"
  case grammarV1FunctionGenericParameterScope
      (DeclarationKey "decl.DuplicateGeneric")
      functionDecl of
    Left (GrammarV1DuplicateGenericBinder duplicate previous) -> do
      assert (locatedValue duplicate == "T")
        "duplicate-generic diagnostic lost source spelling"
      assert (genericDisplayName previous == "T")
        "duplicate-generic diagnostic lost first binder"
    other -> Left ("expected duplicate generic-binder rejection, got " <> show other)

declarationRootsSeparateGenericIdentity :: Either String ()
declarationRootsSeparateGenericIdentity = do
  functionDecl <- onlyFunction
    "fn rooted[T : Type](x : U8) -> U8 satisfies C { return x; }"
  (leftBinders, _) <- mapLeft show $
    grammarV1FunctionGenericParameterScope (DeclarationKey "decl.Left") functionDecl
  (rightBinders, _) <- mapLeft show $
    grammarV1FunctionGenericParameterScope (DeclarationKey "decl.Right") functionDecl
  left <- exactlyOne "left generic binder" leftBinders
  right <- exactlyOne "right generic binder" rightBinders
  assert (genericKey left /= genericKey right)
    "different declaration roots reused one GenericStaticParameterKey"

genericLookupIsExact :: Either String ()
genericLookupIsExact = do
  let parameters =
        [ genericParameter 1 "T" GrammarV1TypeKind
        , genericParameter 2 "E" GrammarV1EffectsKind
        ]
  (resolved, scope) <- mapLeft show $
    grammarV1BindGenericParameters
      parameters
      (grammarV1RootGenericBinderScope (DeclarationKey "decl.Lookup"))
  expected <- case resolved of
    [_t, e] -> Right e
    other -> Left ("expected two generic binders, got " <> show other)
  actual <- mapLeft show $
    grammarV1ResolveGenericParameter (Located (spanAt 80) "E") scope
  assert (genericKey actual == genericKey expected)
    "generic lookup returned a different semantic identity"
  case grammarV1ResolveGenericParameter (Located (spanAt 81) "missing") scope of
    Left (GrammarV1GenericBinderNotInScope missing) ->
      assert (locatedValue missing == "missing")
        "missing-generic diagnostic changed source spelling"
    other -> Left ("expected missing generic-binder rejection, got " <> show other)

genericIdentityFeedsCallableEffects :: Either String ()
genericIdentityFeedsCallableEffects = do
  callable <- onlyCallable $ Text.unlines
    [ "callable GenericEffects[E : Effects, T : Type]() -> Unit {"
    , "  effects E;"
    , "}"
    ]
  (resolvedParameters, scope) <- mapLeft show $
    grammarV1CallableGenericParameterScope
      (DeclarationKey "decl.GenericEffects")
      callable
  sourceUse <- case
      [ effectSet
      | Located _ (GrammarV1CallableEffects effectSet) <- grammarV1CallableClauses callable
      ] of
    [use] -> Right use
    uses -> Left ("expected one Effects use, got " <> show (length uses))
  sourceName <- case locatedValue sourceUse of
    GrammarV1EffectSetReference reference ->
      case grammarV1QualifiedNameParts
          (grammarV1StaticReferenceName (locatedValue reference)) of
        [name] -> Right (Located (locatedSpan reference) name)
        parts -> Left ("expected bare Effects parameter reference, got " <> show parts)
    other -> Left ("expected Effects parameter reference, got " <> show other)
  resolvedUse <- mapLeft show $ grammarV1ResolveGenericParameter sourceName scope
  resolvedE <- case
      [ resolved
      | resolved <- resolvedParameters
      , genericDisplayName resolved == "E"
      ] of
    [resolved] -> Right resolved
    matches -> Left ("expected one resolved E parameter, got " <> show (length matches))
  assert (genericKey resolvedUse == genericKey resolvedE)
    "Effects source use did not resolve to the exact generic binder"
  let parameterEvidence = GrammarV1ResolvedCallableEffectsParameter
        { resolvedCallableEffectsSourceParameter = grammarV1ResolvedGenericSource resolvedE
        , resolvedCallableEffectsParameter = grammarV1ResolvedGenericParameter resolvedE
        }
      useEvidence = GrammarV1ResolvedCallableEffectUse
        { resolvedCallableEffectSourceUse = sourceUse
        , resolvedCallableEffectUseParameterKey = genericKey resolvedUse
        }
      expected =
        [GrammarV1CallableEffectsParameterBound (genericKey resolvedE)]
  assert
    ( grammarV1ResolvedCallableEffectBounds
        [parameterEvidence]
        [useEvidence]
        callable
        == Just (Right expected)
    )
    "callable Effects bridge did not consume the resolver-issued static identity"

genericParameter
  :: Int
  -> Text.Text
  -> GrammarV1GenericKind
  -> Located GrammarV1GenericParam
genericParameter line name kind =
  let sourceSpan = spanAt line
  in Located sourceSpan GrammarV1GenericParam
      { grammarV1GenericParamName = Located sourceSpan name
      , grammarV1GenericParamKind = Located sourceSpan kind
      }

spanAt :: Int -> SourceSpan
spanAt line = SourceSpan point point
  where
    point = SourcePoint
      { sourcePointFile = "generic-binder-scope"
      , sourcePointLine = line
      , sourcePointColumn = 1
      , sourcePointOffset = line * 10
      }

genericKey :: GrammarV1ResolvedGenericParameter -> GenericStaticParameterKey
genericKey = genericStaticParameterKey . grammarV1ResolvedGenericParameter

genericKind :: GrammarV1ResolvedGenericParameter -> GenericStaticKind
genericKind = genericStaticParameterKind . grammarV1ResolvedGenericParameter

genericDisplayName :: GrammarV1ResolvedGenericParameter -> Text.Text
genericDisplayName =
  locatedValue
  . grammarV1GenericParamName
  . locatedValue
  . grammarV1ResolvedGenericSource

onlyFunction :: Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "generic-binder-scope" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left ("expected one function declaration, got " <> show (length declarations))

onlyCallable :: Text.Text -> Either String GrammarV1CallableContractDecl
onlyCallable source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "generic-binder-scope" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CallableContractDeclaration callable -> Right callable
      other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left ("expected one callable declaration, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left ("expected exactly one " <> label <> ", got " <> show (length values))

unique :: Eq a => [a] -> [a]
unique [] = []
unique (first : rest) = first : unique (filter (/= first) rest)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
