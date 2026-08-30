{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-002 provider declaration family preserves exact forms" providerFamilyPreserved
    , test "SURF-002 provider contract item missing semicolon rejects" $
        expectReject "provider P { law L : true }"
    , test "SURF-002 provider implementation operation requires satisfies" $
        expectReject "provider implementation P satisfies C { operation op C {} }"
    , test "SURF-002 opaque provider implementation rejects a body" $
        expectReject "opaque provider implementation P satisfies C {}"
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

providerFamilyPreserved :: Either String ()
providerFamilyPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "providers" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ contractTop, Located _ implementationTop, Located _ opaqueTop] -> do
      case locatedValue (grammarV1Declaration contractTop) of
        GrammarV1ProviderContractDeclaration contractDecl -> checkContract contractDecl
        other -> Left ("expected provider contract first, got " <> show other)
      case locatedValue (grammarV1Declaration implementationTop) of
        GrammarV1ProviderImplementationDeclaration implementationDecl ->
          checkImplementation implementationDecl
        other -> Left ("expected provider implementation second, got " <> show other)
      case locatedValue (grammarV1Declaration opaqueTop) of
        GrammarV1OpaqueProviderImplementationDeclaration opaqueDecl -> checkOpaque opaqueDecl
        other -> Left ("expected opaque provider implementation third, got " <> show other)
    declarations -> Left ("expected three provider declarations, got " <> show (length declarations))
  where
    source = Text.unlines
      [ "provider Store[T : Type] requires { proposition true; } {"
      , "  operation put : Put;"
      , "  law coherent : true;"
      , "  lifecycle alive : true;"
      , "}"
      , "provider implementation MemStore[T : Type] requires { proposition true; } satisfies Store[T] {"
      , "  operation put satisfies Put { return unit }"
      , "  law coherent = true;"
      , "  lifecycle alive = true;"
      , "}"
      , "opaque provider implementation RemoteStore satisfies Store[U32];"
      ]

checkContract :: GrammarV1ProviderContractDecl -> Either String ()
checkContract contractDecl = do
  assert (locatedValue (grammarV1ProviderContractName contractDecl) == "Store")
    "provider contract name was not Store"
  assertTypeGeneric (grammarV1ProviderContractGenericParams contractDecl)
  assert (length (grammarV1ProviderContractRequirements contractDecl) == 1)
    "provider contract generic requirement was not preserved"
  case grammarV1ProviderContractItems contractDecl of
    [ Located _ (GrammarV1ProviderContractOperation operationName operationType)
      , Located _ (GrammarV1ProviderContractLaw lawName lawProposition)
      , Located _ (GrammarV1ProviderContractLifecycle lifecycleName lifecycleProposition)
      ] -> do
        assert (locatedValue operationName == "put") "provider operation was not put"
        assert (namedTypeNamed ["Put"] operationType) "provider operation type was not Put"
        assert (locatedValue lawName == "coherent") "provider law was not coherent"
        assert (locatedValue lawProposition == GrammarV1TrueProposition)
          "provider law proposition was not true"
        assert (locatedValue lifecycleName == "alive") "provider lifecycle was not alive"
        assert (locatedValue lifecycleProposition == GrammarV1TrueProposition)
          "provider lifecycle proposition was not true"
    items -> Left ("unexpected provider contract items " <> show items)

checkImplementation :: GrammarV1ProviderImplementationDecl -> Either String ()
checkImplementation implementationDecl = do
  assert (locatedValue (grammarV1ProviderImplementationName implementationDecl) == "MemStore")
    "provider implementation name was not MemStore"
  assertTypeGeneric (grammarV1ProviderImplementationGenericParams implementationDecl)
  assert (length (grammarV1ProviderImplementationRequirements implementationDecl) == 1)
    "provider implementation generic requirement was not preserved"
  assert (namedTypeWithReferenceActual "Store" "T" (grammarV1ProviderImplementationSatisfies implementationDecl))
    "provider implementation satisfies type was not Store[T]"
  case grammarV1ProviderImplementationItems implementationDecl of
    [ Located _ (GrammarV1ProviderImplementationOperation operationName operationType body)
      , Located _ (GrammarV1ProviderImplementationLaw lawName lawProposition)
      , Located _ (GrammarV1ProviderImplementationLifecycle lifecycleName lifecycleProposition)
      ] -> do
        assert (locatedValue operationName == "put") "implementation operation was not put"
        assert (namedTypeNamed ["Put"] operationType) "implementation operation type was not Put"
        assert (returnsUnit body) "implementation operation body did not return unit"
        assert (locatedValue lawName == "coherent") "implementation law was not coherent"
        assert (locatedValue lawProposition == GrammarV1TrueProposition)
          "implementation law proposition was not true"
        assert (locatedValue lifecycleName == "alive") "implementation lifecycle was not alive"
        assert (locatedValue lifecycleProposition == GrammarV1TrueProposition)
          "implementation lifecycle proposition was not true"
    items -> Left ("unexpected provider implementation items " <> show items)

checkOpaque :: GrammarV1OpaqueProviderImplementationDecl -> Either String ()
checkOpaque opaqueDecl = do
  assert (locatedValue (grammarV1OpaqueProviderImplementationName opaqueDecl) == "RemoteStore")
    "opaque provider implementation name was not RemoteStore"
  assert (null (grammarV1OpaqueProviderImplementationGenericParams opaqueDecl))
    "opaque provider unexpectedly acquired generic parameters"
  assert (null (grammarV1OpaqueProviderImplementationRequirements opaqueDecl))
    "opaque provider unexpectedly acquired generic requirements"
  assert (namedTypeWithTypeActual "Store" (GrammarV1UnsignedType "U32")
    (grammarV1OpaqueProviderImplementationSatisfies opaqueDecl))
    "opaque provider satisfies type was not Store[U32]"

assertTypeGeneric :: [Located GrammarV1GenericParam] -> Either String ()
assertTypeGeneric params = case params of
  [Located _ param] -> do
    assert (locatedValue (grammarV1GenericParamName param) == "T")
      "provider generic parameter was not T"
    assert (locatedValue (grammarV1GenericParamKind param) == GrammarV1TypeKind)
      "provider generic parameter kind was not Type"
  other -> Left ("expected one provider generic parameter, got " <> show other)

namedTypeNamed :: [Text.Text] -> Located GrammarV1Type -> Bool
namedTypeNamed expected (Located _ ty) = case ty of
  GrammarV1NamedType reference ->
    grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == expected
      && null (grammarV1StaticReferenceArguments reference)
  _ -> False

namedTypeWithReferenceActual
  :: Text.Text
  -> Text.Text
  -> Located GrammarV1Type
  -> Bool
namedTypeWithReferenceActual expectedName expectedActual (Located _ ty) = case ty of
  GrammarV1NamedType reference ->
    grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedName]
      && grammarV1StaticReferenceArguments reference ==
        [ GrammarV1StaticReferenceArgument
            (GrammarV1StaticReference
              { grammarV1StaticReferenceName = GrammarV1QualifiedName [expectedActual]
              , grammarV1StaticReferenceArguments = []
              })
        ]
  _ -> False

namedTypeWithTypeActual
  :: Text.Text
  -> GrammarV1Type
  -> Located GrammarV1Type
  -> Bool
namedTypeWithTypeActual expectedName expectedActual (Located _ ty) = case ty of
  GrammarV1NamedType reference ->
    grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedName]
      && grammarV1StaticReferenceArguments reference == [GrammarV1StaticTypeArgument expectedActual]
  _ -> False

returnsUnit :: Located GrammarV1Block -> Bool
returnsUnit (Located _ block) = case grammarV1BlockStatements block of
  [Located _ (GrammarV1ReturnStatement (Located _ GrammarV1UnitExpression))] -> True
  _ -> False

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "provider-reject" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
