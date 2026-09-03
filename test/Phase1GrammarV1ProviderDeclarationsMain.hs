{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.ProviderQualification
  ( ProviderOperationKey (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax (Proposition (..))
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProviderContractSurface
  ( GrammarV1CheckedProviderContractSurface (..)
  , grammarV1CheckedClosedProviderContractSurface
  )
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
    , test "SURF-008 closed provider contract surface preserves stable identity, operation references, laws, and lifecycle"
        closedProviderContractSurface
    , test "SURF-008 provider contract proposition Core failures remain distinct from source non-competence"
        providerContractCoreFailure
    , test "SURF-008 provider operation duplicate spelling remains visible before competent contract construction"
        providerContractDuplicateOperationVisibility
    , test "SURF-008 generic, specialized, structured, and unresolved provider contract forms remain fail-closed"
        providerContractCompetenceBoundaries
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
      , "  operation put satisfies Put { return unit; }"
      , "  law coherent = true;"
      , "  lifecycle alive = true;"
      , "}"
      , "opaque provider implementation RemoteStore satisfies Store[U32];"
      ]

closedProviderContractSurface :: Either String ()
closedProviderContractSurface = do
  provider <- onlyProviderContract $ Text.unlines
    [ "provider Store {"
    , "  operation read : api.Reader;"
    , "  law coherent : true;"
    , "  operation write : Writer;"
    , "  lifecycle alive : false;"
    , "}"
    ]
  renamed <- onlyProviderContract $ Text.unlines
    [ "provider RenamedPresentation {"
    , "  operation read : api.Reader;"
    , "  law coherent : true;"
    , "  operation write : Writer;"
    , "  lifecycle alive : false;"
    , "}"
    ]
  let declarationKey = DeclarationKey "provider.stable.store"
      interfaceRevision = InterfaceRevision "provider.interface.v1"
      expected = GrammarV1CheckedProviderContractSurface
        { checkedProviderDeclarationKey = declarationKey
        , checkedProviderInterfaceRevision = interfaceRevision
        , checkedProviderOperationReferences =
            [ (ProviderOperationKey "read", ReferencedGenericStaticActual "api.Reader")
            , (ProviderOperationKey "write", ReferencedGenericStaticActual "Writer")
            ]
        , checkedProviderLaws = [("coherent", Truth, [])]
        , checkedProviderLifecycle = [("alive", Falsehood, [])]
        }
  assert
    ( grammarV1CheckedClosedProviderContractSurface
        emptyStaticContext
        declarationKey
        interfaceRevision
        provider
        == Just (Right expected)
    )
    "closed provider contract surface did not preserve exact semantic categories"
  assert
    ( grammarV1CheckedClosedProviderContractSurface
        emptyStaticContext
        declarationKey
        interfaceRevision
        renamed
        == Just (Right expected)
    )
    "provider display-name change leaked into stable declaration/interface identity"

providerContractCoreFailure :: Either String ()
providerContractCoreFailure = do
  provider <- onlyProviderContract $ Text.unlines
    [ "provider BadClaim {"
    , "  operation read : Reader;"
    , "  law bad : Missing();"
    , "}"
    ]
  let declarationKey = DeclarationKey "provider.stable.bad-claim"
      interfaceRevision = InterfaceRevision "provider.interface.bad-claim"
  assert
    ( grammarV1CheckedClosedProviderContractSurface
        emptyStaticContext
        declarationKey
        interfaceRevision
        provider
        == Just (Left (UnknownClaim "Missing"))
    )
    "provider law Core UnknownClaim collapsed into source non-competence"

providerContractDuplicateOperationVisibility :: Either String ()
providerContractDuplicateOperationVisibility = do
  provider <- onlyProviderContract $ Text.unlines
    [ "provider Duplicate {"
    , "  operation access : Reader;"
    , "  operation access : Writer;"
    , "}"
    ]
  let declarationKey = DeclarationKey "provider.stable.duplicate"
      interfaceRevision = InterfaceRevision "provider.interface.duplicate"
  case grammarV1CheckedClosedProviderContractSurface
      emptyStaticContext declarationKey interfaceRevision provider of
    Just (Right checked) ->
      assert
        ( checkedProviderOperationReferences checked
            == [ (ProviderOperationKey "access", ReferencedGenericStaticActual "Reader")
               , (ProviderOperationKey "access", ReferencedGenericStaticActual "Writer")
               ]
        )
        "provider operation duplicate spelling was normalized before competent uniqueness checking"
    other -> Left ("duplicate operation visibility changed unexpectedly: " <> show other)

providerContractCompetenceBoundaries :: Either String ()
providerContractCompetenceBoundaries = do
  specialized <- onlyProviderContract
    "provider Specialized { operation read : Reader[U8]; }"
  structured <- onlyProviderContract
    "provider Structured { operation read : U8; }"
  generic <- onlyProviderContract
    "provider Generic[T : Type] { operation read : Reader; }"
  required <- onlyProviderContract
    "provider Required requires { proposition true; } { operation read : Reader; }"
  unresolved <- onlyProviderContract $ Text.unlines
    [ "provider Unresolved {"
    , "  operation read : Reader;"
    , "  lifecycle indexed : n == 0;"
    , "}"
    ]
  let declarationKey = DeclarationKey "provider.stable.boundary"
      interfaceRevision = InterfaceRevision "provider.interface.boundary"
      project = grammarV1CheckedClosedProviderContractSurface
        emptyStaticContext declarationKey interfaceRevision
  assert (project specialized == Nothing)
    "specialized provider operation callable reference was flattened to its base spelling"
  assert (project structured == Nothing)
    "structured provider operation type was reinterpreted as a callable contract reference"
  assert (project generic == Nothing)
    "generic provider contract escaped the closed-provider competence wall"
  assert (project required == Nothing)
    "requirement-bearing provider contract escaped the closed-provider competence wall"
  assert (project unresolved == Nothing)
    "free provider lifecycle proposition acquired an invented top-level binding"

onlyProviderContract :: Text.Text -> Either String GrammarV1ProviderContractDecl
onlyProviderContract source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-provider-contract" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProviderContractDeclaration provider -> Right provider
      other -> Left ("expected provider contract declaration, got " <> show other)
    declarations -> Left
      ("expected one provider contract declaration, got " <> show (length declarations))

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
