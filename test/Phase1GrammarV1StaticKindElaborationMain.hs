{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
import Phil.Core.Static (SemanticForm (..))
import Phil.Surface.GrammarV1.Elaborate
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 generic parameter kinds route exactly to GEN-013"
        genericKindsRouteExactly
    , test "SURF-008 name-shaped static actual stays one reference until expected-kind resolution"
        expectedKindResolvesNameShapedActual
    , test "SURF-008 specialized static reference stays fail-closed in the bare-reference bridge"
        specializedReferenceDoesNotFlatten
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

genericKindsRouteExactly :: Either String ()
genericKindsRouteExactly = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-static-kinds" kindSource
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1RecordDeclaration recordDecl -> do
        let actual =
              [ grammarV1GenericKindCategory (locatedValue (grammarV1GenericParamKind param))
              | Located _ param <- grammarV1RecordGenericParams recordDecl
              ]
            expected =
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
        assert (actual == expected) $
          "generic kind routing changed category/order: " <> show actual
      other -> Left ("expected record declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))
  where
    kindSource = Text.unlines
      [ "record KindMap["
      , "  T : Type,"
      , "  N : Nat,"
      , "  S : Session,"
      , "  M : Message,"
      , "  E : Effects,"
      , "  P : provider Store,"
      , "  C : callable Worker,"
      , "  B : boundary Wire,"
      , "  A : architecture Cluster"
      , "] {"
      , "  value : T"
      , "}"
      ]

expectedKindResolvesNameShapedActual :: Either String ()
expectedKindResolvesNameShapedActual = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-static-reference" referenceSource
  case grammarV1TopLevelDecls sourceFile of
    [providerTop, callableTop, _] -> do
      (providerParameter, providerActual) <- aliasRoute "P" providerTop
      (callableParameter, callableActual) <- aliasRoute "C" callableTop
      assert
        ( providerActual == ReferencedGenericStaticActual "shared"
          && callableActual == ReferencedGenericStaticActual "shared" )
        "same name-shaped source actual did not remain the same unresolved reference"
      providerChecked <- mapLeft show $ checkGenericStaticActuals
        [providerParameter] [providerActual] sharedCandidates
      callableChecked <- mapLeft show $ checkGenericStaticActuals
        [callableParameter] [callableActual] sharedCandidates
      assert
        (map checkedGenericStaticSemanticForm providerChecked == [SemanticAtom "provider.shared"])
        "provider expected kind did not select provider.shared"
      assert
        (map checkedGenericStaticSemanticForm callableChecked == [SemanticAtom "callable.shared"])
        "callable expected kind did not select callable.shared"
    declarations -> Left ("expected three aliases, got " <> show (length declarations))

specializedReferenceDoesNotFlatten :: Either String ()
specializedReferenceDoesNotFlatten = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-specialized-reference" referenceSource
  case grammarV1TopLevelDecls sourceFile of
    [_, _, specializedTop] -> do
      argument <- aliasArgument specializedTop
      assert
        (grammarV1BareStaticReferenceActual argument == Nothing)
        "specialized static reference was flattened into the bare-reference bridge"
    declarations -> Left ("expected three aliases, got " <> show (length declarations))

referenceSource :: Text
referenceSource = Text.unlines
  [ "type ProviderUse[P : provider Store] = Box[shared];"
  , "type CallableUse[C : callable Worker] = Box[shared];"
  , "type Specialized[P : provider Store] = Box[shared[U32]];"
  ]

aliasRoute
  :: Text
  -> Located GrammarV1TopLevelDecl
  -> Either String (GenericStaticParameter, GenericStaticActual)
aliasRoute expectedParameter topLevel = do
  aliasDecl <- aliasDeclaration topLevel
  parameter <- case grammarV1TypeAliasGenericParams aliasDecl of
    [Located _ value] -> Right value
    values -> Left ("expected one generic parameter, got " <> show (length values))
  let parameterName = locatedValue (grammarV1GenericParamName parameter)
  assert (parameterName == expectedParameter) $
    "expected parameter " <> Text.unpack expectedParameter <> ", got " <> Text.unpack parameterName
  argument <- aliasArgument topLevel
  actual <- maybe
    (Left "name-shaped static argument was not preserved by the bare-reference bridge")
    Right
    (grammarV1BareStaticReferenceActual argument)
  let kind = grammarV1GenericKindCategory (locatedValue (grammarV1GenericParamKind parameter))
  Right
    ( GenericStaticParameter (GenericStaticParameterKey parameterName) kind
    , actual
    )

aliasArgument :: Located GrammarV1TopLevelDecl -> Either String GrammarV1StaticArgument
aliasArgument topLevel = do
  aliasDecl <- aliasDeclaration topLevel
  case locatedValue (grammarV1TypeAliasTarget aliasDecl) of
    GrammarV1NamedType reference ->
      case grammarV1StaticReferenceArguments reference of
        [argument] -> Right argument
        arguments -> Left ("expected one static argument, got " <> show (length arguments))
    other -> Left ("expected named alias target, got " <> show other)

aliasDeclaration :: Located GrammarV1TopLevelDecl -> Either String GrammarV1TypeAliasDecl
aliasDeclaration (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl -> Right aliasDecl
    other -> Left ("expected type alias declaration, got " <> show other)

sharedCandidates :: [GenericStaticReferenceCandidate]
sharedCandidates =
  [ candidate "shared" GenericCallableContractKind "callable.shared"
  , candidate "shared" GenericProviderContractKind "provider.shared"
  ]

candidate :: Text -> GenericStaticKind -> Text -> GenericStaticReferenceCandidate
candidate name kind semantic = GenericStaticReferenceCandidate
  { genericStaticReferenceName = name
  , genericStaticReferenceKind = kind
  , genericStaticReferenceSemanticForm = SemanticAtom semantic
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
