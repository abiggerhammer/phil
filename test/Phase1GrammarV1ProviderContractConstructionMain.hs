{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Callable
  ( CallableContract (..)
  , CalleeTransition (..)
  )
import Phil.Core.CallableRefinement
  ( CallableMachineShape (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.ProviderQualification
  ( ProviderContract (..)
  , ProviderOperationContract (..)
  , ProviderOperationKey (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProviderContractSurface
  ( GrammarV1CheckedProviderContractSurface
  , GrammarV1ProviderContractConstructionError (..)
  , GrammarV1ResolvedProviderContract (..)
  , GrammarV1ResolvedProviderOperation (..)
  , grammarV1CheckedClosedProviderContractSurface
  , grammarV1ConstructClosedProviderContract
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 exact resolved provider operations construct Core ProviderContract"
        exactProviderContractConstruction
    , test "SURF-008 provider resolution evidence must preserve exact source key/reference order"
        providerResolutionShapeIsExact
    , test "SURF-008 duplicate provider operation keys reject before Map construction"
        duplicateProviderOperationRejects
    , test "SURF-008 provider display rename remains nonsemantic through Core contract construction"
        providerRenameRemainsNonsemantic
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactProviderContractConstruction :: Either String ()
exactProviderContractConstruction = do
  surface <- checkedSurface "Store" standardProviderBody
  let readContract = operationContract "read"
      writeContract = operationContract "write"
      resolutions =
        [ resolution "read" "api.Reader" readContract
        , resolution "write" "Writer" writeContract
        ]
      expectedCore = ProviderContract
        { providerContractInterfaceRevision = providerInterface
        , providerContractOperations = Map.fromList
            [ (ProviderOperationKey "read", readContract)
            , (ProviderOperationKey "write", writeContract)
            ]
        }
  case grammarV1ConstructClosedProviderContract surface resolutions of
    Right checked -> do
      assert (resolvedProviderDeclarationKey checked == providerDeclaration)
        "provider declaration lineage was not preserved"
      assert (resolvedProviderCoreContract checked == expectedCore)
        "Core ProviderContract did not preserve exact interface/operation contracts"
      assert (resolvedProviderLaws checked == checkedProviderLaws surface)
        "checked provider laws were dropped during Core contract construction"
      assert (resolvedProviderLifecycle checked == checkedProviderLifecycle surface)
        "checked provider lifecycle was dropped during Core contract construction"
    Left err -> Left ("exact provider construction rejected: " <> show err)

providerResolutionShapeIsExact :: Either String ()
providerResolutionShapeIsExact = do
  surface <- checkedSurface "Store" standardProviderBody
  let readContract = operationContract "read"
      writeContract = operationContract "write"
      readResolution = resolution "read" "api.Reader" readContract
      writeResolution = resolution "write" "Writer" writeContract
      wrongReference = resolution "read" "Writer" readContract
  assert
    ( grammarV1ConstructClosedProviderContract surface [writeResolution, readResolution]
        == Left
          (ProviderOperationResolutionMismatch
            0
            (ProviderOperationKey "read")
            (ReferencedGenericStaticActual "api.Reader")
            (ProviderOperationKey "write")
            (ReferencedGenericStaticActual "Writer"))
    )
    "reordered provider resolution evidence was accepted"
  assert
    ( grammarV1ConstructClosedProviderContract surface [readResolution]
        == Left (ProviderOperationResolutionCountMismatch 2 1)
    )
    "missing provider resolution evidence was accepted"
  assert
    ( grammarV1ConstructClosedProviderContract
        surface
        [ readResolution
        , writeResolution
        , resolution "extra" "Extra" (operationContract "extra")
        ]
        == Left (ProviderOperationResolutionCountMismatch 2 3)
    )
    "extra provider resolution evidence was accepted"
  assert
    ( grammarV1ConstructClosedProviderContract surface [wrongReference, writeResolution]
        == Left
          (ProviderOperationResolutionMismatch
            0
            (ProviderOperationKey "read")
            (ReferencedGenericStaticActual "api.Reader")
            (ProviderOperationKey "read")
            (ReferencedGenericStaticActual "Writer"))
    )
    "provider resolution evidence was allowed to change the unresolved callable identity"

duplicateProviderOperationRejects :: Either String ()
duplicateProviderOperationRejects = do
  surface <- checkedSurface "Duplicate" $ Text.unlines
    [ "  operation access : Reader;"
    , "  operation access : Writer;"
    ]
  let resolutions =
        [ resolution "access" "Reader" (operationContract "reader")
        , resolution "access" "Writer" (operationContract "writer")
        ]
  assert
    ( grammarV1ConstructClosedProviderContract surface resolutions
        == Left (ProviderContractDuplicateOperationKey (ProviderOperationKey "access"))
    )
    "duplicate provider operation key was silently normalized/overwritten by Map construction"

providerRenameRemainsNonsemantic :: Either String ()
providerRenameRemainsNonsemantic = do
  original <- checkedSurface "Store" standardProviderBody
  renamed <- checkedSurface "PresentationOnlyRename" standardProviderBody
  let resolutions =
        [ resolution "read" "api.Reader" (operationContract "read")
        , resolution "write" "Writer" (operationContract "write")
        ]
  assert
    (grammarV1ConstructClosedProviderContract original resolutions
      == grammarV1ConstructClosedProviderContract renamed resolutions)
    "provider display rename changed the resolved semantic contract"

standardProviderBody :: Text.Text
standardProviderBody = Text.unlines
  [ "  operation read : api.Reader;"
  , "  law coherent : true;"
  , "  operation write : Writer;"
  , "  lifecycle alive : false;"
  ]

checkedSurface
  :: Text.Text
  -> Text.Text
  -> Either String GrammarV1CheckedProviderContractSurface
checkedSurface displayName body = do
  declaration <- onlyProviderContract
    ("provider " <> displayName <> " {\n" <> body <> "}\n")
  case grammarV1CheckedClosedProviderContractSurface
      emptyStaticContext providerDeclaration providerInterface declaration of
    Just (Right checked) -> Right checked
    other -> Left ("provider surface did not check: " <> show other)

resolution
  :: Text.Text
  -> Text.Text
  -> ProviderOperationContract
  -> GrammarV1ResolvedProviderOperation
resolution key reference contract = GrammarV1ResolvedProviderOperation
  { resolvedProviderOperationKey = ProviderOperationKey key
  , resolvedProviderOperationReference = ReferencedGenericStaticActual reference
  , resolvedProviderOperationContract = contract
  }

operationContract :: Text.Text -> ProviderOperationContract
operationContract label = ProviderOperationContract
  { providerOperationCallableContract = CallableRefinementSurface
      { callableRefinementMachineShape = CallableMachineShape (label <> ".shape")
      , callableRefinementContract = CallableContract
          { callableContractInterfaceRevision = InterfaceRevision (label <> ".callable.interface")
          , callableContractCalleeTransition = PreserveCallee
          , callableContractEffectBound = Set.empty
          }
      , callableRefinementCallerAuthority = Set.empty
      , callableRefinementFailures = Set.empty
      }
  , providerOperationPreconditions = Set.empty
  , providerOperationOutcomeResidues = Map.empty
  }

providerDeclaration :: DeclarationKey
providerDeclaration = DeclarationKey "provider.stable.store"

providerInterface :: InterfaceRevision
providerInterface = InterfaceRevision "provider.interface.v1"

onlyProviderContract :: Text.Text -> Either String GrammarV1ProviderContractDecl
onlyProviderContract source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "provider-contract-construction" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProviderContractDeclaration provider -> Right provider
      other -> Left ("expected provider contract declaration, got " <> show other)
    declarations -> Left
      ("expected one provider contract declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
