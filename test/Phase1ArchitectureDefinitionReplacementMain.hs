{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.ProviderQualification
  ( CheckedProviderSemanticQualification (..)
  , ProviderContract (..)
  , ProviderImplementation (..)
  , ProviderImplementationOperation (..)
  , ProviderPreconditionKey (..)
  , ProviderQualificationClaim (..)
  , ProviderQualificationError (..)
  , checkProviderSemanticQualification
  )
import Phil.Core.Static
  ( DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  )
import Phil.Examples.Steve.ProviderQualifications
  ( SteveProviderQualificationArtifact (..)
  , SteveProviderQualifications (..)
  , materializeSteveProviderQualifications
  )
import System.Exit (exitFailure)

main :: IO ()
main =
  case materializeSteveProviderQualifications of
    Left err -> do
      putStrLn ("FAIL: materialize Steve provider qualification fixture -- " <> show err)
      exitFailure
    Right qualifications -> do
      let artifact = steveDigestProviderQualification qualifications
      results <- sequence
        [ test "definition rewrite preserves InterfaceRevision and revises DefinitionRevision"
            definitionRewriteSeparatesRevisions
        , test "original definition qualifies against the stable public contract"
            (originalDefinitionQualifies artifact)
        , test "replacement definition requalifies against the same public contract"
            (replacementDefinitionQualifies artifact)
        , test "replacement qualification binds unchanged interface and new definition revision"
            (replacementQualificationTracksRevisions artifact)
        , test "non-refining replacement is rejected under the unchanged interface"
            (nonRefiningReplacementRejects artifact)
        , test "public-contract change remains an InterfaceRevision change"
            publicContractChangeRevisesInterface
        ]
      unless (and results) exitFailure

originalIdentity :: DeclarationIdentity
originalIdentity = deriveDeclarationIdentity originalDescriptor

replacementIdentity :: DeclarationIdentity
replacementIdentity = deriveDeclarationIdentity replacementDescriptor

publicChangedIdentity :: DeclarationIdentity
publicChangedIdentity = deriveDeclarationIdentity publicChangedDescriptor

originalDescriptor :: DeclarationDescriptor
originalDescriptor = DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "digest_provider" ["Steve", "Providers"]
  , declarationKey = DeclarationKey "provider.steve.digest"
  , declarationInterfaceSemantics = stableInterfaceSemantics
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("algorithm", SemanticAtom "sha256-provider-v1")
      , ("composition", SemanticAtom "direct-library-call")
      ])
  }

replacementDescriptor :: DeclarationDescriptor
replacementDescriptor = originalDescriptor
  { declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("algorithm", SemanticAtom "sha256-provider-v2")
      , ("composition", SemanticAtom "streaming-wrapper")
      ])
  }

publicChangedDescriptor :: DeclarationDescriptor
publicChangedDescriptor = originalDescriptor
  { declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "DigestProvider[SHA256]")
      , ("authority", SemanticAtom "none")
      , ("failure", SemanticAtom "explicit-new-public-failure")
      ])
  }

stableInterfaceSemantics :: SemanticForm
stableInterfaceSemantics = SemanticRecord (Map.fromList
  [ ("provider", SemanticAtom "DigestProvider[SHA256]")
  , ("authority", SemanticAtom "none")
  ])

definitionRewriteSeparatesRevisions :: Bool
definitionRewriteSeparatesRevisions =
  identityDeclarationKey originalIdentity == identityDeclarationKey replacementIdentity
    && identityInterfaceRevision originalIdentity == identityInterfaceRevision replacementIdentity
    && identityDefinitionRevision originalIdentity /= identityDefinitionRevision replacementIdentity

originalDefinitionQualifies :: SteveProviderQualificationArtifact -> Bool
originalDefinitionQualifies artifact =
  case checkProviderSemanticQualification
      (stableContract artifact)
      (implementationFor originalIdentity artifact)
      (claimFor originalIdentity artifact) of
    Right checked ->
      checkedProviderContractRevision checked == identityInterfaceRevision originalIdentity
        && checkedProviderImplementationRevision checked == identityDefinitionRevision originalIdentity
    Left _ -> False

replacementDefinitionQualifies :: SteveProviderQualificationArtifact -> Bool
replacementDefinitionQualifies artifact =
  case checkProviderSemanticQualification
      (stableContract artifact)
      (implementationFor replacementIdentity artifact)
      (claimFor replacementIdentity artifact) of
    Right checked ->
      checkedProviderContractRevision checked == identityInterfaceRevision originalIdentity
        && checkedProviderImplementationRevision checked == identityDefinitionRevision replacementIdentity
    Left _ -> False

replacementQualificationTracksRevisions :: SteveProviderQualificationArtifact -> Bool
replacementQualificationTracksRevisions artifact =
  let claim = claimFor replacementIdentity artifact
  in providerQualificationRequiredInterface claim == identityInterfaceRevision originalIdentity
      && providerQualificationRequiredInterface claim == identityInterfaceRevision replacementIdentity
      && providerQualificationImplementationRevision claim == identityDefinitionRevision replacementIdentity
      && providerQualificationImplementationRevision claim /= identityDefinitionRevision originalIdentity

nonRefiningReplacementRejects :: SteveProviderQualificationArtifact -> Bool
nonRefiningReplacementRejects artifact =
  let extra = ProviderPreconditionKey "arch004.extra-caller-precondition"
      implementation0 = implementationFor replacementIdentity artifact
      implementation = implementation0
        { providerImplementationEntries = Map.map
            (\operation -> operation
              { providerImplementationPreconditions =
                  Set.insert extra (providerImplementationPreconditions operation)
              })
            (providerImplementationEntries implementation0)
        }
  in case checkProviderSemanticQualification
      (stableContract artifact)
      implementation
      (claimFor replacementIdentity artifact) of
      Left (ProviderQualificationStrongerPreconditions _ excess) -> Set.member extra excess
      _ -> False

publicContractChangeRevisesInterface :: Bool
publicContractChangeRevisesInterface =
  identityDeclarationKey originalIdentity == identityDeclarationKey publicChangedIdentity
    && identityInterfaceRevision originalIdentity /= identityInterfaceRevision publicChangedIdentity
    && identityDefinitionRevision originalIdentity /= identityDefinitionRevision publicChangedIdentity

stableContract :: SteveProviderQualificationArtifact -> ProviderContract
stableContract artifact =
  (steveProviderContract artifact)
    { providerContractInterfaceRevision = identityInterfaceRevision originalIdentity }

implementationFor
  :: DeclarationIdentity
  -> SteveProviderQualificationArtifact
  -> ProviderImplementation
implementationFor identity artifact =
  (steveProviderImplementation artifact)
    { providerImplementationDefinitionRevision = identityDefinitionRevision identity }

claimFor
  :: DeclarationIdentity
  -> SteveProviderQualificationArtifact
  -> ProviderQualificationClaim
claimFor identity artifact =
  (steveProviderSemanticClaim artifact)
    { providerQualificationRequiredInterface = identityInterfaceRevision identity
    , providerQualificationImplementationRevision = identityDefinitionRevision identity
    }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
