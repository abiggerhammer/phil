{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCorePolicy
import Phil.Core.Static
  ( DeclarationKey (..)
  , declareOpaqueClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , InstanceLineageSiteId (..)
  , PortableInstanceLineage (..)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )
import Phil.Surface.Phase0 (clientUploadSession, serverUploadSession)

main :: IO ()
main = do
  clientSource <- TextIO.readFile "examples/upload/client.phil"
  serverSource <- TextIO.readFile "examples/upload/server.phil"
  case checkedUploadArchitecture clientSource serverSource of
    Left err -> error err
    Right architecture -> do
      putStrLn "UPLOAD CALL SITES"
      mapM_ print (Map.toAscList (sourceCoreCallSites architecture))
      putStrLn "UPLOAD BRANCH SITES"
      mapM_ print (Map.toAscList (sourceCoreBranchSites architecture))

checkedUploadArchitecture :: Text -> Text -> Either String CheckedSourceArchitecture
checkedUploadArchitecture clientSource serverSource = do
  clientEnvironment <- mapLeft show uploadClientEnvironment
  serverEnvironment <- mapLeft show uploadServerEnvironment
  checked <- mapLeft show $ checkPortableSourceBundle
    uploadRoots
    (Map.fromList
      [ (clientDeclaration, clientEnvironment)
      , (serverDeclaration, serverEnvironment)
      ])
    (uploadBundle clientSource serverSource)
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:upload" (InstanceLineageSiteId "instance.upload"))
    checked

uploadBundle :: Text -> Text -> PortableSourceBundle
uploadBundle clientSource serverSource = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:upload"
  , portableSourceUnits =
      [ PortableSourceUnit
          (SourceUnitId "unit.upload.client")
          (DeclarationSiteId "site.upload.client")
          (Just "decl:upload.client")
          clientSource
      , PortableSourceUnit
          (SourceUnitId "unit.upload.server")
          (DeclarationSiteId "site.upload.server")
          (Just "decl:upload.server")
          serverSource
      ]
  , portableInstanceLineage =
      [ PortableInstanceLineage
          (InstanceLineageSiteId "instance.upload")
          "inst:phase1.upload"
      ]
  , portableProcessLineage = []
  }

uploadRoots :: SourceRootMap
uploadRoots = Map.singleton "program:upload" serverDeclaration

clientDeclaration, serverDeclaration :: DeclarationKey
clientDeclaration = DeclarationKey "decl:upload.client"
serverDeclaration = DeclarationKey "decl:upload.server"

uploadClientEnvironment :: Either Text SurfaceEnvironment
uploadClientEnvironment = do
  base <- uploadBaseEnvironment
  pure base
    { surfaceInitialBindings = Map.fromList
        [ ("session0", InitialBinding Linear (TyEndpoint clientUploadSession) PlainShape)
        , ("payload", ownedPayload "payload")
        , ("sha256", InitialBinding Unrestricted (TyOpaque "DigestAlgorithm") PlainShape)
        ]
    , surfaceExpectedProvides = Just (TyEndpoint clientUploadSession)
    , surfaceReleaseTransitions = [payloadReleaseTransition]
    }

uploadServerEnvironment :: Either Text SurfaceEnvironment
uploadServerEnvironment = do
  base <- uploadBaseEnvironment
  pure base
    { surfaceInitialBindings = Map.fromList
        [ ("session0", InitialBinding Linear (TyEndpoint serverUploadSession) PlainShape)
        , ("policyContext", InitialBinding Unrestricted
            (TyOpaqueSorted "PolicyContext" (SortStableId "Policy")) PlainShape)
        , ("serverSupported", InitialBinding Unrestricted
            (TyOpaqueSorted "SupportedVersions" versionSetSort) PlainShape)
        ]
    , surfaceExpectedProvides = Just (TyEndpoint serverUploadSession)
    , surfaceSelectRequirements = uploadSelectRequirements
    , surfaceReceiveExactRequirement = Just beginPolicyProposition
    , surfaceReleaseTransitions = [serverPayloadReleaseTransition]
    }

uploadBaseEnvironment :: Either Text SurfaceEnvironment
uploadBaseEnvironment = do
  staticContext <- case declareOpaqueClaim
      "DigestMatches"
      [ (Name "begin", SortOpaque "Frame")
      , (Name "payload_id", SortStableId "OwnedBytes")
      ]
      emptyStaticContext of
        Left err -> Left (Text.pack (show err))
        Right context -> Right context
  pure (emptySurfaceEnvironment staticContext)
    { surfacePrimitives = Map.fromList
        [ ("supported_versions", PrimitiveSupportedVersions)
        , ("sha256", PrimitiveSha256)
        , ("should_cancel_upload", PrimitiveShouldCancel)
        , ("choose_supported", PrimitiveChooseSupported)
        , ("store", PrimitiveStore)
        , ("record_upload_id", PrimitiveRecordUploadId)
        ]
    , surfaceTypeAliases = Map.fromList
        [ ("Client[Upload]", TyEndpoint clientUploadSession)
        , ("Server[Upload]", TyEndpoint serverUploadSession)
        ]
    }

uploadSelectRequirements :: Map.Map Text [Proposition]
uploadSelectRequirements = Map.fromList
  [ ("unsupported", [helloPolicyProposition, Disjoint serverSupportedTerm helloVersionsTerm])
  , ("version", [helloPolicyProposition])
  , ("proceed", [beginPolicyProposition])
  , ("accepted", [digestMatchesProposition])
  ]

helloPolicyProposition :: Proposition
helloPolicyProposition = Atom "HelloPolicy"
  [RefVar (Name "policyContext"), RefVar (Name "hello")]

beginPolicyProposition :: Proposition
beginPolicyProposition = Atom "BeginPolicy"
  [RefVar (Name "policyContext"), RefVar (Name "begin")]

digestMatchesProposition :: Proposition
digestMatchesProposition = Atom "DigestMatches"
  [RefVar (Name "begin"), RefOpaque (SortStableId "OwnedBytes") "payload"]

serverSupportedTerm :: RefTerm
serverSupportedTerm = RefVar (Name "serverSupported")

helloVersionsTerm :: RefTerm
helloVersionsTerm = RefField (RefVar (Name "hello")) "versions" versionSetSort

beginLengthUInt :: RefTerm
beginLengthUInt = RefField (RefVar (Name "begin")) "length" (SortUInt 64)

beginLengthNat :: RefTerm
beginLengthNat = RefToNat beginLengthUInt

versionSetSort :: RefSort
versionSetSort = SortFiniteSet (SortUInt 16)

ownedPayload :: Text -> InitialBinding
ownedPayload name =
  let lengthUInt = RefField (RefVar (Name name)) "length" (SortUInt 64)
      index = RefToNat lengthUInt
  in InitialBinding Linear (TyBytes index) (OwnedBytesShape index)

payloadReleaseTransition :: ReleaseTransitionContract
payloadReleaseTransition = ReleaseTransitionContract
  { releaseTransitionKey = "upload.payload.release.v1"
  , releaseTransitionOwnerType = initialType (ownedPayload "payload")
  , releaseTransitionRequirements = Set.empty
  , releaseTransitionSemanticAccount = emptyReleaseAccount "upload.payload"
  , releaseTransitionOutcome = ReleaseContinuesUnit
  , releaseTransitionResidue = ReleaseConsumesOwner
  }

serverPayloadReleaseTransition :: ReleaseTransitionContract
serverPayloadReleaseTransition = ReleaseTransitionContract
  { releaseTransitionKey = "upload.server.payload.release.v1"
  , releaseTransitionOwnerType = TyBytes beginLengthNat
  , releaseTransitionRequirements = Set.empty
  , releaseTransitionSemanticAccount = emptyReleaseAccount "upload.server.payload"
  , releaseTransitionOutcome = ReleaseContinuesUnit
  , releaseTransitionResidue = ReleaseConsumesOwner
  }

emptyReleaseAccount :: Text -> ReleaseSemanticAccount
emptyReleaseAccount subject = ReleaseSemanticAccount
  { releaseAccountAuthorityRefs = Set.empty
  , releaseAccountEvidenceRefs = Set.empty
  , releaseAccountEffectRefs = Set.empty
  , releaseAccountAssumptionRefs = Set.empty
  , releaseAccountCostRefs = Set.empty
  , releaseAccountSubjectRef = subject
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
