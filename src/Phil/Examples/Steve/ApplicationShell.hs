{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Steve.ApplicationShell
  ( SteveShellIOBinding (..)
  , steveShellIOBindings
  , stevePutShellEnvironment
  , steveGetShellEnvironment
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Callable (SemanticEffect)
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Ty (..))
import Phil.IO.Console
  ( ConsoleOperation (..)
  , ConsoleOperationContract (..)
  , consoleEnvironmentStdin
  , consoleEnvironmentStdout
  , consoleOperationContract
  , consoleProviderOccurrenceKey
  , standardConsoleEnvironment
  , unConsoleOccurrenceKey
  )
import Phil.IO.FileSystem
  ( FileSystemOperation (..)
  , fileSystemOperationEffect
  )
import Phil.Surface.Check
  ( PrimitiveArgumentDiscipline (..)
  , PrimitiveSemantics (..)
  , ProviderOutcomeSpec (..)
  , ReleaseResidue (..)
  , ReleaseSemanticAccount (..)
  , ReleaseTransitionContract (..)
  , ReleaseTransitionOutcome (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Systems
  ( fileSystemOccurrence
  , unFileSystemOccurrence
  )

-- | Exact IO-provider meaning attached to one Steve shell primitive spelling.
-- This is deliberately separate from the spelling itself so the later
-- qualification/replacement slice can vary implementations without changing
-- Phil source.
data SteveShellIOBinding = SteveShellIOBinding
  { steveShellPrimitiveName :: Text
  , steveShellProviderOccurrence :: Text
  , steveShellProviderOperation :: Text
  , steveShellProviderEffect :: SemanticEffect
  }
  deriving (Eq, Ord, Show)

steveShellIOBindings :: Either Text (Map Text SteveShellIOBinding)
steveShellIOBindings = do
  fileSystem <- mapLeft (Text.pack . show) (fileSystemOccurrence "steve.user.fs")
  let console = standardConsoleEnvironment
      stdin = consoleEnvironmentStdin console
      stdout = consoleEnvironmentStdout console
  stdinRead <- mapLeft (Text.pack . show)
    (consoleOperationContract stdin ConsoleReadLineOp)
  stdoutWrite <- mapLeft (Text.pack . show)
    (consoleOperationContract stdout ConsoleWriteOp)
  pure $ Map.fromList
    [ binding
        "console_read_line"
        (unConsoleOccurrenceKey (consoleProviderOccurrenceKey stdin))
        "read_line"
        (consoleContractEffect stdinRead)
    , binding
        "console_write"
        (unConsoleOccurrenceKey (consoleProviderOccurrenceKey stdout))
        "write"
        (consoleContractEffect stdoutWrite)
    , binding
        "fs_read"
        (unFileSystemOccurrence fileSystem)
        "read"
        (fileSystemOperationEffect fileSystem FileSystemReadOp)
    , binding
        "fs_replace"
        (unFileSystemOccurrence fileSystem)
        "replace"
        (fileSystemOperationEffect fileSystem FileSystemReplaceOp)
    ]
  where
    binding name occurrence operation effect =
      (name, SteveShellIOBinding name occurrence operation effect)

stevePutShellEnvironment :: Either Text SurfaceEnvironment
stevePutShellEnvironment = do
  _ <- steveShellIOBindings
  pure $ (emptySurfaceEnvironment emptyStaticContext)
    { surfacePrimitives = Map.fromList
        [ ("console_read_line", consoleReadLinePrimitive)
        , ("path_parse", pathParsePrimitive)
        , ("fs_read", fileReadPrimitive)
        , ("digest_compute", digestComputePrimitive)
        , ("content_id_render", contentIdRenderPrimitive)
        , ("console_write", consoleWritePrimitive)
        ]
    , surfaceCallables = Map.singleton "StevePut" stevePutCallable
    , surfaceExpectedProvides = Just TyUnit
    }

steveGetShellEnvironment :: Either Text SurfaceEnvironment
steveGetShellEnvironment = do
  _ <- steveShellIOBindings
  pure $ (emptySurfaceEnvironment emptyStaticContext)
    { surfacePrimitives = Map.fromList
        [ ("console_read_line", consoleReadLinePrimitive)
        , ("content_id_parse", contentIdParsePrimitive)
        , ("path_parse", pathParsePrimitive)
        , ("blob_read", blobReadPrimitive)
        , ("digest_check", digestCheckPrimitive)
        , ("fs_replace", fileReplacePrimitive)
        ]
    , surfaceCallables = Map.singleton "SteveGet" steveGetCallable
    , surfaceExpectedProvides = Just TyUnit
    , surfaceReleaseTransitions = [ownedBytesRelease]
    }

stevePutCallable :: SurfaceCallableSignature
stevePutCallable = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = DeclarationKey "decl:steve.put"
  , surfaceCallableParameters = [(Linear, ownedBytesType)]
  , surfaceCallableResult = Nothing
  }

steveGetCallable :: SurfaceCallableSignature
steveGetCallable = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = DeclarationKey "decl:steve.get"
  , surfaceCallableParameters = [(Unrestricted, contentIdType)]
  , surfaceCallableResult = Nothing
  }

consoleReadLinePrimitive :: PrimitiveSemantics
consoleReadLinePrimitive = PrimitiveProviderDecision []
  [ ProviderOutcomeSpec "line" [(Unrestricted, textType)]
  , ProviderOutcomeSpec "end-of-input" []
  , ProviderOutcomeSpec "console-failure" [(Unrestricted, consoleFailureType)]
  ]

consoleWritePrimitive :: PrimitiveSemantics
consoleWritePrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "written" []
  , ProviderOutcomeSpec "console-failure" [(Unrestricted, consoleFailureType)]
  ]

pathParsePrimitive :: PrimitiveSemantics
pathParsePrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "path" [(Unrestricted, providerRelativePathType)]
  , ProviderOutcomeSpec "invalid-path" [(Unrestricted, pathFailureType)]
  ]

fileReadPrimitive :: PrimitiveSemantics
fileReadPrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "found" [(Linear, ownedBytesType)]
  , ProviderOutcomeSpec "not-found" []
  , ProviderOutcomeSpec "too-large" []
  , ProviderOutcomeSpec "file-failure" [(Unrestricted, fileFailureType)]
  ]

fileReplacePrimitive :: PrimitiveSemantics
fileReplacePrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly, PrimitiveReadOnly]
  [ ProviderOutcomeSpec "replaced" []
  , ProviderOutcomeSpec "file-failure" [(Unrestricted, fileFailureType)]
  ]

digestComputePrimitive :: PrimitiveSemantics
digestComputePrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ProviderOutcomeSpec "computed" [(Unrestricted, contentIdType)]]

blobInstallPrimitive :: PrimitiveSemantics
blobInstallPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly, PrimitiveConsume]
  [ ProviderOutcomeSpec "installed" []
  , ProviderOutcomeSpec "already-exists" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

blobReadPrimitive :: PrimitiveSemantics
blobReadPrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "found" [(Linear, ownedBytesType)]
  , ProviderOutcomeSpec "not-found" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

digestCheckPrimitive :: PrimitiveSemantics
digestCheckPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly, PrimitiveReadOnly]
  [ ProviderOutcomeSpec "accepted" []
  , ProviderOutcomeSpec "rejected" [(Unrestricted, digestFailureType)]
  ]

contentIdParsePrimitive :: PrimitiveSemantics
contentIdParsePrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "content-id" [(Unrestricted, contentIdType)]
  , ProviderOutcomeSpec "invalid-content-id" [(Unrestricted, contentIdFailureType)]
  ]

contentIdRenderPrimitive :: PrimitiveSemantics
contentIdRenderPrimitive = PrimitiveProviderDecision [PrimitiveReadOnly]
  [ProviderOutcomeSpec "rendered" [(Unrestricted, textType)]]

textType, providerRelativePathType, ownedBytesType, contentIdType :: Ty
consoleFailureType, pathFailureType, fileFailureType, storageFailureType :: Ty
digestFailureType, contentIdFailureType :: Ty
textType = TyOpaque "Text"
providerRelativePathType = TyOpaque "ProviderRelativePath[steve.user.fs]"
ownedBytesType = TyOpaque "OwnedBytes"
contentIdType = TyOpaque "ContentId[SHA256]"
consoleFailureType = TyOpaque "ConsoleFailure"
pathFailureType = TyOpaque "ProviderRelativePathError"
fileFailureType = TyOpaque "FileSystemFailure"
storageFailureType = TyOpaque "StorageFailure"
digestFailureType = TyOpaque "DigestFailure"
contentIdFailureType = TyOpaque "ContentIdParseFailure"

ownedBytesRelease :: ReleaseTransitionContract
ownedBytesRelease = ReleaseTransitionContract
  { releaseTransitionKey = "provider.owned-bytes.release"
  , releaseTransitionOwnerType = ownedBytesType
  , releaseTransitionRequirements = Set.empty
  , releaseTransitionSemanticAccount = ReleaseSemanticAccount
      { releaseAccountAuthorityRefs = Set.empty
      , releaseAccountEvidenceRefs = Set.empty
      , releaseAccountEffectRefs = Set.empty
      , releaseAccountAssumptionRefs = Set.empty
      , releaseAccountCostRefs = Set.empty
      , releaseAccountSubjectRef = "owned-bytes"
      }
  , releaseTransitionOutcome = ReleaseContinuesUnit
  , releaseTransitionResidue = ReleaseConsumesOwner
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
