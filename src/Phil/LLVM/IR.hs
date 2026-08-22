{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.IR
  ( LLVMBlockId (..)
  , LLVMStrengtheningId (..)
  , LLVMStrengtheningKind (..)
  , LLVMAuthority (..)
  , LLVMStrengthening (..)
  , LLVMOp (..)
  , LLVMTerminator (..)
  , LLVMBlock (..)
  , LLVMFunction (..)
  , LLVMModule (..)
  , LLVMEdgeWitness (..)
  , LLVMEmissionContract (..)
  , LLVMArtifact (..)
  , LLVMTargetProfile (..)
  , llvmBlockSuccessors
  , llvmModuleDigest
  , llvmRuntimeSites
  , llvmStrengtheningUses
  , renderLLVMModule
  ) where

import Data.Char (isAlphaNum)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( Digest (..)
  , EvidenceEntryId (..)
  , RevisionId (..)
  , digestText
  )
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , ScalarType (..)
  )
import Phil.Systems.IR
  ( BlockId
  , CompilationProfile (..)
  , InvariantId (..)
  , RuntimeSiteRef (..)
  )

newtype LLVMBlockId = LLVMBlockId { unLLVMBlockId :: Text }
  deriving (Eq, Ord, Show)

newtype LLVMStrengtheningId = LLVMStrengtheningId { unLLVMStrengtheningId :: Text }
  deriving (Eq, Ord, Show)

data LLVMStrengtheningKind
  = LLVMNoUnsignedWrap
  | LLVMNoSignedWrap
  | LLVMInBounds
  | LLVMAssume
  | LLVMUnreachableFact
  deriving (Eq, Ord, Show)

data LLVMAuthority
  = LLVMInvariant InvariantId
  | LLVMEvidence EvidenceEntryId
  | LLVMObligation RevisionId
  deriving (Eq, Ord, Show)

data LLVMStrengthening = LLVMStrengthening
  { llvmStrengtheningId :: LLVMStrengtheningId
  , llvmStrengtheningKind :: LLVMStrengtheningKind
  , llvmStrengtheningClaim :: Text
  , llvmStrengtheningAuthority :: LLVMAuthority
  , llvmStrengtheningFunction :: Text
  , llvmStrengtheningBlock :: LLVMBlockId
  }
  deriving (Eq, Ord, Show)

data LLVMOp
  = LLVMCall Text
  | LLVMRuntime RuntimeSiteRef Text
  | LLVMCleanup Text
  | LLVMPlain Text
  | LLVMScalarLiteral Text ScalarLiteral
  | LLVMStrengtheningOp LLVMStrengtheningId Text
  | LLVMPoison Text
  | LLVMUndef Text
  | LLVMFreeze Text
  | LLVMMetadata Text
  deriving (Eq, Ord, Show)

data LLVMTerminator
  = LLVMJump LLVMBlockId
  | LLVMBranch LLVMBlockId LLVMBlockId
  | LLVMRuntimeBranch RuntimeSiteRef Text LLVMBlockId LLVMBlockId
  | LLVMReturnScalar Text ScalarType
  | LLVMReturn Text
  | LLVMUnreachable (Maybe LLVMStrengtheningId)
  deriving (Eq, Ord, Show)

data LLVMBlock = LLVMBlock
  { llvmBlockId :: LLVMBlockId
  , llvmBlockOps :: [LLVMOp]
  , llvmBlockTerminator :: LLVMTerminator
  }
  deriving (Eq, Ord, Show)

data LLVMFunction = LLVMFunction
  { llvmFunctionName :: Text
  , llvmFunctionEntry :: LLVMBlockId
  , llvmFunctionBlocks :: Map LLVMBlockId LLVMBlock
  }
  deriving (Eq, Show)

data LLVMModule = LLVMModule
  { llvmModuleName :: Text
  , llvmLanguageVersion :: Text
  , llvmToolVersion :: Text
  , llvmTargetTriple :: Text
  , llvmDataLayout :: Text
  , llvmRuntimeABIDigest :: Digest
  , llvmRuntimeABIProfile :: Text
  , llvmCompilationProfile :: CompilationProfile
  , llvmFunctions :: Map Text LLVMFunction
  , llvmStrengthenings :: Map LLVMStrengtheningId LLVMStrengthening
  }
  deriving (Eq, Show)

data LLVMEdgeWitness = LLVMEdgeWitness
  { llvmEdgeSourceFunction :: Text
  , llvmEdgeSourceFrom :: BlockId
  , llvmEdgeSourceTo :: BlockId
  , llvmEdgeTargetFunction :: Text
  , llvmEdgeTargetPath :: [LLVMBlockId]
  }
  deriving (Eq, Ord, Show)

data LLVMEmissionContract = LLVMEmissionContract
  { llvmContractSourceDigest :: Digest
  , llvmContractTargetDigest :: Digest
  , llvmContractEdgeWitnesses :: [LLVMEdgeWitness]
  , llvmContractTraceRelation :: [Text]
  , llvmContractResourceFailureRelation :: [Text]
  }
  deriving (Eq, Show)

data LLVMArtifact = LLVMArtifact
  { llvmArtifactModule :: LLVMModule
  , llvmArtifactText :: Text
  , llvmArtifactContract :: LLVMEmissionContract
  }
  deriving (Eq, Show)

data LLVMTargetProfile = LLVMTargetProfile
  { llvmTargetLanguageVersion :: Text
  , llvmTargetToolVersion :: Text
  , llvmTargetTripleName :: Text
  , llvmTargetDataLayout :: Text
  , llvmTargetRuntimeABIDigest :: Digest
  , llvmTargetRuntimeABIProfile :: Text
  }
  deriving (Eq, Ord, Show)

llvmBlockSuccessors :: LLVMBlock -> [LLVMBlockId]
llvmBlockSuccessors blockValue = case llvmBlockTerminator blockValue of
  LLVMJump target -> [target]
  LLVMBranch yes no -> [yes, no]
  LLVMRuntimeBranch _ _ yes no -> [yes, no]
  LLVMReturnScalar _ _ -> []
  LLVMReturn _ -> []
  LLVMUnreachable _ -> []

llvmModuleDigest :: LLVMModule -> Digest
llvmModuleDigest = digestText . renderLLVMModule

llvmRuntimeSites :: LLVMModule -> [RuntimeSiteRef]
llvmRuntimeSites moduleValue = concat
  [ blockRuntimeSites blockValue
  | function <- Map.elems (llvmFunctions moduleValue)
  , blockValue <- Map.elems (llvmFunctionBlocks function)
  ]
  where
    blockRuntimeSites blockValue =
      [ site
      | LLVMRuntime site _ <- llvmBlockOps blockValue
      ] <> case llvmBlockTerminator blockValue of
        LLVMRuntimeBranch site _ _ _ -> [site]
        _ -> []

llvmStrengtheningUses :: LLVMModule -> [LLVMStrengtheningId]
llvmStrengtheningUses moduleValue = concat
  [ blockUses blockValue
  | function <- Map.elems (llvmFunctions moduleValue)
  , blockValue <- Map.elems (llvmFunctionBlocks function)
  ]
  where
    blockUses blockValue =
      [ strengtheningId
      | LLVMStrengtheningOp strengtheningId _ <- llvmBlockOps blockValue
      ] <> case llvmBlockTerminator blockValue of
        LLVMUnreachable (Just strengtheningId) -> [strengtheningId]
        _ -> []

renderLLVMModule :: LLVMModule -> Text
renderLLVMModule moduleValue = Text.unlines $
  header
  <> strengtheningRecords
  <> declarations
  <> concatMap renderFunction (Map.toAscList (llvmFunctions moduleValue))
  where
    header =
      [ "; Phil canonical pre-optimization LLVM artifact"
      , "; llvm-language=" <> oneLine (llvmLanguageVersion moduleValue)
      , "; llvm-tool=" <> oneLine (llvmToolVersion moduleValue)
      , "; compilation-profile=" <> renderCompilationProfile (llvmCompilationProfile moduleValue)
      , "; runtime-abi-profile=" <> oneLine (llvmRuntimeABIProfile moduleValue)
      , "; runtime-abi-digest=" <> oneLine (unDigest (llvmRuntimeABIDigest moduleValue))
      , "source_filename = \"" <> escapeString (llvmModuleName moduleValue) <> "\""
      , "target datalayout = \"" <> escapeString (llvmDataLayout moduleValue) <> "\""
      , "target triple = \"" <> escapeString (llvmTargetTriple moduleValue) <> "\""
      , ""
      ]

    strengtheningRecords =
      map renderStrengtheningRecord (Map.toAscList (llvmStrengthenings moduleValue))
      <> if Map.null (llvmStrengthenings moduleValue) then [] else [""]

    renderStrengtheningRecord (key, strengthening) = Text.intercalate " "
      [ "; phil-strengthening"
      , "key=" <> oneLine (unLLVMStrengtheningId key)
      , "id=" <> oneLine (unLLVMStrengtheningId (llvmStrengtheningId strengthening))
      , "kind=" <> renderStrengtheningKind (llvmStrengtheningKind strengthening)
      , "authority=" <> renderAuthority (llvmStrengtheningAuthority strengthening)
      , "function=" <> oneLine (llvmStrengtheningFunction strengthening)
      , "block=" <> oneLine (unLLVMBlockId (llvmStrengtheningBlock strengthening))
      , "claim=" <> oneLine (llvmStrengtheningClaim strengthening)
      ]

    declarations =
      branchDeclaration
      <> cleanupDeclaration
      <> assumeDeclaration
      <> map renderCallDeclaration (Set.toAscList callNames)
      <> map renderRuntimeDeclaration (Set.toAscList runtimeEvidence)
      <> [""]

    allBlocks =
      [ blockValue
      | function <- Map.elems (llvmFunctions moduleValue)
      , blockValue <- Map.elems (llvmFunctionBlocks function)
      ]

    branchDeclaration =
      if any isGenericBranch allBlocks then ["declare i1 @phil_branch_condition()"] else []

    cleanupDeclaration =
      if any hasCleanup allBlocks then ["declare void @phil_cleanup()"] else []

    assumeDeclaration =
      if any ((== LLVMAssume) . llvmStrengtheningKind) (Map.elems (llvmStrengthenings moduleValue))
        then ["declare void @llvm.assume(i1)"]
        else []

    callNames = Set.fromList
      [ name
      | blockValue <- allBlocks
      , LLVMCall name <- llvmBlockOps blockValue
      ]

    runtimeEvidence = Set.fromList
      ( [ unEvidenceEntryId (runtimeSiteEvidence site)
        | blockValue <- allBlocks
        , LLVMRuntime site _ <- llvmBlockOps blockValue
        ]
        <> [ unEvidenceEntryId (runtimeSiteEvidence site)
           | blockValue <- allBlocks
           , LLVMRuntimeBranch site _ _ _ <- [llvmBlockTerminator blockValue]
           ]
      )

    isGenericBranch blockValue = case llvmBlockTerminator blockValue of
      LLVMBranch _ _ -> True
      _ -> False

    hasCleanup blockValue = any isCleanup (llvmBlockOps blockValue)
    isCleanup LLVMCleanup {} = True
    isCleanup _ = False

    renderCallDeclaration name = "declare void @phil_call_" <> symbol name <> "()"
    renderRuntimeDeclaration evidence = "declare i1 @phil_runtime_" <> symbol evidence <> "()"

    renderFunction (functionKey, function) =
      [ "define " <> renderFunctionReturnType function <> " @" <> symbol functionKey <> "() {" ]
      <> concatMap renderBlock (orderedBlocks function)
      <> ["}", ""]

    renderFunctionReturnType function =
      case
        [ scalarType
        | blockValue <- Map.elems (llvmFunctionBlocks function)
        , LLVMReturnScalar _ scalarType <- [llvmBlockTerminator blockValue]
        ] of
          scalarType : _ -> renderScalarType scalarType
          [] -> "i32"

    orderedBlocks function =
      case Map.lookup (llvmFunctionEntry function) (llvmFunctionBlocks function) of
        Nothing -> Map.toAscList (llvmFunctionBlocks function)
        Just entryBlock ->
          (llvmFunctionEntry function, entryBlock)
          : filter ((/= llvmFunctionEntry function) . fst)
              (Map.toAscList (llvmFunctionBlocks function))

    renderBlock (blockKey, blockValue) =
      [ symbol (unLLVMBlockId blockKey) <> ":" ]
      <> map ("  " <>) (concatMap renderOp (llvmBlockOps blockValue))
      <> map ("  " <>) (renderTerminator blockValue)

    renderOp operation = case operation of
      LLVMCall name -> ["call void @phil_call_" <> symbol name <> "()"]
      LLVMRuntime site name ->
        [ "; runtime " <> oneLine name
        , "call i1 @phil_runtime_" <> symbol (unEvidenceEntryId (runtimeSiteEvidence site)) <> "()"
        ]
      LLVMCleanup name ->
        ["; cleanup " <> oneLine name, "call void @phil_cleanup()"]
      LLVMPlain description -> ["; plain " <> oneLine description]
      LLVMScalarLiteral name literal -> [renderScalarLiteralInstruction name literal]
      LLVMStrengtheningOp strengtheningId description ->
        renderStrengthening strengtheningId description
      LLVMPoison description ->
        [ "%phil_poison_" <> symbol description <> " = select i1 poison, i1 true, i1 false" ]
      LLVMUndef description ->
        [ "%phil_undef_" <> symbol description <> " = select i1 undef, i1 true, i1 false" ]
      LLVMFreeze description ->
        [ "%phil_freeze_" <> symbol description <> " = freeze i1 undef" ]
      LLVMMetadata description -> ["; !phil " <> oneLine description]

    renderScalarLiteralInstruction name literal =
      case literal of
        ScalarBoolLiteral value ->
          "%" <> symbol name <> " = or i1 false, " <> if value then "true" else "false"
        ScalarUIntLiteral width value ->
          "%" <> symbol name <> " = add i" <> Text.pack (show width)
            <> " 0, " <> Text.pack (show value)

    renderStrengthening strengtheningId description =
      case Map.lookup strengtheningId (llvmStrengthenings moduleValue) of
        Nothing -> ["; missing-strengthening " <> oneLine (unLLVMStrengtheningId strengtheningId)]
        Just strengthening -> case llvmStrengtheningKind strengthening of
          LLVMNoUnsignedWrap ->
            [ "%phil_strength_" <> symbol (unLLVMStrengtheningId strengtheningId)
                <> " = add nuw i64 0, 0 ; " <> oneLine description
            ]
          LLVMNoSignedWrap ->
            [ "%phil_strength_" <> symbol (unLLVMStrengtheningId strengtheningId)
                <> " = add nsw i64 0, 0 ; " <> oneLine description
            ]
          LLVMInBounds ->
            [ "%phil_strength_" <> symbol (unLLVMStrengtheningId strengtheningId)
                <> " = getelementptr inbounds i8, ptr null, i64 0 ; " <> oneLine description
            ]
          LLVMAssume ->
            [ "call void @llvm.assume(i1 true) ; " <> oneLine description ]
          LLVMUnreachableFact ->
            [ "; unreachable authority " <> oneLine description ]

    renderTerminator blockValue = case llvmBlockTerminator blockValue of
      LLVMJump target -> ["br label %" <> symbol (unLLVMBlockId target)]
      LLVMBranch yes no ->
        [ "%phil_cond_" <> symbol (unLLVMBlockId (llvmBlockId blockValue))
            <> " = call i1 @phil_branch_condition()"
        , "br i1 %phil_cond_" <> symbol (unLLVMBlockId (llvmBlockId blockValue))
            <> ", label %" <> symbol (unLLVMBlockId yes)
            <> ", label %" <> symbol (unLLVMBlockId no)
        ]
      LLVMRuntimeBranch site name yes no ->
        [ "; runtime-branch " <> oneLine name
        , "%phil_runtime_cond_" <> symbol (unLLVMBlockId (llvmBlockId blockValue))
            <> " = call i1 @phil_runtime_" <> symbol (unEvidenceEntryId (runtimeSiteEvidence site)) <> "()"
        , "br i1 %phil_runtime_cond_" <> symbol (unLLVMBlockId (llvmBlockId blockValue))
            <> ", label %" <> symbol (unLLVMBlockId yes)
            <> ", label %" <> symbol (unLLVMBlockId no)
        ]
      LLVMReturnScalar name scalarType ->
        ["ret " <> renderScalarType scalarType <> " %" <> symbol name]
      LLVMReturn outcome -> ["ret i32 0 ; " <> oneLine outcome]
      LLVMUnreachable _ -> ["unreachable"]

renderScalarType :: ScalarType -> Text
renderScalarType scalarType = case scalarType of
  ScalarBool -> "i1"
  ScalarUInt width -> "i" <> Text.pack (show width)

renderCompilationProfile :: CompilationProfile -> Text
renderCompilationProfile profile = case profile of
  CheckedRuntime -> "checked-runtime"
  CertifiedRelease -> "certified-release"

renderStrengtheningKind :: LLVMStrengtheningKind -> Text
renderStrengtheningKind kind = case kind of
  LLVMNoUnsignedWrap -> "nuw"
  LLVMNoSignedWrap -> "nsw"
  LLVMInBounds -> "inbounds"
  LLVMAssume -> "llvm.assume"
  LLVMUnreachableFact -> "unreachable"

renderAuthority :: LLVMAuthority -> Text
renderAuthority authority = case authority of
  LLVMInvariant invariantId -> "invariant:" <> oneLine (unInvariantId invariantId)
  LLVMEvidence evidenceId -> "evidence:" <> oneLine (unEvidenceEntryId evidenceId)
  LLVMObligation revision -> "obligation:" <> oneLine (unRevisionId revision)

symbol :: Text -> Text
symbol value =
  let mapped = Text.map (\character -> if isAlphaNum character then character else '_') value
  in if Text.null mapped then "unnamed" else mapped

oneLine :: Text -> Text
oneLine = Text.replace "\r" " " . Text.replace "\n" " "

escapeString :: Text -> Text
escapeString = Text.replace "\"" "\\22" . Text.replace "\\" "\\5C"