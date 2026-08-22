{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler
import Phil.Core.Scalar
  ( ScalarLiteral (ScalarUIntLiteral)
  , ScalarType (ScalarUInt)
  )
import Phil.LLVM (llvmArtifactText)
import Phil.Systems
  ( BlockId (..)
  , ScalarDataflowError (..)
  , SystemsArtifact (..)
  , SystemsBlock (..)
  , SystemsFunction (..)
  , SystemsOp (..)
  , SystemsProgram (..)
  , SystemsTerminator (..)
  , SystemsValue (systemsValueRole)
  , SystemsValueRole (TypedScalar)
  , ValueId (..)
  , verifyScalarDataflow
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "runnable Unit source compiles through verified LLVM" validUnitCompiles
    , test "direct U32 return compiles through verified LLVM" validU32Compiles
    , test "checked scalar let binding compiles through verified LLVM" scalarBindingCompiles
    , test "source scalar binding identity survives into Systems IR" bindingIdentitySurvivesSystems
    , test "source scalar binding becomes the LLVM SSA name" bindingIdentitySurvivesLLVM
    , test "scalar variable aliases do not introduce a copy" scalarAliasDoesNotCopy
    , test "U32 scalar type survives into Systems IR" u32TypeSurvivesSystems
    , test "direct U32 literal and width survive into LLVM SSA" u32ValueSurvivesLLVM
    , test "scalar SSA verifier rejects a missing definition" missingScalarDefinitionRejects
    , test "scalar SSA verifier rejects multiple definitions" duplicateScalarDefinitionRejects
    , test "scalar SSA verifier rejects a non-dominating definition" nonDominatingScalarDefinitionRejects
    , test "Surface projection rejects scalar literal drift" sourceLiteralDriftRejects
    , test "Surface projection rejects return-target drift" sourceReturnTargetDriftRejects
    , test "runnable source identity is content-bound" sourceIdentityIsContentBound
    , test "Unit-only compatibility entry point rejects scalar programs" unitEntryRejectsScalar
    , test "runnable fragment requires main component" nonMainRejects
    , test "runnable fragment rejects unsupported provides type" unsupportedProvidesRejects
    , test "runnable fragment requires matching Unit return" nonUnitReturnRejects
    , test "U32 runnable fragment rejects non-scalar return" nonScalarU32Rejects
    , test "U32 runnable fragment rejects out-of-range literal" u32OverflowRejects
    , test "U32 let binding rejects out-of-range literal" u32BindingOverflowRejects
    , test "native runnable scalar ABI currently rejects U16" u16ReturnRejects
    , test "scalar runnable fragment rejects unsupported expression statements" scalarExpressionStatementRejects
    , test "Unit runnable fragment rejects extra statements" extraUnitStatementRejects
    , test "runnable fragment requires one component" multipleComponentsReject
    ]
  if and results then pure () else exitFailure

unitSource :: Text
unitSource = Text.unlines
  [ "component main provides Unit {"
  , "    return unit"
  , "}"
  ]

u32Source :: Text
u32Source = Text.unlines
  [ "component main provides U32 {"
  , "    return 42"
  , "}"
  ]

bindingSource :: Text
bindingSource = Text.unlines
  [ "component main provides U32 {"
  , "    let answer = 42"
  , "    return answer"
  , "}"
  ]

aliasSource :: Text
aliasSource = Text.unlines
  [ "component main provides U32 {"
  , "    let original = 42"
  , "    let answer = original"
  , "    return answer"
  , "}"
  ]

returnChoiceSource :: Text
returnChoiceSource = Text.unlines
  [ "component main provides U32 {"
  , "    let answer = 42"
  , "    let wrong = 7"
  , "    return answer"
  , "}"
  ]

validUnitCompiles :: Bool
validUnitCompiles = case compileRunnable "unit.phil" unitSource of
  Left _ -> False
  Right runnable ->
    let llvm = llvmArtifactText (runnableLLVMArtifact runnable)
    in runnableResult runnable == RunnableUnit
        && Text.isInfixOf "define i32 @main() {" llvm
        && Text.isInfixOf "ret i32 0 ; return-unit" llvm

validU32Compiles :: Bool
validU32Compiles = case compileRunnable "u32.phil" u32Source of
  Left _ -> False
  Right runnable ->
    runnableResult runnable == RunnableScalar (ScalarUInt 32)

scalarBindingCompiles :: Bool
scalarBindingCompiles = case compileRunnable "binding.phil" bindingSource of
  Left _ -> False
  Right runnable -> runnableResult runnable == RunnableScalar (ScalarUInt 32)

bindingIdentitySurvivesSystems :: Bool
bindingIdentitySurvivesSystems = case compileRunnable "binding.phil" bindingSource of
  Left _ -> False
  Right runnable ->
    case mainFunction (runnableSystemsArtifact runnable) of
      Nothing -> False
      Just functionValue ->
        case Map.lookup (ValueId "answer") (systemsFunctionValues functionValue) of
          Just value -> systemsValueRole value == TypedScalar (ScalarUInt 32)
          Nothing -> False

bindingIdentitySurvivesLLVM :: Bool
bindingIdentitySurvivesLLVM = case compileRunnable "binding.phil" bindingSource of
  Left _ -> False
  Right runnable ->
    let llvm = llvmArtifactText (runnableLLVMArtifact runnable)
    in Text.isInfixOf "%answer = add i32 0, 42" llvm
        && Text.isInfixOf "ret i32 %answer" llvm

scalarAliasDoesNotCopy :: Bool
scalarAliasDoesNotCopy = case compileRunnable "alias.phil" aliasSource of
  Left _ -> False
  Right runnable ->
    let llvm = llvmArtifactText (runnableLLVMArtifact runnable)
    in Text.isInfixOf "%original = add i32 0, 42" llvm
        && Text.isInfixOf "ret i32 %original" llvm
        && not (Text.isInfixOf "%answer =" llvm)

u32TypeSurvivesSystems :: Bool
u32TypeSurvivesSystems = case compileRunnable "u32.phil" u32Source of
  Left _ -> False
  Right runnable ->
    case toList
        (systemsProgramFunctions (systemsArtifactProgram (runnableSystemsArtifact runnable))) of
      [functionValue] ->
        any ((== TypedScalar (ScalarUInt 32)) . systemsValueRole)
          (toList (systemsFunctionValues functionValue))
      _ -> False

u32ValueSurvivesLLVM :: Bool
u32ValueSurvivesLLVM = case compileRunnable "u32.phil" u32Source of
  Left _ -> False
  Right runnable ->
    let llvm = llvmArtifactText (runnableLLVMArtifact runnable)
    in Text.isInfixOf "define i32 @main() {" llvm
        && Text.isInfixOf "%return_value_0 = add i32 0, 42" llvm
        && Text.isInfixOf "ret i32 %return_value_0" llvm

missingScalarDefinitionRejects :: Bool
missingScalarDefinitionRejects =
  case compileRunnable "binding.phil" bindingSource of
    Left _ -> False
    Right runnable ->
      let bad = adjustEntryBlock
            (\blockValue -> blockValue { systemsBlockOps = [] })
            (runnableSystemsArtifact runnable)
      in case verifyScalarDataflow bad of
          Left ScalarDefinitionMissing {} -> True
          _ -> False

duplicateScalarDefinitionRejects :: Bool
duplicateScalarDefinitionRejects =
  case compileRunnable "binding.phil" bindingSource of
    Left _ -> False
    Right runnable ->
      let bad = adjustEntryBlock
            (\blockValue -> blockValue
              { systemsBlockOps = systemsBlockOps blockValue <> systemsBlockOps blockValue })
            (runnableSystemsArtifact runnable)
      in case verifyScalarDataflow bad of
          Left ScalarDefinitionMultiple {} -> True
          _ -> False

nonDominatingScalarDefinitionRejects :: Bool
nonDominatingScalarDefinitionRejects =
  case compileRunnable "binding.phil" bindingSource of
    Left _ -> False
    Right runnable ->
      case mainFunction (runnableSystemsArtifact runnable) of
        Nothing -> False
        Just functionValue ->
          case Map.lookup (BlockId "entry") (systemsFunctionBlocks functionValue) of
            Nothing -> False
            Just entryBlock ->
              let lateBlockId = BlockId "late.definition"
                  lateBlock = SystemsBlock
                    { systemsBlockId = lateBlockId
                    , systemsBlockOps = systemsBlockOps entryBlock
                    , systemsBlockTerminator = TermEnd "late-definition-test"
                    }
                  changedFunction = functionValue
                    { systemsFunctionBlocks = Map.fromList
                        [ (BlockId "entry", entryBlock { systemsBlockOps = [] })
                        , (lateBlockId, lateBlock)
                        ]
                    }
                  bad = replaceMainFunction changedFunction (runnableSystemsArtifact runnable)
              in case verifyScalarDataflow bad of
                  Left ScalarUseBeforeDefinition {} -> True
                  _ -> False

sourceLiteralDriftRejects :: Bool
sourceLiteralDriftRejects =
  case compileRunnable "binding.phil" bindingSource of
    Left _ -> False
    Right runnable ->
      let bad = adjustEntryBlock changeLiteral (runnableSystemsArtifact runnable)
      in case verifyRunnableSourceProjection "binding.phil" bindingSource bad of
          Left (RunnableSourceProjectionError SourceProjectionNamedLiteralMismatch {}) -> True
          _ -> False
  where
    changeLiteral blockValue = blockValue
      { systemsBlockOps = map rewrite (systemsBlockOps blockValue) }
    rewrite operation = case operation of
      OpScalarLiteral (ValueId "answer") _ ->
        OpScalarLiteral (ValueId "answer") (ScalarUIntLiteral 32 43)
      _ -> operation

sourceReturnTargetDriftRejects :: Bool
sourceReturnTargetDriftRejects =
  case compileRunnable "return-choice.phil" returnChoiceSource of
    Left _ -> False
    Right runnable ->
      let bad = adjustEntryBlock
            (\blockValue -> blockValue
              { systemsBlockTerminator = TermReturnScalar (ValueId "wrong") })
            (runnableSystemsArtifact runnable)
      in case verifyRunnableSourceProjection "return-choice.phil" returnChoiceSource bad of
          Left (RunnableSourceProjectionError SourceProjectionReturnTargetMismatch {}) -> True
          _ -> False

sourceIdentityIsContentBound :: Bool
sourceIdentityIsContentBound =
  case ( compileRunnable "one.phil" bindingSource
       , compileRunnable "two.phil" (bindingSource <> "\n")
       ) of
    (Right first, Right second) -> runnableSourceDigest first /= runnableSourceDigest second
    _ -> False

unitEntryRejectsScalar :: Bool
unitEntryRejectsScalar = case compileRunnableUnit "u32.phil" u32Source of
  Left RunnableFragmentError {} -> True
  _ -> False

nonMainRejects :: Bool
nonMainRejects = fragmentRejects $ Text.unlines
  [ "component not_main provides Unit {"
  , "    return unit"
  , "}"
  ]

unsupportedProvidesRejects :: Bool
unsupportedProvidesRejects = fragmentRejects $ Text.unlines
  [ "component main provides Bool {"
  , "    return true"
  , "}"
  ]

nonUnitReturnRejects :: Bool
nonUnitReturnRejects = fragmentRejects $ Text.unlines
  [ "component main provides Unit {"
  , "    return true"
  , "}"
  ]

nonScalarU32Rejects :: Bool
nonScalarU32Rejects = fragmentRejects $ Text.unlines
  [ "component main provides U32 {"
  , "    return unit"
  , "}"
  ]

u32OverflowRejects :: Bool
u32OverflowRejects = fragmentRejects $ Text.unlines
  [ "component main provides U32 {"
  , "    return 4294967296"
  , "}"
  ]

u32BindingOverflowRejects :: Bool
u32BindingOverflowRejects = fragmentRejects $ Text.unlines
  [ "component main provides U32 {"
  , "    let answer = 4294967296"
  , "    return answer"
  , "}"
  ]

u16ReturnRejects :: Bool
u16ReturnRejects = fragmentRejects $ Text.unlines
  [ "component main provides U16 {"
  , "    return 42"
  , "}"
  ]

scalarExpressionStatementRejects :: Bool
scalarExpressionStatementRejects = fragmentRejects $ Text.unlines
  [ "component main provides U32 {"
  , "    1"
  , "    return 42"
  , "}"
  ]

extraUnitStatementRejects :: Bool
extraUnitStatementRejects = fragmentRejects $ Text.unlines
  [ "component main provides Unit {"
  , "    unit"
  , "    return unit"
  , "}"
  ]

multipleComponentsReject :: Bool
multipleComponentsReject = fragmentRejects $ unitSource <> Text.unlines
  [ "component helper provides Unit {"
  , "    return unit"
  , "}"
  ]

mainFunction :: SystemsArtifact -> Maybe SystemsFunction
mainFunction artifact =
  Map.lookup "main" (systemsProgramFunctions (systemsArtifactProgram artifact))

replaceMainFunction :: SystemsFunction -> SystemsArtifact -> SystemsArtifact
replaceMainFunction functionValue artifact = artifact
  { systemsArtifactProgram = program
      { systemsProgramFunctions = Map.insert "main" functionValue (systemsProgramFunctions program) }
  }
  where
    program = systemsArtifactProgram artifact

adjustEntryBlock :: (SystemsBlock -> SystemsBlock) -> SystemsArtifact -> SystemsArtifact
adjustEntryBlock modify artifact =
  case mainFunction artifact of
    Nothing -> artifact
    Just functionValue ->
      let changed = functionValue
            { systemsFunctionBlocks = Map.adjust modify (BlockId "entry")
                (systemsFunctionBlocks functionValue)
            }
      in replaceMainFunction changed artifact

fragmentRejects :: Text -> Bool
fragmentRejects source = case compileRunnable "invalid.phil" source of
  Left RunnableFragmentError {} -> True
  _ -> False

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
