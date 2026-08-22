{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Foldable (toList)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler
import Phil.Core.Scalar (ScalarLiteral (ScalarUIntLiteral), ScalarType (ScalarUInt))
import Phil.LLVM (llvmArtifactText)
import Phil.Systems
  ( SystemsArtifact (systemsArtifactProgram)
  , SystemsFunction (systemsFunctionValues)
  , SystemsProgram (systemsProgramFunctions)
  , SystemsValue (systemsValueRole)
  , SystemsValueRole (TypedScalar)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "runnable Unit source compiles through verified LLVM" validUnitCompiles
    , test "runnable U32 source compiles through verified LLVM" validU32Compiles
    , test "U32 scalar type survives into Systems IR" u32TypeSurvivesSystems
    , test "U32 literal and width survive into LLVM SSA" u32ValueSurvivesLLVM
    , test "runnable source identity is content-bound" sourceIdentityIsContentBound
    , test "Unit-only compatibility entry point rejects scalar programs" unitEntryRejectsScalar
    , test "runnable fragment requires main component" nonMainRejects
    , test "runnable fragment rejects unsupported provides type" unsupportedProvidesRejects
    , test "runnable fragment requires matching Unit return" nonUnitReturnRejects
    , test "U32 runnable fragment rejects non-literal return" nonLiteralU32Rejects
    , test "U32 runnable fragment rejects out-of-range literal" u32OverflowRejects
    , test "native runnable scalar ABI currently rejects U16" u16ReturnRejects
    , test "runnable fragment rejects extra statements" extraStatementRejects
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
    runnableResult runnable == RunnableScalar (ScalarUIntLiteral 32 42)

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
        && Text.isInfixOf "%return_value = add i32 0, 42" llvm
        && Text.isInfixOf "ret i32 %return_value" llvm

sourceIdentityIsContentBound :: Bool
sourceIdentityIsContentBound =
  case ( compileRunnable "one.phil" u32Source
       , compileRunnable "two.phil" (u32Source <> "\n")
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

nonLiteralU32Rejects :: Bool
nonLiteralU32Rejects = fragmentRejects $ Text.unlines
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

u16ReturnRejects :: Bool
u16ReturnRejects = fragmentRejects $ Text.unlines
  [ "component main provides U16 {"
  , "    return 42"
  , "}"
  ]

extraStatementRejects :: Bool
extraStatementRejects = fragmentRejects $ Text.unlines
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

fragmentRejects :: Text -> Bool
fragmentRejects source = case compileRunnable "invalid.phil" source of
  Left RunnableFragmentError {} -> True
  _ -> False

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
