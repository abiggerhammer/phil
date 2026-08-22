{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler
import Phil.LLVM (llvmArtifactText)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "runnable Unit source compiles through verified LLVM" validProgramCompiles
    , test "runnable source identity is content-bound" sourceIdentityIsContentBound
    , test "runnable fragment requires main component" nonMainRejects
    , test "runnable fragment requires Unit provides type" nonUnitProvidesRejects
    , test "runnable fragment requires return unit" nonUnitReturnRejects
    , test "runnable fragment rejects extra statements" extraStatementRejects
    , test "runnable fragment requires one component" multipleComponentsReject
    ]
  if and results then pure () else exitFailure

validSource :: Text
validSource = Text.unlines
  [ "component main provides Unit {"
  , "    return unit"
  , "}"
  ]

validProgramCompiles :: Bool
validProgramCompiles = case compileRunnableUnit "valid.phil" validSource of
  Left _ -> False
  Right runnable ->
    let llvm = llvmArtifactText (runnableLLVMArtifact runnable)
    in Text.isInfixOf "define i32 @main() {" llvm
        && Text.isInfixOf "ret i32 0 ; return-unit" llvm

sourceIdentityIsContentBound :: Bool
sourceIdentityIsContentBound =
  case ( compileRunnableUnit "one.phil" validSource
       , compileRunnableUnit "two.phil" (validSource <> "\n")
       ) of
    (Right first, Right second) -> runnableSourceDigest first /= runnableSourceDigest second
    _ -> False

nonMainRejects :: Bool
nonMainRejects = fragmentRejects $ Text.unlines
  [ "component not_main provides Unit {"
  , "    return unit"
  , "}"
  ]

nonUnitProvidesRejects :: Bool
nonUnitProvidesRejects =
  case compileRunnableUnit "bad-provides.phil" $ Text.unlines
      [ "component main provides Bool {"
      , "    return unit"
      , "}"
      ] of
    Left RunnableSurfaceCheckError {} -> True
    Left RunnableFragmentError {} -> True
    _ -> False

nonUnitReturnRejects :: Bool
nonUnitReturnRejects = fragmentRejects $ Text.unlines
  [ "component main provides Unit {"
  , "    return true"
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
multipleComponentsReject = fragmentRejects $ validSource <> Text.unlines
  [ "component helper provides Unit {"
  , "    return unit"
  , "}"
  ]

fragmentRejects :: Text -> Bool
fragmentRejects source = case compileRunnableUnit "invalid.phil" source of
  Left RunnableFragmentError {} -> True
  _ -> False

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
