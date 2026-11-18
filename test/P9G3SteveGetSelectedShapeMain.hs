{-# LANGUAGE OverloadedStrings #-}

-- P9-G3 FSEM-05/06: a read-only, exact selected-AST/selected-Core
-- *shape* validator. It checks the real parser output and separately
-- supplied production Core against an independently written literal
-- closed-fragment description. This is NOT a source evaluator,
-- semantics soundness theorem, or source-to-machine certificate.
module Main (main) where

import Control.Monad (guard, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Examples.Phase1.SystemsWitnesses (steveCoreProgram)
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax
import Phil.Systems.GenericLowering
  ( CoreSystemsBlock (..), CoreSystemsFunction (..)
  , CoreSystemsOperation (..), CoreSystemsProgram (..)
  , CoreSystemsTerminator (..), CoreSystemsValue (..)
  , CoreSystemsValueRole (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  original <- TextIO.readFile "examples/steve/get.phil"
  require "actual parsed SteveGet source matches the ENTIRE closed fragment"
    (matchesSource original)
  require "actual selected supplied Core has EXACT source-fragment CFG/roles"
    (matchesCore steveCoreProgram)
  mapM_ (\(label, before, after) -> do
    let mutated = Text.replace before after original
    require ("mutation changes source: " <> label) (mutated /= original)
    require ("rejected source mutation: " <> label)
      (not (matchesSource mutated)))
    sourceMutations
  let selected = case Map.lookup "SteveGet" (coreProgramFunctions steveCoreProgram) of
        Just value -> value
        Nothing -> error "SteveGet missing"
      blocks = coreFunctionBlocks selected
      changed name change = selected
        { coreFunctionBlocks = Map.adjust change name blocks }
      withFunction f = steveCoreProgram
        { coreProgramFunctions =
            Map.insert "SteveGet" f (coreProgramFunctions steveCoreProgram) }
  require "reject Core digest arguments reordered" $
    not (matchesCore (withFunction (changed "get.check" $ \block ->
      block { coreBlockTerminator =
        CoreSystemsRuntimeChoice "DigestProvider.check"
          ["get.bytes-view", "get.id"] Nothing digestArms })))
  require "reject Core release omitted on accepted branch" $
    not (matchesCore (withFunction (changed "get.ok" $ \block ->
      block { coreBlockOperations = [CoreTrace "steve.get.commit"] })))
  require "reject Core release hoisted before digest" $
    not (matchesCore (withFunction (changed "get.check" $ \block ->
      block { coreBlockOperations = [CoreReleaseOwner "cleanup" "get.bytes"] })))
  require "reject Core wrong branch entry" $
    not (matchesCore (withFunction
      (selected { coreFunctionEntry = "get.check" })))
  require "reject extra unreachable Core block" $
    not (matchesCore (withFunction (selected
      { coreFunctionBlocks = Map.insert "get.unreachable"
          (CoreSystemsBlock "get.unreachable" [] (CoreSystemsEnd "success"))
          blocks })))
  putStrLn "PASS: P9-G3 exact selected source AST/Core CFG fragment discrimination"

require :: String -> Bool -> IO ()
require label accepted =
  if accepted
    then putStrLn ("PASS: " <> label)
    else putStrLn ("FAIL: " <> label) >> exitFailure

sourceMutations :: [(String, Text, Text)]
sourceMutations =
  [ ("found owner rebinding", "found(bytes)", "found(other)")
  , ("borrow wrong owner", "borrow bytes as bytesView",
       "borrow contentId as bytesView")
  , ("swapped digest operands", "digest_check(contentId, bytesView)",
       "digest_check(bytesView, contentId)")
  , ("duplicate digest in accepted arm", "accepted => {",
       "accepted => {\n                    digest_check(contentId, bytesView)")
  , ("wrong result binder", "let digestDecision", "let otherDecision")
  , ("wrong released owner", "release bytes", "release contentId")
  , ("wrong not-found branch name", "not-found =>", "notfound =>")
  ]

-- This is deliberately a WHOLE-AST-shape admission, not a name-occurs-
-- somewhere test. Only source spans are ignored. No extra statement,
-- alternate arm, hidden call or changed release can be silently accepted.
matchesSource :: Text -> Bool
matchesSource source = case parseSurfaceFile "examples/steve/get.phil" source of
  Right parsed -> maybe False (const True) (selectedSource parsed)
  Left _ -> False

selectedSource :: SurfaceFile -> Maybe ()
selectedSource (SurfaceFile [locatedComponent]) = do
  let component = locatedValue locatedComponent
  guard (componentName component == "SteveGet"
    && null (componentParameters component))
  provided <- componentProvides component
  guard (locatedValue provided == SurfaceUnitType)
  [statement] <- pure (blockStatements (locatedValue (componentBody component)))
  root <- expressionStatement statement
  (readCall, readArms) <- decide root
  (readName, [contentId]) <- call readCall
  guard (readName == "blob_read" && isVar "contentId" contentId)
  [found, missing, failure] <- pure readArms
  guard (patternIs "found" ["bytes"] found
    && patternIs "not-found" [] missing
    && patternIs "storage-failure" ["reason"] failure)
  foundBody (caseArmBody (locatedValue found))
  guard (returnOnly (caseArmBody (locatedValue missing)))
  guard (returnOnly (caseArmBody (locatedValue failure)))
selectedSource _ = Nothing

foundBody :: Located Block -> Maybe ()
foundBody locatedBlock = do
  [borrowStmt, decideStmt] <-
    pure (blockStatements (locatedValue locatedBlock))
  (bound, borrowed) <- letStatement borrowStmt
  guard (locatedValue bound == BindPattern "digestDecision")
  (owner, view, scoped) <- borrow borrowed
  guard (isVar "bytes" owner && view == "bytesView")
  [digestStmt] <- pure (blockStatements (locatedValue scoped))
  digest <- expressionStatement digestStmt
  (digestName, [idArg, viewArg]) <- call digest
  guard (digestName == "digest_check"
    && isVar "contentId" idArg && isVar "bytesView" viewArg)
  decision <- expressionStatement decideStmt
  (scrutinee, outcomes) <- decide decision
  guard (isVar "digestDecision" scrutinee)
  [accepted, rejected] <- pure outcomes
  guard (patternIs "accepted" [] accepted
    && patternIs "rejected" ["reason"] rejected)
  guard (releaseThenReturn (caseArmBody (locatedValue accepted))
    && releaseThenReturn (caseArmBody (locatedValue rejected)))

expressionStatement :: Located Statement -> Maybe (Located SurfaceExpression)
expressionStatement stmt = case locatedValue stmt of
  ExpressionStatement value -> Just value
  _ -> Nothing

letStatement :: Located Statement
  -> Maybe (Located Pattern, Located SurfaceExpression)
letStatement stmt = case locatedValue stmt of
  LetStatement binding value -> Just (binding, value)
  _ -> Nothing

borrow :: Located SurfaceExpression
  -> Maybe (Located SurfaceExpression, Text, Located Block)
borrow expr = case locatedValue expr of
  BorrowExpression owner view body -> Just (owner, view, body)
  _ -> Nothing

decide :: Located SurfaceExpression
  -> Maybe (Located SurfaceExpression, [Located CaseArm])
decide expr = case locatedValue expr of
  DecideExpression scrutinee arms -> Just (scrutinee, arms)
  _ -> Nothing

call :: Located SurfaceExpression
  -> Maybe (Text, [Located SurfaceExpression])
call expr = case locatedValue expr of
  CallExpression name arguments -> Just (name, arguments)
  _ -> Nothing

isVar :: Text -> Located SurfaceExpression -> Bool
isVar name expr = locatedValue expr == VariableExpression name

patternIs :: Text -> [Text] -> Located CaseArm -> Bool
patternIs label binders arm =
  casePatternLabel patternValue == label
    && casePatternBinders patternValue == binders
  where
    patternValue = caseArmPattern (locatedValue arm)

returnOnly :: Located Block -> Bool
returnOnly block = case blockStatements (locatedValue block) of
  [stmt] -> case locatedValue stmt of
    ReturnStatement value -> locatedValue value == UnitExpression
    _ -> False
  _ -> False

releaseThenReturn :: Located Block -> Bool
releaseThenReturn block = case blockStatements (locatedValue block) of
  [first, second] -> case (locatedValue first, locatedValue second) of
    (ExpressionStatement rel, ReturnStatement ret) ->
      locatedValue rel == ReleaseExpression (varAt rel "bytes")
        && locatedValue ret == UnitExpression
    _ -> False
  _ -> False

-- Only the semantic variable spelling matters, not the source span.
varAt :: Located SurfaceExpression -> Text -> Located SurfaceExpression
varAt outer name = Located (locatedSpan outer) (VariableExpression name)

matchesCore :: CoreSystemsProgram -> Bool
matchesCore program =
  case Map.lookup "SteveGet" (coreProgramFunctions program) of
    Just selected -> selected == expectedGet
    Nothing -> False

expectedGet :: CoreSystemsFunction
expectedGet = CoreSystemsFunction
  { coreFunctionKey = "SteveGet"
  , coreFunctionEntry = "get.entry"
  , coreFunctionValues = Map.fromList
      [ value "get.id" (CoreRuntimeScalar "ContentId[SHA256]") Nothing
      , value "get.bytes" (CoreOwnedBuffer "OwnedBytes")
          (Just "steve.read-result")
      , value "get.bytes-view" (CoreBorrowedValue "get.bytes") Nothing
      ]
  , coreFunctionBlocks = Map.fromList
      [ block "get.entry" [] (CoreSystemsRuntimeChoice
          "BlobProvider.read" ["get.id"] Nothing readArms)
      , block "get.check" [] (CoreSystemsRuntimeChoice
          "DigestProvider.check" ["get.id", "get.bytes-view"] Nothing digestArms)
      , block "get.ok"
          [CoreReleaseOwner "cleanup" "get.bytes", CoreTrace "steve.get.commit"]
          (CoreSystemsEnd "success")
      , block "get.not-found" [] (CoreSystemsEnd "not-found")
      , block "get.integrity-failure"
          [CoreReleaseOwner "cleanup" "get.bytes"]
          (CoreSystemsEnd "integrity-failure")
      , block "get.failure" [] (CoreSystemsEnd "storage-failure")
      ]
  }
  where
    value name role storage =
      (name, CoreSystemsValue name role storage)
    block name ops terminator =
      (name, CoreSystemsBlock name ops terminator)

readArms :: Map.Map Text Text
readArms = Map.fromList
  [ ("found", "get.check")
  , ("not-found", "get.not-found")
  , ("storage-failure", "get.failure")
  ]

digestArms :: Map.Map Text Text
digestArms = Map.fromList
  [ ("accepted", "get.ok")
  , ("rejected", "get.integrity-failure")
  ]
