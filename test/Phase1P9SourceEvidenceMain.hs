{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Focusing (FocusMechanism (..), FocusedRequirement (..))
import Phil.Core.Static (emptyStaticContext, declareOpaqueClaim)
import Phil.Core.Syntax (Mode (..), Proposition (..), Ty (..))
import Phil.Surface.Check
  ( InitialBinding (..), SourceEvidenceBranch (..), SourceEvidenceEvent (..)
  , SourceEvidenceUse (..), SurfaceEnvironment (..), SurfaceShape (..)
  , checkSurfaceComponent, checkSurfaceComponentWithEvidence, emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ check "empty source has no evidence use" noUses
    , check "two equal-resource branches retain distinct actual evidence" bothBranches
    , check "named proof use retains actual focused binding" namedProof
    , check "ordinary acceptance and observed acceptance are identical" sameAcceptance
    , check "rejected proof cannot mint accepted event" rejectedSource
    ]
  unless (and results) exitFailure

check :: String -> Either String () -> IO Bool
check label result = case result of
  Right () -> putStrLn ("PASS: P9-E1 " ++ label) >> pure True
  Left err -> putStrLn ("FAIL: P9-E1 " ++ label ++ ": " ++ err) >> pure False

checked :: SurfaceEnvironment -> Text -> Either String [SourceEvidenceEvent]
checked env source = do
  parsed <- either (Left . show) Right $ parseSurfaceFile "p9-e1.phil" source
  case parsed of
    SurfaceFile [component] -> do
      (_, events) <- either (Left . show) Right $
        checkSurfaceComponentWithEvidence env component
      Right events
    _ -> Left "expected exactly one checked source component"

base :: SurfaceEnvironment
base = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "flag"
      (InitialBinding Unrestricted TyBool PlainShape)
  }

noUses :: Either String ()
noUses = do
  events <- checked base "component Empty { return unit }"
  unless (null events) (Left ("empty source invented use: " ++ show events))

bothBranches :: Either String ()
bothBranches = do
  events <- checked base "component Branch { let p = decide flag { true => { prove true } false => { prove true } } return p }"
  let routes =
        [ map sourceBranchLabel (sourceEvidenceBranchRoute event)
        | event <- events
        , SourceProveEvidence _ _ <- [sourceEvidenceUse event]
        ]
  unless (length routes == 2 && routes == [["true"],["false"]]) $
    Left ("missing/duplicated branch observations: " ++ show routes)

namedProof :: Either String ()
namedProof = do
  static <- either (Left . show) Right $
    declareOpaqueClaim "OpaqueClaim" [] emptyStaticContext
  let env = (emptySurfaceEnvironment static)
        { surfaceInitialBindings = Map.singleton "evidence"
            (InitialBinding Unrestricted (TyProof (Atom "OpaqueClaim" [])) PlainShape)
        }
  events <- checked env "component Named { prove OpaqueClaim() }"
  let named = [ ()
        | event <- events
        , SourceProveEvidence requirement False <- [sourceEvidenceUse event]
        , FocusByEvidence _ <- [focusedMechanism requirement]
        ]
  unless (length named == 1) (Left ("no named use: " ++ show events))

sameAcceptance :: Either String ()
sameAcceptance = do
  parsed <- either (Left . show) Right $
    parseSurfaceFile "p9-e1.phil" "component Plain { prove true }"
  case parsed of
    SurfaceFile [component] -> do
      plain <- either (Left . show) Right $ checkSurfaceComponent base component
      (observed, _) <- either (Left . show) Right $
        checkSurfaceComponentWithEvidence base component
      unless (plain == observed) (Left "observational path changed accepted result")
    _ -> Left "expected exactly one component"

rejectedSource :: Either String ()
rejectedSource = do
  parsed <- either (Left . show) Right $
    parseSurfaceFile "p9-e1.phil" "component Invalid { prove false }"
  case parsed of
    SurfaceFile [component] ->
      case checkSurfaceComponentWithEvidence base component of
        Left _ -> Right ()
        Right actual -> Left ("unjustified acceptance: " ++ show actual)
    _ -> Left "expected exactly one component"
