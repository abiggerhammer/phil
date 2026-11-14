{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Focusing (FocusMechanism (..), FocusedRequirement (..))
import Phil.Core.Static (emptyStaticContext, declareOpaqueClaim)
import Phil.Core.Syntax (Mode (..), Name (..), Proposition (..), RefTerm (..), Ty (..))
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
    , check "real accepted Core value evidence survives ordinary source checking" realCoreUse
    , check "Core evidence in both joined branches keeps separate site and route" joinedCoreUses
    , check "repeated checked source sites preserve ordinals and identities" repeatedUses
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


-- These run through the production parser and the exact production checker;
-- neither test constructs a ValueResult or an accepted event manually.
trueBool :: Ty
trueBool = TyRefined (Name "v") TyBool
  (Equal (RefVar (Name "v")) (RefBool True))

coreBase :: SurfaceEnvironment
coreBase = base
  { surfaceInitialBindings = Map.fromList
      [ ("flag", InitialBinding Unrestricted TyBool PlainShape)
      , ("good", InitialBinding Unrestricted trueBool PlainShape)
      , ("other", InitialBinding Unrestricted trueBool PlainShape)
      ]
  , surfaceTypeAliases = Map.singleton "TrueBool" trueBool
  }

realCoreUse :: Either String ()
realCoreUse = do
  events <- checked coreBase
    "component Actual { let value = accept good as TrueBool; return value }"
  let core = [ event | event <- events
        , SourceCoreValueEvidence _ <- [sourceEvidenceUse event] ]
  unless (not (null core) && all (null . sourceEvidenceBranchRoute) core)
    (Left ("real checked Core value evidence missing: " ++ show events))

joinedCoreUses :: Either String ()
joinedCoreUses = do
  events <- checked coreBase $
    "component Joined { let value = decide flag { "
    <> "true => { accept good as TrueBool } "
    <> "false => { accept other as TrueBool } "
    <> "} return value }"
  let core = [ event | event <- events
        , SourceCoreValueEvidence _ <- [sourceEvidenceUse event] ]
      routes = map (map sourceBranchLabel . sourceEvidenceBranchRoute) core
  unless (length core >= 2 && "true" `elem` concat routes
        && "false" `elem` concat routes
        && length (map sourceEvidenceSite core) >= 2)
    (Left ("joined static alternatives lost a Core checked-use event: " ++ show events))

repeatedUses :: Either String ()
repeatedUses = do
  events <- checked base
    "component Repeated { prove true; prove true; return unit }"
  let proofUses = [event | event <- events
        , SourceProveEvidence _ _ <- [sourceEvidenceUse event]]
  unless (length proofUses == 2
      && map sourceEvidenceOrdinal proofUses == [0,1]
      && sourceEvidenceSite (head proofUses) /= sourceEvidenceSite (last proofUses))
    (Left ("repeated source uses lost ordered distinct sites: " ++ show events))

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
