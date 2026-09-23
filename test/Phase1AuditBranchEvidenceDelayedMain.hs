{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Branch (..)
  , Control (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , Proposition (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( InitialBinding (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

end :: Session
end = End (Outcome "success")

trueBool :: Ty
trueBool =
  TyRefined
    (Name "v")
    TyBool
    (Equal (RefVar (Name "v")) (RefBool True))

baseEnv :: SurfaceEnvironment
baseEnv =
  (emptySurfaceEnvironment emptyStaticContext)
    { surfaceInitialBindings = Map.fromList
        [ ("good", InitialBinding Unrestricted trueBool PlainShape)
        , ("flag", InitialBinding Unrestricted TyBool PlainShape)
        , ("ctx", InitialBinding Unrestricted (TyOpaque "Context") PlainShape)
        , ("ep", InitialBinding Linear
            (TyEndpoint
              (Select
                [ Branch "proceed" Nothing end
                , Branch "reject" Nothing end
                ]))
            PlainShape)
        ]
    , surfaceSelectRequirements = Map.singleton "proceed"
        [Atom "IsTrue" [RefVar (Name "ctx"), RefVar (Name "x")]]
    }

plainEnv :: SurfaceEnvironment
plainEnv =
  baseEnv
    { surfaceInitialBindings = Map.delete "ep" (surfaceInitialBindings baseEnv)
    , surfaceSelectRequirements = Map.empty
    }

main :: IO ()
main = do
  results <- sequence
    [ sourceTest "S01 delayed validation decision cannot escape its subject scope"
        baseEnv (carrierSource False) scopeRejected
    , sourceTest "S02 tuple-carried validation decision cannot escape its subject scope"
        baseEnv (carrierSource True) scopeRejected
    , sourceTest "S03 validation decision about surviving outer subject remains valid"
        baseEnv sourceOuterSubject closed
    , sourceTest "S04 delayed evidence cannot authorize a distinct surviving subject"
        (baseEnv
          { surfaceSelectRequirements = Map.singleton "proceed"
              [Atom "IsTrue" [RefVar (Name "ctx"), RefVar (Name "y")]]
          })
        sourceDistinctSubject
        (rejected MissingEvidence)
    , sourceTest "S05 closed Boolean decision remains a valid carrier"
        baseEnv sourceBooleanCarrier closed
    , sourceTest "S06 source spelling reuse remains allowed without retained support"
        plainEnv sourceSpellingReuse (returned TyBool)
    ]
  unless (and results) exitFailure

sourceTest
  :: String
  -> SurfaceEnvironment
  -> Text
  -> (Either SurfaceCheckError SurfaceCheckResult -> Bool)
  -> IO Bool
sourceTest label environment source oracle =
  case sourceCheck environment source of
    Left detail -> failCase ("setup failure: " <> detail)
    Right observed
      | oracle observed -> passCase
      | otherwise -> failCase ("unexpected result: " <> show observed)
  where
    passCase = do
      putStrLn ("PASS: PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 " <> label)
      pure True
    failCase detail = do
      putStrLn
        ("FAIL: PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 "
          <> label <> " -- " <> detail)
      pure False

sourceCheck
  :: SurfaceEnvironment
  -> Text
  -> Either String (Either SurfaceCheckError SurfaceCheckResult)
sourceCheck environment source =
  case parseSurfaceFile "branch-evidence-delayed-audit.phil" source of
    Left err -> Left (show err)
    Right (SurfaceFile [component]) -> Right (checkSurfaceComponent environment component)
    Right (SurfaceFile components) ->
      Left ("unexpected component count: " <> show (length components))

scopeRejected :: Either SurfaceCheckError SurfaceCheckResult -> Bool
scopeRejected (Left err) =
  surfaceErrorClass err == TypeMismatch
    && "branch result depends on out-of-scope subject(s):"
      `Text.isPrefixOf` surfaceErrorDetail err
scopeRejected _ = False

rejected
  :: RejectionClass
  -> Either SurfaceCheckError SurfaceCheckResult
  -> Bool
rejected expected (Left err) = surfaceErrorClass err == expected
rejected _ _ = False

closed :: Either SurfaceCheckError SurfaceCheckResult -> Bool
closed (Right result) =
  checkedComponentName result == "Audit"
    && not (null (checkedTerminalControls result))
    && all (== Closed (Outcome "success")) (checkedTerminalControls result)
closed _ = False

returned :: Ty -> Either SurfaceCheckError SurfaceCheckResult -> Bool
returned ty (Right result) =
  checkedComponentName result == "Audit"
    && checkedTerminalControls result == [Return ty]
returned _ _ = False

finish :: [Text]
finish =
  [ "let ep1 = decide decision {"
  , " accepted(e) => { select proceed on ep using e }"
  , " rejected(reason) => { select reject on ep }"
  , "}"
  , "close ep1"
  ]

carrierSource :: Bool -> Text
carrierSource tuple = Text.unlines $
  [ "component Audit {"
  , if tuple
      then "let (decision, marker) = decide flag {"
      else "let decision = decide flag {"
  , " true => { let x = (good)"
  , if tuple
      then " (validate IsTrue at ctx on x, unit) }"
      else " validate IsTrue at ctx on x }"
  , " false => { let x = (good)"
  , if tuple
      then " (validate IsTrue at ctx on x, unit) }"
      else " validate IsTrue at ctx on x }"
  , "}"
  , "let x = false"
  ] ++ finish ++ ["}"]

sourceOuterSubject :: Text
sourceOuterSubject = Text.unlines $
  [ "component Audit {"
  , "let x = good"
  , "let decision = decide flag {"
  , " true => { validate IsTrue at ctx on x }"
  , " false => { validate IsTrue at ctx on x }"
  , "}"
  ] ++ finish ++ ["}"]

sourceDistinctSubject :: Text
sourceDistinctSubject = Text.unlines
  [ "component Audit {"
  , "let x = good"
  , "let decision = decide flag {"
  , " true => { validate IsTrue at ctx on x }"
  , " false => { validate IsTrue at ctx on x }"
  , "}"
  , "let y = false"
  , "let ep1 = decide decision {"
  , " accepted(e) => { select proceed on ep using e }"
  , " rejected(reason) => { select reject on ep }"
  , "}"
  , "close ep1"
  , "}"
  ]

sourceBooleanCarrier :: Text
sourceBooleanCarrier = Text.unlines
  [ "component Audit {"
  , "let decision = decide flag { true => { true } false => { false } }"
  , "let ep1 = decide decision {"
  , " true => { select reject on ep }"
  , " false => { select reject on ep }"
  , "}"
  , "close ep1"
  , "}"
  ]

sourceSpellingReuse :: Text
sourceSpellingReuse = Text.unlines
  [ "component Audit {"
  , "let marker = decide flag {"
  , " true => { let x = (good)"
  , " unit }"
  , " false => { let x = (good)"
  , " unit }"
  , "}"
  , "let x = false"
  , "return x"
  , "}"
  ]
