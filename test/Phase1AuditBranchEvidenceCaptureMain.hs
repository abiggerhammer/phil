{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..), emptyCheckState, emitObligation)
import Phil.Core.Context
  ( CheckError (..)
  , emptyContext
  , insertBinding
  , joinContinuing
  , startSharedLoan
  )
import Phil.Core.Process (continueFlow, flowPaths, joinBranches, pathState)
import Phil.Core.Refinement (RefinementError (StaticallyFalse))
import Phil.Core.Session
  ( SessionStep (..)
  , closeEndpoint
  , selectEndpoint
  )
import Phil.Core.Static (StaticContext (..))
import Phil.Core.Syntax
  ( Branch (..)
  , Control (..)
  , Mode (..)
  , Name (..)
  , Obligation (..)
  , ObligationId (..)
  , Outcome (..)
  , Proposition (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value
  ( ValueError (..)
  , ValueResult (..)
  , checkValue
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

data Observed
  = SurfaceOK SurfaceCheckResult
  | SurfaceNo SurfaceCheckError
  | Checked Bool
  deriving (Show)

trueBool :: Ty
trueBool =
  TyRefined
    (Name "v")
    TyBool
    (Equal (RefVar (Name "v")) (RefBool True))

baseEnv :: SurfaceEnvironment
baseEnv =
  (emptySurfaceEnvironment (StaticContext Map.empty))
    { surfaceInitialBindings = Map.fromList
        [ ("good", InitialBinding Unrestricted trueBool PlainShape)
        , ("flag", InitialBinding Unrestricted TyBool PlainShape)
        ]
    , surfaceTypeAliases = Map.singleton "TrueBool" trueBool
    }

offerEnv :: SurfaceEnvironment
offerEnv =
  baseEnv
    { surfaceInitialBindings =
        Map.insert
          "ep"
          (InitialBinding
            Linear
            (TyEndpoint
              (Offer
                [Branch
                  "take"
                  (Just (Name "formal", trueBool))
                  (End (Outcome "success"))
                ]))
            PlainShape)
          (surfaceInitialBindings baseEnv)
    }

linearEnv :: SurfaceEnvironment
linearEnv =
  baseEnv
    { surfaceInitialBindings =
        Map.insert
          "token"
          (InitialBinding Linear (TyOpaque "Token") PlainShape)
          (surfaceInitialBindings baseEnv)
    }

main :: IO ()
main = do
  results <- sequence
    [ sourceTest "R01 flat branch proof cannot certify later false value"
        baseEnv sourceR01 scopeRejected
    , sourceTest "R02 tuple-carried proof cannot capture reused local spelling"
        baseEnv sourceR02 scopeRejected
    , sourceTest "R03 nested alternative cleanup cannot retarget evidence"
        baseEnv sourceR03 scopeRejected
    , sourceTest "R04 offer-local proof cannot certify later false value"
        offerEnv sourceR04 scopeRejected
    , sourceTest "C01 legitimate refined input remains accepted"
        baseEnv sourceC01 (returned trueBool)
    , sourceTest "C02 false value without evidence rejects"
        baseEnv sourceC02 (rejected MissingEvidence)
    , sourceTest "C03 proof about outer subject does not certify new subject"
        baseEnv sourceC03 (rejected MissingEvidence)
    , sourceTest "C04 renamed escaped subject remains rejected"
        baseEnv sourceC04 scopeRejected
    , sourceTest "C05 closed proof may leave a branch"
        baseEnv sourceC05 (returned (TyProof Truth))
    , sourceTest "C06 self-contained refined value may leave a branch"
        baseEnv sourceC06 (returned trueBool)
    , sourceTest "C07 closed local spelling may be reused"
        baseEnv sourceC07 (returned TyBool)
    , sourceTest "C08 unconsumed linear branch-local rejects"
        linearEnv sourceC08 (rejected LinearCompletion)
    , sourceTest "C09 properly transferred linear branch result remains accepted"
        linearEnv sourceC09 (returned (TyOpaque "Token"))
    , sourceTest "C10 offer evidence remains usable inside its own scope"
        offerEnv sourceC10 closed
    , coreTest "K01 identical resource join preserves exact map" k01
    , coreTest "K02 different unrestricted types reject at join" k02
    , coreTest "K03 affine intersection drops missing occurrence" k03
    , coreTest "K04 active loan rejects at resource join" k04
    , coreTest "K05 Core process join retains path residual maps" k05
    , coreTest "K06 guarded recursion progresses and closes exactly" k06
    , coreTest "K07 Core constructs true refinement and rejects false" k07
    ]
  unless (and results) exitFailure

sourceTest
  :: String
  -> SurfaceEnvironment
  -> Text
  -> (Observed -> Bool)
  -> IO Bool
sourceTest label environment source oracle =
  case sourceCheck environment source of
    Left detail -> failCase ("setup failure: " <> detail)
    Right observed
      | oracle observed -> passCase
      | otherwise -> failCase ("unexpected result: " <> show observed)
  where
    passCase =
      putStrLn ("PASS: PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 " <> label)
        >> pure True
    failCase detail =
      putStrLn
        ("FAIL: PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 "
          <> label <> " -- " <> detail)
        >> pure False

coreTest :: String -> Either String Observed -> IO Bool
coreTest label result =
  case result of
    Right observed | checked observed ->
      putStrLn ("PASS: PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 " <> label)
        >> pure True
    Right observed ->
      putStrLn
        ("FAIL: PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 "
          <> label <> " -- " <> show observed)
        >> pure False
    Left detail ->
      putStrLn
        ("FAIL: PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 "
          <> label <> " -- " <> detail)
        >> pure False

sourceCheck :: SurfaceEnvironment -> Text -> Either String Observed
sourceCheck environment source =
  case parseSurfaceFile "branch-evidence-audit.phil" source of
    Left err -> Left (show err)
    Right (SurfaceFile [component]) ->
      Right $
        case checkSurfaceComponent environment component of
          Left err -> SurfaceNo err
          Right result -> SurfaceOK result
    Right (SurfaceFile components) ->
      Left ("unexpected component count: " <> show (length components))

returned :: Ty -> Observed -> Bool
returned ty (SurfaceOK result) =
  checkedComponentName result == "Audit"
    && checkedTerminalControls result == [Return ty]
returned _ _ = False

closed :: Observed -> Bool
closed (SurfaceOK result) =
  checkedComponentName result == "Audit"
    && checkedTerminalControls result == [Closed (Outcome "success")]
closed _ = False

rejected :: RejectionClass -> Observed -> Bool
rejected expected (SurfaceNo err) = surfaceErrorClass err == expected
rejected _ _ = False

scopeRejected :: Observed -> Bool
scopeRejected (SurfaceNo err) =
  surfaceErrorClass err `elem`
    [ MissingEvidence
    , StructuralUse
    , TypeMismatch
    , IncompatibleBranchResidue
    ]
scopeRejected _ = False

checked :: Observed -> Bool
checked (Checked result) = result
checked _ = False

mapError :: Show e => Either e a -> Either String a
mapError = either (Left . show) Right

k01, k02, k03, k04, k05, k06, k07 :: Either String Observed
k01 = do
  context <-
    mapError $
      insertBinding Unrestricted (Name "shared") TyBool emptyContext
  Right (Checked (joinContinuing [context, context] == Right context))

k02 = do
  left <-
    mapError $
      insertBinding Unrestricted (Name "shared") TyBool emptyContext
  right <-
    mapError $
      insertBinding Unrestricted (Name "shared") (TyUInt 16) emptyContext
  Right $
    Checked $
      case joinContinuing [left, right] of
        Left (UnrestrictedBranchMismatch _ _) -> True
        _ -> False

k03 = do
  left <-
    mapError $
      insertBinding Affine (Name "optional") TyBool emptyContext
  right <-
    mapError $
      insertBinding Affine (Name "optional") (TyUInt 16) emptyContext
  Right (Checked (joinContinuing [left, emptyContext, right] == Right emptyContext))

k04 = do
  initial <-
    mapError $
      insertBinding Linear (Name "owner") (TyOpaque "Token") emptyContext
  loaned <- mapError $ startSharedLoan (Name "owner") initial
  Right $
    Checked $
      case joinContinuing [loaned] of
        Left (EscapingLoans loans) -> loans == Set.singleton (Name "owner")
        _ -> False

k05 = do
  let obligationA =
        Obligation
          (ObligationId "audit.a")
          Truth
          "audit"
          "left"
          "return"
      obligationB =
        Obligation
          (ObligationId "audit.b")
          Truth
          "audit"
          "right"
          "return"
  left <- mapError $ emitObligation obligationA emptyCheckState
  right <- mapError $ emitObligation obligationB emptyCheckState
  joined <- mapError $ joinBranches [continueFlow left, continueFlow right]
  Right $
    Checked $
      map (residualObligations . pathState) (flowPaths joined)
        == [residualObligations left, residualObligations right]

k06 = do
  let loop =
        Rec
          (Name "R")
          (Select
            [ Branch "again" Nothing (SessionVar (Name "R"))
            , Branch "done" Nothing (End (Outcome "success"))
            ])
  initial <-
    mapError $
      insertBinding Linear (Name "ep") (TyEndpoint loop) emptyContext
  first <-
    mapError $
      selectEndpoint (Name "ep") (Name "ep1") "again" initial
  final <-
    mapError $
      selectEndpoint
        (Name "ep1")
        (Name "ep2")
        "done"
        (stepContext first)
  result <-
    mapError $
      closeEndpoint
        (Name "ep2")
        (Outcome "success")
        (stepContext final)
  Right $
    Checked $
      stepSuccessor first == Just (Name "ep1", loop)
        && stepSuccessor final
          == Just (Name "ep2", End (Outcome "success"))
        && stepContext result == emptyContext
        && stepSuccessor result == Nothing

k07 = do
  good <- mapError $ checkValue (VBool True) trueBool emptyCheckState
  Right $
    Checked $
      valueResultType good == trueBool
        && valueResultState good == emptyCheckState
        && case checkValue (VBool False) trueBool emptyCheckState of
          Left (ValueRefinementError (StaticallyFalse _)) -> True
          _ -> False

sourceR01, sourceR02, sourceR03, sourceR04 :: Text
sourceR01 = Text.unlines
  [ "component Audit {"
  , "let escaped = decide flag {"
  , "  true => { let x = good"
  , "            prove x == true }"
  , "  false => { let x = good"
  , "             prove x == true }"
  , "}"
  , "let x = false"
  , "let checked = accept x as TrueBool"
  , "return checked"
  , "}"
  ]

sourceR02 = Text.unlines
  [ "component Audit {"
  , "let (escaped, marker) = decide flag {"
  , "  true => { let x = good"
  , "            let p = prove x == true"
  , "            (p, unit) }"
  , "  false => { let x = good"
  , "             let p = prove x == true"
  , "             (p, unit) }"
  , "}"
  , "let x = false"
  , "let checked = accept x as TrueBool"
  , "return checked"
  , "}"
  ]

sourceR03 = Text.unlines
  [ "component Audit {"
  , "let escaped = decide flag {"
  , "  true => { decide flag {"
  , "    true => { let x = good"
  , "              prove x == true }"
  , "    false => { let x = good"
  , "               prove x == true }"
  , "  } }"
  , "  false => { decide flag {"
  , "    true => { let x = good"
  , "              prove x == true }"
  , "    false => { let x = good"
  , "               prove x == true }"
  , "  } }"
  , "}"
  , "let x = false"
  , "let checked = accept x as TrueBool"
  , "return checked"
  , "}"
  ]

sourceR04 = Text.unlines
  [ "component Audit {"
  , "let escaped = offer ep {"
  , "  take(x) => { prove x == true }"
  , "}"
  , "let x = false"
  , "let checked = accept x as TrueBool"
  , "close ep"
  , "}"
  ]

sourceC01, sourceC02, sourceC03, sourceC04, sourceC05 :: Text
sourceC06, sourceC07, sourceC08, sourceC09, sourceC10 :: Text
sourceC01 = Text.unlines
  [ "component Audit {"
  , "let checked = accept good as TrueBool"
  , "return checked"
  , "}"
  ]

sourceC02 = Text.unlines
  [ "component Audit {"
  , "let x = false"
  , "let checked = accept x as TrueBool"
  , "return checked"
  , "}"
  ]

sourceC03 = Text.unlines
  [ "component Audit {"
  , "let escaped = decide flag {"
  , "  true => { prove good == true }"
  , "  false => { prove good == true }"
  , "}"
  , "let x = false"
  , "let checked = accept x as TrueBool"
  , "return checked"
  , "}"
  ]

sourceC04 = Text.unlines
  [ "component Audit {"
  , "let escaped = decide flag {"
  , "  true => { let y = good"
  , "            prove y == true }"
  , "  false => { let y = good"
  , "             prove y == true }"
  , "}"
  , "let x = false"
  , "let checked = accept x as TrueBool"
  , "return checked"
  , "}"
  ]

sourceC05 = Text.unlines
  [ "component Audit {"
  , "let escaped = decide flag {"
  , "  true => { prove true }"
  , "  false => { prove true }"
  , "}"
  , "return escaped"
  , "}"
  ]

sourceC06 = Text.unlines
  [ "component Audit {"
  , "let chosen = decide flag {"
  , "  true => { let x = good"
  , "            x }"
  , "  false => { let x = good"
  , "             x }"
  , "}"
  , "let x = false"
  , "return chosen"
  , "}"
  ]

sourceC07 = Text.unlines
  [ "component Audit {"
  , "let marker = decide flag {"
  , "  true => { let x = good"
  , "            unit }"
  , "  false => { let x = good"
  , "             unit }"
  , "}"
  , "let x = false"
  , "return x"
  , "}"
  ]

sourceC08 = Text.unlines
  [ "component Audit {"
  , "let marker = decide flag {"
  , "  true => { let owned = token"
  , "            unit }"
  , "  false => { let owned = token"
  , "             unit }"
  , "}"
  , "return unit"
  , "}"
  ]

sourceC09 = Text.unlines
  [ "component Audit {"
  , "let chosen = decide flag {"
  , "  true => { let owned = token"
  , "            owned }"
  , "  false => { let owned = token"
  , "             owned }"
  , "}"
  , "return chosen"
  , "}"
  ]

sourceC10 = Text.unlines
  [ "component Audit {"
  , "offer ep {"
  , "  take(x) => { let checked = accept x as TrueBool"
  , "              unit }"
  , "}"
  , "close ep"
  , "}"
  ]