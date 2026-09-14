{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( CallableOutcomeControlSpec (..)
  , CallableOutcomeSpec (..)
  , InitialBinding (..)
  , RejectionClass (..)
  , SurfaceCallableSignature (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , CallableOutcomeResourceBinding (..)
  , CallableOutcomeResourceSpec (..)
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax
  ( Block (..)
  , Component (..)
  , Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceFile (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 exact occurrence resource residue reaches Surface arms"
        exactResidueReachesArms
    , test "CALL-019 legacy callable path stays resource-neutral"
        noResiduePreservesLegacyState
    , test "CALL-019 partial occurrence resource coverage rejects"
        partialCoverageRejects
    , test "CALL-019 resource residue from another occurrence is ignored"
        wrongOccurrenceDoesNotApply
    , test "CALL-019 sibling resource residue still obeys ordinary join discipline"
        mismatchedSiblingResidueRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

ownerMeta :: BindingMeta
ownerMeta = BindingMeta Linear (TyOpaque "Owner") PlainShape

baseEnvironment :: SurfaceEnvironment
baseEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "owner"
      (InitialBinding Linear (TyOpaque "Owner") PlainShape)
  , surfaceCallables = Map.singleton "Worker" SurfaceCallableSignature
      { surfaceCallableDeclarationKey = workerKey
      , surfaceCallableParameters = []
      , surfaceCallableResult = Nothing
      }
  , surfaceCallableOutcomes = Map.singleton workerKey
      [ outcomeSpec "ok"
      , outcomeSpec "retry"
      ]
  }

outcomeSpec :: Text -> CallableOutcomeSpec
outcomeSpec label = CallableOutcomeSpec
  { callableOutcomeLabel = label
  , callableOutcomePayload = []
  , callableOutcomeControl = CallableOutcomeContinues
  , callableOutcomeFacts = []
  , callableOutcomeResidualObligationArity = 0
  , callableOutcomeObligations = []
  }

source :: Text
source =
  "component Caller { "
    <> "decide invoke Worker() { ok => { unit } retry => { unit } } "
    <> "return unit }"

absentOwnerSpec :: CallableOutcomeResourceSpec
absentOwnerSpec = CallableOutcomeResourceSpec
  { callableOutcomeResourceBindings =
      Map.singleton "owner" CallableOutcomeResourceAbsent
  , callableOutcomeResourceActiveEndpoint = Nothing
  }

presentOwnerSpec :: CallableOutcomeResourceSpec
presentOwnerSpec = CallableOutcomeResourceSpec
  { callableOutcomeResourceBindings =
      Map.singleton "owner" (CallableOutcomeResourcePresent ownerMeta)
  , callableOutcomeResourceActiveEndpoint = Nothing
  }

exactResidueReachesArms :: Either String ()
exactResidueReachesArms = do
  component <- parseOne
  invocationSpan <- invocationSpanOf component
  let environment = baseEnvironment
        { surfaceCallableOutcomeResources = Map.fromList
            [ ((invocationSpan, workerKey, "ok"), absentOwnerSpec)
            , ((invocationSpan, workerKey, "retry"), absentOwnerSpec)
            ]
        }
  _ <- mapLeft show (checkSurfaceComponent environment component)
  Right ()

noResiduePreservesLegacyState :: Either String ()
noResiduePreservesLegacyState = do
  component <- parseOne
  expectClass LinearCompletion (checkSurfaceComponent baseEnvironment component)

partialCoverageRejects :: Either String ()
partialCoverageRejects = do
  component <- parseOne
  invocationSpan <- invocationSpanOf component
  let environment = baseEnvironment
        { surfaceCallableOutcomeResources = Map.singleton
            (invocationSpan, workerKey, "ok")
            absentOwnerSpec
        }
  expectClass IncompatibleBranchResidue
    (checkSurfaceComponent environment component)

wrongOccurrenceDoesNotApply :: Either String ()
wrongOccurrenceDoesNotApply = do
  component <- parseOne
  let wrongSpan = SourceSpan
        (SourcePoint "wrong-occurrence" 9 1 900)
        (SourcePoint "wrong-occurrence" 9 2 901)
      environment = baseEnvironment
        { surfaceCallableOutcomeResources = Map.fromList
            [ ((wrongSpan, workerKey, "ok"), absentOwnerSpec)
            , ((wrongSpan, workerKey, "retry"), absentOwnerSpec)
            ]
        }
  expectClass LinearCompletion (checkSurfaceComponent environment component)

mismatchedSiblingResidueRejects :: Either String ()
mismatchedSiblingResidueRejects = do
  component <- parseOne
  invocationSpan <- invocationSpanOf component
  let environment = baseEnvironment
        { surfaceCallableOutcomeResources = Map.fromList
            [ ((invocationSpan, workerKey, "ok"), absentOwnerSpec)
            , ((invocationSpan, workerKey, "retry"), presentOwnerSpec)
            ]
        }
  expectClass IncompatibleBranchResidue
    (checkSurfaceComponent environment component)

expectClass
  :: RejectionClass
  -> Either SurfaceCheckError a
  -> Either String ()
expectClass expected result = case result of
  Left errorValue
    | surfaceErrorClass errorValue == expected -> Right ()
    | otherwise -> Left
        ("expected " <> show expected <> ", got " <> show errorValue)
  Right _ -> Left ("expected rejection " <> show expected <> ", but check succeeded")

invocationSpanOf :: Located Component -> Either String SourceSpan
invocationSpanOf locatedComponent =
  case blockStatements (locatedValue (componentBody (locatedValue locatedComponent))) of
    Located _ (ExpressionStatement decision) : _ ->
      case locatedValue decision of
        DecideExpression scrutinee _ -> Right (locatedSpan scrutinee)
        other -> Left ("expected decide expression, got " <> show other)
    statements -> Left
      ("expected leading decision statement, got " <> show (length statements))

parseOne :: Either String (Located Component)
parseOne = do
  parsed <- mapLeft show (parseSurfaceFile "call019-surface-arm-resources" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
