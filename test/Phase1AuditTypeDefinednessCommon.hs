{-# LANGUAGE OverloadedStrings #-}
module Phase1AuditTypeDefinednessCommon
  ( Mode (..), Result, runCases, eq, require, namedContext, sameContext
  , boolState, q, bad, badPredicate, refined, noResidual, checkFalse
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import qualified Phil.Core.Context as Context
import Phil.Core.Refinement (RefinementError (..))
import Phil.Core.SortCheck (SortError (..))
import Phil.Core.Static (StaticContext, declareTransparentClaim, emptyStaticContext)
import Phil.Core.Syntax
  ( Name (..), Proposition (..), RefSort (..), RefTerm (..), Ty (..) )
import qualified Phil.Core.Syntax as Syntax
import Phil.Core.Value (ValueError (..), ValueResult (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)

data Mode = Regression | Characterize deriving (Eq, Show)
type Result = Either String ()

runCases :: (Mode -> [(String, Result)]) -> [(String, Result)] -> IO ()
runCases checks observations = do
  args <- getArgs
  case args of
    [] -> execute Regression False
    ["--characterize"] -> execute Characterize False
    ["--observations"] -> execute Regression True
    ["--characterize", "--observations"] -> execute Characterize True
    _ -> putStrLn "usage: [--characterize] [--observations]" >> exitFailure
  where
    execute mode includeObservations = do
      outcomes <- mapM (emit "CHECK" (if mode == Regression then "PASS" else "MATCH")) (checks mode)
      observed <- if includeObservations then mapM (emit "OBSERVE" "MATCH") observations else pure []
      if and (outcomes ++ observed) then pure () else exitFailure
    emit kind success (ident, result) = case result of
      Right () -> putStrLn (kind <> "\t" <> ident <> "\t" <> success) >> pure True
      Left detail -> do
        putStrLn (kind <> "\t" <> ident <> "\tFAIL")
        putStrLn ("DETAIL " <> ident <> " " <> filter (/= '\n') detail)
        pure False

eq :: (Eq a, Show a) => a -> a -> Result
eq actual expected = require (actual == expected)
  ("expected " <> show expected <> "; got " <> show actual)

require :: Bool -> String -> Result
require True _ = Right ()
require False message = Left message

q :: Name
q = Name "q"

bad :: RefTerm
bad = RefSub (RefNat 3) (RefNat 5)

badPredicate :: Proposition
badPredicate = Equal bad bad

refined :: Proposition -> Ty
refined = TyRefined (Name "s") TyBool

boolState :: Either String CheckState
boolState = do
  context <- either (Left . show) Right $
    Context.insertBinding Syntax.Unrestricted q TyBool (resourceContext emptyCheckState)
  pure emptyCheckState { resourceContext = context }

namedContext :: Text -> Name -> Either String StaticContext
namedContext claim second = either (Left . show) Right $
  declareTransparentClaim claim
    [(Name "p", SortBool), (second, SortBool)]
    (Equal (RefVar (Name "p")) (RefVar second)) emptyStaticContext

sameContext :: Either String StaticContext
sameContext = namedContext "Same" q

noResidual :: ValueResult -> Result
noResidual = flip eq Map.empty . residualObligations . valueResultState

-- Only a definedness/refinement rejection is accepted here. A resource error,
-- parser failure, missing module, or unrelated type mismatch is not a pass.
checkFalse :: Either ValueError ValueResult -> Result
checkFalse result = case result of
  Left (ValueRefinementError (StaticallyFalse _)) -> Right ()
  Left (ValueRefinementError (RefinementSortError (InvalidNatLiteral _))) -> Right ()
  other -> Left ("expected semantic definedness rejection; got " <> show other)
