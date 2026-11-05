{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Refinement (RefinementError (..))
import Phil.Core.Syntax
  ( Branch (..), FrameId (..), GrammarId (..), Mode (..), Name (..)
  , Outcome (..), PendingRecvSpec (..), ProductElementType (..)
  , Proposition (..), RefTerm (..), Session (..), Ty (..), Value (..)
  )
import Phil.Core.Value
  ( ValueError (..), ValueResult (..), checkValue, synthValue )
import System.Exit (exitFailure)

type Check = Either String ()

endpoint, keeper :: Name
endpoint = Name "ep"
keeper = Name "keeper"

end :: Session
end = End (Outcome "ok")

-- Well-sorted Nat subtraction whose definedness prerequisite (5 <= 3)
-- is false. Equality and zero scaling can normalize away its syntax.
partial :: RefTerm
partial = RefSub (RefNat 3) (RefNat 5)

badBytes, goodBytes, badProof, goodProof :: Ty
badBytes = TyBytes (RefScale 0 partial)
goodBytes = TyBytes (RefNat 0)
badProof = TyProof (Equal partial partial)
goodProof = TyProof Truth

recv, send :: Ty -> Ty
recv payload = TyEndpoint (Receive (Name "payload") payload end)
send payload = TyEndpoint (Send (Name "payload") payload end)

branch :: Ty -> Branch
branch payload = Branch "payload" (Just (Name "value", payload)) end

later :: Ty -> Ty
later payload = TyEndpoint (Receive (Name "first") TyBool
  (Send (Name "second") payload end))

pending :: Ty -> Ty
pending payload = TyPendingRecv PendingRecvSpec
  { pendingSourceEndpoint = endpoint
  , pendingGrammar = GrammarId "audit.grammar"
  , pendingFrame = FrameId "audit.frame"
  , pendingBinder = Name "frame"
  , pendingContinuation = Send (Name "payload") payload end
  }

seed :: Ty -> Either String CheckState
seed ty = do
  keeperContext <- mapLeft show $
    insertBinding Unrestricted keeper TyBool (resourceContext emptyCheckState)
  context <- mapLeft show $ insertBinding Linear endpoint ty keeperContext
  Right emptyCheckState { resourceContext = context }

expectDefinednessReject :: Ty -> Ty -> Check
expectDefinednessReject source target = do
  state <- seed source
  case checkValue (VVar endpoint) target state of
    Left (ValueRefinementError (StaticallyFalse _)) -> Right ()
    other -> Left ("expected false subtraction prerequisite, got " ++ show other)

expectAscriptionReject :: Ty -> Ty -> Check
expectAscriptionReject source target = do
  state <- seed source
  case synthValue (VAscribe (VVar endpoint) target) state of
    Left (ValueRefinementError (StaticallyFalse _)) -> Right ()
    other -> Left ("expected ascription definedness rejection, got " ++ show other)

expectSourceReject :: Ty -> Ty -> Check
expectSourceReject source target = expectDefinednessReject source target

accept :: Ty -> Check
accept ty = do
  state <- seed ty
  result <- mapLeft show $ checkValue (VVar endpoint) ty state
  let after = valueResultState result
      beforeContext = resourceContext state
      afterContext = resourceContext after
  ensure (valueResultType result == ty) "changed endpoint annotation"
  ensure (valueResultMode result == Just Linear) "changed ownership mode"
  ensure (valueResultTerm result == Just (RefVar endpoint)) "changed subject"
  ensure (Map.notMember endpoint (linearBindings afterContext))
    "linear endpoint was not consumed"
  ensure (Map.lookup keeper (unrestrictedBindings afterContext)
          == Map.lookup keeper (unrestrictedBindings beforeContext))
    "unrelated unrestricted binding was altered"
  ensure (Map.null (residualObligations after))
    "type formation left a residual obligation"

dependent :: Ty
dependent = TyEndpoint (Receive (Name "n") (TyUInt 8)
  (Send (Name "payload")
    (TyBytes (RefToNat (RefVar (Name "n"))))
    end))

recursive :: Ty
recursive = TyEndpoint (Rec (Name "loop")
  (Receive (Name "flag") TyBool (SessionVar (Name "loop"))))

uninhabited :: Ty
uninhabited = recv (TyRefined (Name "v") TyBool Falsehood)

cases :: [(String, Check)]
cases =
  [ ("D01 receive payload hides invalid subtraction",
      expectDefinednessReject (recv goodBytes) (recv badBytes))
  , ("D02 send Proof payload hides invalid subtraction",
      expectAscriptionReject (send goodProof) (send badProof))
  , ("D03 offer branch payload hides invalid subtraction",
      expectDefinednessReject
        (TyEndpoint (Offer [branch goodBytes]))
        (TyEndpoint (Offer [branch badBytes])))
  , ("D04 select branch payload hides invalid subtraction",
      expectDefinednessReject
        (TyEndpoint (Select [branch goodBytes]))
        (TyEndpoint (Select [branch badBytes])))
  , ("D05 later continuation hides invalid subtraction",
      expectDefinednessReject (later goodBytes) (later badBytes))
  , ("D06 nested product refinement predicate is checked",
      expectDefinednessReject
        (recv (TyProduct
          [ProductElementType Unrestricted (TyRefined (Name "v") TyBool Truth)]))
        (recv (TyProduct
          [ProductElementType Unrestricted
            (TyRefined (Name "v") TyBool (Equal partial partial))])))
  , ("D07 pending receive continuation is checked",
      expectDefinednessReject (pending goodBytes) (pending badBytes))
  , ("D08 stored endpoint binding is checked before consumption",
      expectSourceReject (recv badBytes) (recv goodBytes))
  , ("C01 ordinary dependent continuation stays valid", accept dependent)
  , ("C02 finite recursive session stays valid", accept recursive)
  , ("C03 uninhabited refinement is not forced true", accept uninhabited)
  , ("C04 ordinary send payload stays valid", accept (send goodBytes))
  , ("C05 ordinary branch payload stays valid",
      accept (TyEndpoint (Offer [branch goodBytes])))
  ]

ensure :: Bool -> String -> Check
ensure True _ = Right ()
ensure False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

main :: IO ()
main = do
  results <- mapM run cases
  unless (and results) exitFailure
  where
    run (name, result) = case result of
      Right () -> putStrLn ("PASS: D01-D03 " ++ name) >> pure True
      Left detail -> putStrLn ("FAIL: D01-D03 " ++ name ++ " -- " ++ detail)
        >> pure False
