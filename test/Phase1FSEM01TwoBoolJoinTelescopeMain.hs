{-# LANGUAGE OverloadedStrings #-}

-- Real Grammar-v1 source, exact lexical tuple order and production native cuts.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceTwoBoolJoinRun (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..), GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1JoinStateScopeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceTwoBoolJoinTelescope
  ( GrammarV1TwoBoolJoinError (..), GrammarV1TwoBoolJoinTrace (..)
  , grammarV1CheckedTwoBoolJoinTelescopeTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.two-bool-join.choose"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

assert :: Bool -> String -> Either String ()
assert condition message = if condition then Right () else Left message

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-two-bool-join" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("source is not one function: " ++ show other)
    _ -> Left "source must contain exactly one function"

check :: Text ->
  Maybe (Either GrammarV1TwoBoolJoinError GrammarV1TwoBoolJoinTrace)
check source = case parseOne source of
  Left _ -> Nothing
  Right fn ->
    grammarV1CheckedTwoBoolJoinTelescopeTrace emptyStaticContext root fn

checked :: Text -> Either String GrammarV1TwoBoolJoinTrace
checked source = do
  fn <- parseOne source
  case grammarV1CheckedTwoBoolJoinTelescopeTrace emptyStaticContext root fn of
    Just (Right evidence) -> Right evidence
    other -> Left ("no checked two-slot trace: " ++ show other)

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

names :: GrammarV1TwoBoolJoinTrace -> [Name]
names evidence = map name
  [ twoBoolJoinFlagBinder evidence, twoBoolJoinAlternativeBinder evidence
  , twoBoolJoinPayloadBinder evidence, twoBoolJoinFirstSlotBinder evidence
  , twoBoolJoinSecondSlotBinder evidence ]

initial :: GrammarV1TwoBoolJoinTrace -> Core.ResourceContext
initial evidence = case names evidence of
  [flag,alternate,payload,_,_] -> Core.ResourceContext
    { Core.unrestrictedBindings =
        Map.fromList [(flag,TyBool),(alternate,TyBool)]
    , Core.affineBindings = Map.empty
    , Core.linearBindings = Map.singleton payload bytes8
    , Core.sharedLoans = Set.empty }
  _ -> error "impossible: five source bindings"

firstBound :: GrammarV1TwoBoolJoinTrace -> Core.ResourceContext
firstBound evidence = case names evidence of
  [_,_,_,first,_] -> (initial evidence)
    { Core.unrestrictedBindings =
        Map.insert first TyBool (Core.unrestrictedBindings (initial evidence)) }
  _ -> error "impossible: five source bindings"

bothBound :: GrammarV1TwoBoolJoinTrace -> Core.ResourceContext
bothBound evidence = case names evidence of
  [_,_,_,_,second] -> (firstBound evidence)
    { Core.unrestrictedBindings =
        Map.insert second TyBool (Core.unrestrictedBindings (firstBound evidence)) }
  _ -> error "impossible: five source bindings"

checkIdentity :: GrammarV1TwoBoolJoinTrace -> Either String SourceTwoBoolJoinRun
checkIdentity evidence = do
  let ns = names evidence
      run = twoBoolJoinBranchRun evidence
      left = map name (twoBoolJoinThenBinders evidence)
      right = map name (twoBoolJoinElseBinders evidence)
  assert (length (Set.fromList ns) == 5)
    "duplicate source parameter or join-state identity"
  assert (length left == 2 && length right == 2 &&
          all (\x -> elem x (take 3 ns)) (left ++ right))
    "predecessor tuple lost an exact source binder or ordinal"
  assert (twoBoolJoinSlotCheckedModes evidence ==
          replicate 2 (CheckedTypeMode TyBool Unrestricted))
    "source slot types/modes were not independently checked"
  assert (sourceTwoBoolJoinBefore run == Just (initial evidence) &&
          sourceTwoBoolJoinOutcome run == twoBoolJoinCheckedOutcome evidence)
    "ordinary production path and tracer disagree"
  Right run

checkAccepted :: Text -> SourceBoolJoinInvariant -> [Int] -> [Int]
  -> Either String ()
checkAccepted source expectedProof leftOrder rightOrder = do
  evidence <- checked source
  run <- checkIdentity evidence
  let ns = names evidence
      first = ns !! 3
      second = ns !! 4
      types = Just [(Unrestricted,TyBool),(Unrestricted,TyBool)]
  assert (map name (twoBoolJoinThenBinders evidence) ==
            map (ns !!) leftOrder &&
          map name (twoBoolJoinElseBinders evidence) ==
            map (ns !!) rightOrder)
    "tuple position differs from checked source operand identity"
  assert (twoBoolJoinInvariantProof evidence == expectedProof)
    "invariant does not match exact lexical proof"
  assert (sourceTwoBoolJoinThen run == Just (initial evidence) &&
          sourceTwoBoolJoinElse run == Just (initial evidence) &&
          sourceTwoBoolJoinCoreJoined run == Just (initial evidence) &&
          sourceTwoBoolJoinFirstBound run == Just (firstBound evidence) &&
          sourceTwoBoolJoinBothBound run == Just (bothBound evidence) &&
          sourceTwoBoolJoinThenTypes run == types &&
          sourceTwoBoolJoinElseTypes run == types)
    "native join/pair typing/ordered binding checkpoints diverged"
  assert (Core.joinContinuing [initial evidence,initial evidence] ==
            Right (initial evidence) &&
          Core.insertBinding Unrestricted first TyBool (initial evidence) ==
            Right (firstBound evidence) &&
          Core.insertBinding Unrestricted second TyBool (firstBound evidence) ==
            Right (bothBound evidence))
    "independent native Core replay disagrees with production trace"
  assert (twoBoolJoinCheckedOutcome evidence ==
          Right (SurfaceCheckResult "choose" [Return bytes8]))
    "linear spectator was not returned exactly once"

checkUnproved :: Text -> Either String ()
checkUnproved source = do
  evidence <- checked source
  run <- checkIdentity evidence
  assert (twoBoolJoinInvariantProof evidence == SourceBoolInvariantUnproved &&
          sourceTwoBoolJoinThen run == Just (initial evidence) &&
          sourceTwoBoolJoinElse run == Just (initial evidence) &&
          sourceTwoBoolJoinCoreJoined run == Just (initial evidence) &&
          sourceTwoBoolJoinFirstBound run == Just (firstBound evidence) &&
          sourceTwoBoolJoinBothBound run == Just (bothBound evidence))
    "unproved invariant refused before complete typed state was reached"
  case twoBoolJoinCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == MissingEvidence &&
       surfaceErrorDetail err ==
        "join invariant has no checked proof for this bounded source telescope")
      ("incorrect MissingEvidence detail: " ++ show err)
    Right _ -> Left "unproved invariant was silently assumed"

checkBadOperand :: Text -> Bool -> Either String ()
checkBadOperand source failsLeft = do
  evidence <- checked source
  run <- checkIdentity evidence
  assert (sourceTwoBoolJoinCoreJoined run == Nothing &&
          sourceTwoBoolJoinFirstBound run == Nothing &&
          sourceTwoBoolJoinBothBound run == Nothing &&
          if failsLeft
            then sourceTwoBoolJoinThen run == Nothing &&
                 sourceTwoBoolJoinElse run == Nothing
            else sourceTwoBoolJoinThen run == Just (initial evidence) &&
                 sourceTwoBoolJoinElse run == Nothing)
    "bad tuple operand fabricated post-error successor"
  case twoBoolJoinCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == TypeMismatch &&
       surfaceErrorDetail err ==
        "two-slot join predecessor requires a pair of unrestricted Bool values")
      ("incorrect production TypeMismatch: " ++ show err)
    Right _ -> Left "Linear Bytes accepted as an unrestricted Bool"

checkShadow :: Text -> Either String ()
checkShadow source = case check source of
  Just (Left (TwoBoolJoinScopeError (GrammarV1JoinStateBinderError
    (GrammarV1DuplicateBinder _ _)))) -> Right ()
  other -> Left ("duplicate binder not rejected lexically: " ++ show other)

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source description = do
  _ <- parseOne source
  assert (check source == Nothing)
    ("out-of-competence source was unexpectedly admitted: " ++ description)

main :: IO ()
main = do
  let get filename = TextIO.readFile
        ("test/fixtures/fsem01-two-bool-join-telescope-v1/" ++ filename ++ ".phil")
  accepted <- get "accepted-reflexive"
  tru <- get "accepted-true"
  second <- get "accepted-second-reflexive"
  same <- get "accepted-same-tuple"
  repeatOperand <- get "accepted-repeated-operand"
  falseCase <- get "unproved-false"
  cross <- get "unproved-cross-slot"
  wrongThenFirst <- get "wrong-then-first"
  wrongThenSecond <- get "wrong-then-second"
  wrongElseFirst <- get "wrong-else-first"
  wrongElseSecond <- get "wrong-else-second"
  shadowFirst <- get "shadow-first"
  shadowSecond <- get "shadow-second"
  unsupported <- mapM get
    [ "branch-reads-future-slot", "wrong-second-slot-type"
    , "three-slot-telescope", "one-slot-telescope", "missing-invariant"
    , "missing-else", "wrong-post-join-use", "wrong-condition"
    , "one-member-predecessor", "wrong-return-width" ]
  let result = do
        checkAccepted accepted SourceBoolInvariantProvenReflexive [0,1] [1,0]
        checkAccepted tru SourceBoolInvariantProvenTrue [0,1] [1,0]
        checkAccepted second SourceBoolInvariantProvenReflexive [0,1] [1,0]
        checkAccepted same SourceBoolInvariantProvenReflexive [0,1] [0,1]
        checkAccepted repeatOperand SourceBoolInvariantProvenReflexive [0,0] [1,1]
        checkUnproved falseCase
        checkUnproved cross
        checkBadOperand wrongThenFirst True
        checkBadOperand wrongThenSecond True
        checkBadOperand wrongElseFirst False
        checkBadOperand wrongElseSecond False
        checkShadow shadowFirst
        checkShadow shadowSecond
        mapM_ (uncurry checkUnsupported) (zip unsupported
          [ "early slot", "linear slot", "three slots", "one slot"
          , "no invariant", "no else", "wrong successor slot", "wrong condition"
          , "one-value predecessor", "wrong return width" ])
        assert (Text.replace "(flag, alternative);" "(flag, payload);"
          accepted == wrongThenSecond)
          "wrong-then-second differs by more than one source expression"
  case result of
    Right () -> putStrLn
      "PASS: 23 exact source two-slot fixtures; native Map/Set pair join, two fresh binders and error prefixes"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
