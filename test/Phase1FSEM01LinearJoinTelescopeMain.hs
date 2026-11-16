{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 J-5: one real source Linear Bytes[N] join slot, exact production
-- consume/join/rebind and no invented successor after source failures.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax
  ( Control (Return), Mode (..), Name (..), RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceLinearJoinRun (..) )
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
import Phil.Surface.GrammarV1.SourceLinearJoinTelescope
  ( GrammarV1LinearJoinError (..), GrammarV1LinearJoinTrace (..)
  , grammarV1CheckedLinearJoinTelescopeTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.j5.choose"

bytes8, bytes9 :: Ty
bytes8 = TyBytes (RefNat 8)
bytes9 = TyBytes (RefNat 9)

directory :: FilePath
directory = "test/fixtures/fsem01-linear-join-telescope-v1/"

assert :: Bool -> String -> Either String ()
assert passed why = if passed then Right () else Left why

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne input = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-j5" input)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("J5 source not one function: " ++ show other)
    other -> Left ("J5 expected exactly one declaration, got " ++ show (length other))

check :: Text
  -> Maybe (Either GrammarV1LinearJoinError GrammarV1LinearJoinTrace)
check input = case parseOne input of
  Left _ -> Nothing
  Right fn ->
    grammarV1CheckedLinearJoinTelescopeTrace emptyStaticContext root fn

checked :: Text -> Either String GrammarV1LinearJoinTrace
checked input = do
  fn <- parseOne input
  case grammarV1CheckedLinearJoinTelescopeTrace emptyStaticContext root fn of
    Just (Right evidence) -> Right evidence
    other -> Left ("not actual J5 parsed-source Linear join: " ++ show other)

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

flagName, payloadName, slotName :: GrammarV1LinearJoinTrace -> Name
flagName = name . linearJoinFlagBinder
payloadName = name . linearJoinPayloadBinder
slotName = name . linearJoinSlotBinder

initial :: GrammarV1LinearJoinTrace -> Core.ResourceContext
initial evidence = Core.ResourceContext
  { Core.unrestrictedBindings = Map.singleton (flagName evidence) TyBool
  , Core.affineBindings = Map.empty
  , Core.linearBindings = Map.singleton (payloadName evidence) bytes8
  , Core.sharedLoans = Set.empty
  }

spent :: GrammarV1LinearJoinTrace -> Core.ResourceContext
spent evidence = (initial evidence)
  { Core.linearBindings = Map.empty }

bound :: GrammarV1LinearJoinTrace -> Core.ResourceContext
bound evidence = (spent evidence)
  { Core.linearBindings = Map.singleton (slotName evidence) bytes8 }

checkIdentity :: GrammarV1LinearJoinTrace -> Either String SourceLinearJoinRun
checkIdentity evidence = do
  let names = [flagName evidence,payloadName evidence,slotName evidence]
      run = linearJoinNativeRun evidence
  assert (Set.size (Set.fromList names) == 3)
    "source binder names or join slot identity collided"
  assert (grammarV1ResolvedBinderDisplayName (linearJoinSlotBinder evidence)
            == "selected")
    "source join slot binder spelling/identity changed"
  assert (sourceLinearJoinBefore run == Just (initial evidence) &&
          sourceLinearJoinOutcome run == linearJoinCheckedOutcome evidence)
    "ordinary production checker and traced state disagree"
  Right run

checkAccepted :: Text -> SourceBoolJoinInvariant -> Either String ()
checkAccepted source expectedInvariant = do
  evidence <- checked source
  run <- checkIdentity evidence
  let first = initial evidence
      consumed = spent evidence
      inserted = bound evidence
      old = payloadName evidence
      slot = slotName evidence
  assert (linearJoinThenBinder evidence == linearJoinPayloadBinder evidence &&
          linearJoinElseBinder evidence == linearJoinPayloadBinder evidence &&
          linearJoinReturnBinder evidence == linearJoinSlotBinder evidence &&
          linearJoinSlotCheckedMode evidence ==
            CheckedTypeMode bytes8 Linear &&
          linearJoinInvariantProof evidence == expectedInvariant)
    "the source-checked Linear join actuals, type or invariant changed"
  assert (sourceLinearJoinThen run == Just consumed &&
          sourceLinearJoinElse run == Just consumed &&
          sourceLinearJoinCoreJoined run == Just consumed &&
          sourceLinearJoinBound run == Just inserted &&
          sourceLinearJoinThenType run == Just (Linear,bytes8) &&
          sourceLinearJoinElseType run == Just (Linear,bytes8))
    "native source consume, both predecessor cuts, join or bound owner differs"
  assert (Core.consumeLinear old first == Right (bytes8,consumed) &&
          Core.joinContinuing [consumed,consumed] == Right consumed &&
          Core.insertBinding Linear slot bytes8 consumed == Right inserted &&
          Core.consumeLinear slot inserted == Right (bytes8,consumed))
    "independent Core consume/join/fresh binding/return replay disagreed"
  assert (Map.notMember old (Core.linearBindings inserted) &&
          Map.lookup slot (Core.linearBindings inserted) == Just bytes8 &&
          Map.size (Core.linearBindings inserted) == 1 &&
          Core.sharedLoans inserted == Set.empty &&
          Core.unrestrictedBindings inserted ==
            Core.unrestrictedBindings first &&
          Core.affineBindings inserted == Core.affineBindings first)
    "old owner resurrected, new owner duplicated or spectator/loan changed"
  assert (Core.insertBinding Linear slot bytes8 inserted ==
            Left (Core.DuplicateBinding slot) &&
          Core.consumeLinear old inserted == Left (Core.UnknownBinding old))
    "native Core accepted duplicate join slot or stale old owner use"
  assert (linearJoinCheckedOutcome evidence ==
            Right (SurfaceCheckResult "choose" [Return bytes8]))
    "checked final source did not return the new Linear slot exactly once"

checkUnproved :: Text -> Either String ()
checkUnproved source = do
  evidence <- checked source
  run <- checkIdentity evidence
  assert (linearJoinInvariantProof evidence == SourceBoolInvariantUnproved &&
          sourceLinearJoinThen run == Just (spent evidence) &&
          sourceLinearJoinElse run == Just (spent evidence) &&
          sourceLinearJoinCoreJoined run == Just (spent evidence) &&
          sourceLinearJoinBound run == Just (bound evidence))
    "unproved invariant incorrectly bypassed native move/rebind checkpoints"
  case linearJoinCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == MissingEvidence &&
       surfaceErrorDetail err ==
         "join invariant has no checked proof for this bounded source telescope")
      ("wrong MissingEvidence source error: " ++ show err)
    Right _ -> Left "unproved Linear join invariant was silently assumed"

checkWrongOperand :: Text -> Bool -> Bool -> Either String ()
checkWrongOperand source failsThen wrongWidth = do
  evidence <- checked source
  run <- checkIdentity evidence
  assert (sourceLinearJoinCoreJoined run == Nothing &&
          sourceLinearJoinBound run == Nothing &&
          sourceLinearJoinElse run == Nothing &&
          (if failsThen
            then sourceLinearJoinThen run == Nothing
            else sourceLinearJoinThen run == Just (spent evidence)) &&
          (if wrongWidth
            then linearJoinSlotCheckedMode evidence == CheckedTypeMode bytes9 Linear
            else linearJoinSlotCheckedMode evidence == CheckedTypeMode bytes8 Linear))
    "bad predecessor introduced post-error Core join or Linear slot"
  case linearJoinCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == TypeMismatch &&
       surfaceErrorDetail err ==
         "linear join predecessor must move the exact checked Linear Bytes actual")
      ("wrong exact predecessor rejection class/detail: " ++ show err)
    Right _ -> Left "wrong source type/width accepted as one Linear join actual"

checkStaleReturn :: Text -> Either String ()
checkStaleReturn source = do
  evidence <- checked source
  run <- checkIdentity evidence
  let old = payloadName evidence
  assert (linearJoinReturnBinder evidence == linearJoinPayloadBinder evidence &&
          sourceLinearJoinThen run == Just (spent evidence) &&
          sourceLinearJoinElse run == Just (spent evidence) &&
          sourceLinearJoinCoreJoined run == Just (spent evidence) &&
          sourceLinearJoinBound run == Just (bound evidence))
    "source stale-owner read incorrectly escaped the real successful join"
  case linearJoinCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == StructuralUse &&
       surfaceErrorDetail err == "unknown or consumed binding: " <> unName old)
      ("wrong stale-owner rejection: " ++ show err)
    Right _ -> Left "old source owner could be reused after Linear phi"

checkBorrowed :: Text -> Either String ()
checkBorrowed source = do
  evidence <- checked source
  _ <- checkIdentity evidence
  let old = payloadName evidence
      start = initial evidence
      borrowed = start { Core.sharedLoans = Set.singleton old }
      done = spent evidence
  assert (Core.startSharedLoan old start == Right borrowed &&
          Core.consumeLinear old borrowed == Left (Core.OwnerBorrowed old) &&
          Core.joinContinuing [borrowed,done] ==
            Left (Core.EscapingLoans (Set.singleton old)) &&
          Core.joinContinuing [start,done] ==
            Left (Core.LinearBranchMismatch
              (Core.linearBindings start) (Core.linearBindings done)))
    "borrowed/unequal predecessor was admitted or wrong failure precedence"

checkShadow :: Text -> Either String ()
checkShadow source = case check source of
  Just (Left (LinearJoinScopeError
    (GrammarV1JoinStateBinderError
      (GrammarV1DuplicateBinder _ _)))) -> Right ()
  other -> Left ("source join active shadow not rejected lexically: " ++ show other)

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source why = do
  _ <- parseOne source
  assert (check source == Nothing)
    ("out-of-fragment source was mistakenly admitted: " ++ why)

main :: IO ()
main = do
  let get key = TextIO.readFile (directory ++ key ++ ".phil")
  accepted <- get "accepted-true"
  reflexive <- get "accepted-reflexive"
  unproved <- get "unproved-false"
  wrongThen <- get "wrong-then-bool"
  wrongElse <- get "wrong-else-bool"
  wrongWidth <- get "wrong-slot-width"
  stale <- get "stale-return"
  shadow <- get "shadow-parameter"
  unsupported <- mapM get
    [ "branch-reads-future-slot","missing-invariant","missing-else"
    , "two-slot-telescope","wrong-return-width","wrong-condition" ]
  let result = do
        checkAccepted accepted SourceBoolInvariantProvenTrue
        checkAccepted reflexive SourceBoolInvariantProvenReflexive
        checkUnproved unproved
        checkWrongOperand wrongThen True False
        checkWrongOperand wrongElse False False
        checkWrongOperand wrongWidth True True
        checkStaleReturn stale
        checkBorrowed accepted
        checkShadow shadow
        mapM_ (uncurry checkUnsupported)
          (zip unsupported
            [ "future source join slot used in predecessor"
            , "unproved absent explicit invariant"
            , "missing else predecessor"
            , "two or more state slots"
            , "incorrect declared result width"
            , "source condition not checked Bool flag" ])
        assert (Text.replace "    payload;\n  } else"
                  "    flag;\n  } else" accepted == wrongThen)
          "wrong-then source is not a one-expression mutation"
        assert (Text.replace "  } else {\n    payload;"
                  "  } else {\n    flag;" accepted == wrongElse)
          "wrong-else source is not a one-expression mutation"
  case result of
    Right () -> putStrLn
      "PASS J-5: 14 genuine Grammar-v1 Linear join source fixtures, exact native consume/join/fresh owner/return and precise error refusal"
    Left err -> putStrLn ("FAIL J-5: " ++ err) >> exitFailure
