{-# LANGUAGE OverloadedStrings #-}

-- Bounded CORR-6: exact source-derived before/raw/pruned/join states.
-- Independent list-based join checks real Phil.Core.Context.joinContinuing.
module Main (main) where

import Control.Monad (forM_)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as ByteString
import qualified Data.Text.Encoding as Encoding
import Numeric (showHex)
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.FilePath ((</>))
import Data.List (find)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import qualified Phil.Core.Context as Core
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.NominalDataMode (NominalRestrictionJustification (..))
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..),emptyStaticContext)
import Phil.Core.Syntax (Mode (Affine, Linear), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine (SourceScopedIfJoinRun (..))
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..) )
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.CheckedType (GrammarV1CheckedTypeModeOrigin (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl, GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceAffineIfJoinResource
  ( GrammarV1AffineIfJoinTrace (..), grammarV1CheckedAffineIfJoinTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

data Snapshot = Snapshot
  { snapU :: [(Name,Ty)]
  , snapA :: [(Name,Ty)]
  , snapL :: [(Name,Ty)]
  , snapLoans :: [Name]
  } deriving (Eq,Show)

snapshot :: Core.ResourceContext -> Snapshot
snapshot c = Snapshot
  (Map.toAscList (Core.unrestrictedBindings c))
  (Map.toAscList (Core.affineBindings c))
  (Map.toAscList (Core.linearBindings c))
  (Set.toAscList (Core.sharedLoans c))

check :: Bool -> String -> Either String ()
check yes why = if yes then Right () else Left why

sorted :: Ord a => [a] -> Bool
sorted xs = and (zipWith (<) xs (drop 1 xs))

validate :: Snapshot -> Either String ()
validate s = do
  let zones = [snapU s,snapA s,snapL s]
      names = concatMap (map fst) zones
      restricted = map fst (snapA s ++ snapL s)
  check (all (sorted . map fst) zones &&
         sorted (snapLoans s) &&
         length names == Set.size (Set.fromList names) &&
         all (\x -> elem x restricted) (snapLoans s))
    "forged or noncanonical four-zone resource state"

-- Actual finite decision computed independently from sorted association lists.
-- No Map.intersection or production join is used in this function.
finiteJoin :: Snapshot -> Snapshot -> Either Core.CheckError Snapshot
finiteJoin first second
  | not (null (snapLoans first)) =
      Left (Core.EscapingLoans (Set.fromList (snapLoans first)))
  | not (null (snapLoans second)) =
      Left (Core.EscapingLoans (Set.fromList (snapLoans second)))
  | snapU first /= snapU second =
      Left (Core.UnrestrictedBranchMismatch
        (Map.fromList (snapU first)) (Map.fromList (snapU second)))
  | snapL first /= snapL second =
      Left (Core.LinearBranchMismatch
        (Map.fromList (snapL first)) (Map.fromList (snapL second)))
  | otherwise = case find mismatch (snapA first) of
      Just (name,ty) -> case lookup name (snapA second) of
        Just other -> Left (Core.AffineBranchTypeMismatch name ty other)
        Nothing -> Left (Core.UnknownBinding name) -- unreachable if mismatch
      Nothing -> Right (Snapshot (snapU first)
        [ (name,ty) | (name,ty) <- snapA first
        , lookup name (snapA second) == Just ty ]
        (snapL first) [])
  where
    mismatch (name,ty) = case lookup name (snapA second) of
      Just other -> ty /= other
      Nothing -> False

-- Compare BOTH finite and actual name domains in all four structural zones.
fullRelation :: Snapshot -> Core.ResourceContext -> Bool
fullRelation finite native =
  let actual = snapshot native
      keys = Set.toList (Set.fromList (
        concatMap (map fst)
          [snapU finite,snapA finite,snapL finite,
           snapU actual,snapA actual,snapL actual] ++
        snapLoans finite ++ snapLoans actual ++
        [Name "corr6-absent-1",Name "corr6-absent-2"]))
  in all (\name ->
     lookup name (snapU finite) ==
       Map.lookup name (Core.unrestrictedBindings native) &&
     lookup name (snapA finite) ==
       Map.lookup name (Core.affineBindings native) &&
     lookup name (snapL finite) ==
       Map.lookup name (Core.linearBindings native) &&
     elem name (snapLoans finite) ==
       Set.member name (Core.sharedLoans native)) keys

compareJoin :: String -> Core.ResourceContext -> Core.ResourceContext
  -> Either String (Either Core.CheckError Core.ResourceContext)
compareJoin label left right = do
  let a = snapshot left; b = snapshot right
      native = Core.joinContinuing [left,right]
  validate a
  validate b
  case (finiteJoin a b,native) of
    (Left expected,Left observed) -> do
      check (expected == observed) (label ++ ": exact error diverged: " ++
                                   show (expected,observed))
      Right (Left observed)
    (Right finite,Right observed) -> do
      validate finite
      check (snapshot observed == finite && fullRelation finite observed)
        (label ++ ": fabricated/dropped U/A/L/loan successor")
      Right (Right observed)
    other -> Left (label ++ ": native/finite join outcome mismatch: " ++
                   show other)

dataRoot,fnRoot :: DeclarationKey
dataRoot = DeclarationKey "decl.fsem01.join.Permit"
fnRoot = DeclarationKey "decl.fsem01.join.choose"
revision :: InterfaceRevision
revision = InterfaceRevision "iface.fsem01.join.v1"
lifecycle :: Maybe NominalRestrictionJustification
lifecycle = Just (AdmittedLifecycleObligation
  "external independently reviewed permission to abandon Permit")
permitTy,bytes8 :: Ty
permitTy = TyOpaque "Permit"
bytes8 = TyBytes (RefNat 8)
directory :: FilePath
directory = "test/fixtures/fsem01-affine-join-scope-v1/"

parsePair :: Text -> Either String (GrammarV1DataDecl,GrammarV1FunctionDecl)
parsePair source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-corr6" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ dat,Located _ fn] ->
      case (locatedValue (grammarV1Declaration dat),
            locatedValue (grammarV1Declaration fn)) of
        (GrammarV1DataDeclaration a,GrammarV1FunctionDeclaration b) -> Right (a,b)
        other -> Left ("wrong parsed data/function declarations " ++ show other)
    other -> Left ("expected two declarations, got " ++ show (length other))

sourceTrace :: Text -> Either String GrammarV1AffineIfJoinTrace
sourceTrace source = do
  (dat,fn) <- parsePair source
  case grammarV1CheckedAffineIfJoinTrace
      emptyStaticContext dataRoot revision lifecycle dat fnRoot fn of
    Just (Right trace) -> Right trace
    other -> Left ("actual source adapter did not admit: " ++ show other)

binder :: GrammarV1ResolvedBinder -> Name
binder = grammarV1ResolvedBinderCoreName

initial :: GrammarV1AffineIfJoinTrace -> Core.ResourceContext
initial t = Core.ResourceContext
  (Map.singleton (binder (affineIfJoinFlagBinder t)) TyBool)
  (Map.singleton (binder (affineIfJoinPermitBinder t)) permitTy)
  (Map.singleton (binder (affineIfJoinPayloadBinder t)) bytes8)
  Set.empty

data Profile = Asymmetric | Retained | BothLocals | UnrestrictedLocal
  | LinearLeak | StaleAfter deriving (Eq,Show)

fixture :: Profile -> String
fixture Asymmetric = "accepted-asymmetric"
fixture Retained = "retained-affine"
fixture BothLocals = "both-local-affine"
fixture UnrestrictedLocal = "unrestricted-local"
fixture LinearLeak = "unreleased-linear-local"
fixture StaleAfter = "stale-after-join"

checkSource :: Profile -> GrammarV1AffineIfJoinTrace -> Either String ()
checkSource kind trace = do
  let run = affineIfJoinRun trace
      before = initial trace
      permit = binder (affineIfJoinPermitBinder trace)
      payload = binder (affineIfJoinPayloadBinder trace)
      locals = map binder (affineIfJoinLocalBinders trace)
      thenCuts = scopedIfJoinThenPruned run
      elseCuts = scopedIfJoinElsePruned run
  check (scopedIfJoinBefore run == Just before &&
         scopedIfJoinOutcome run == affineIfJoinOutcome trace &&
         affineIfJoinDataKey trace == dataRoot &&
         affineIfJoinInterfaceRevision trace == revision &&
         affineIfJoinPermitMode trace == CheckedTypeMode permitTy Affine &&
         affineIfJoinPayloadMode trace == CheckedTypeMode bytes8 Linear &&
         affineIfJoinPermitOrigin trace ==
           GrammarV1NamedTypeModeOrigin
             (ReferencedGenericStaticActual "Permit") dataRoot revision)
    "source type, identity, mode admission or production trace differs"
  case kind of
    LinearLeak -> do
      check (null thenCuts && null elseCuts &&
             scopedIfJoinJoined run == Nothing &&
             length locals == 1)
        "source LinearCompletion invented successor"
      case affineIfJoinOutcome trace of
        Left e -> check (surfaceErrorClass e == LinearCompletion)
          "source local Linear debt had wrong error"
        Right _ -> Left "source did not reject live branch-local Linear owner"
    _ -> do
      left <- case thenCuts of
        [one] -> Right one
        _ -> Left "missing exact left pruned source predecessor"
      right <- case elseCuts of
        [one] -> Right one
        _ -> Left "missing exact right pruned source predecessor"
      result <- compareJoin ("source " ++ show kind) left right
      joined <- case result of
        Left e -> Left ("real source join rejected unexpectedly: " ++ show e)
        Right ctx -> Right ctx
      check (scopedIfJoinJoined run == Just joined &&
             Core.linearBindings joined == Map.singleton payload bytes8)
        "real source joined trace or linear spectator not preserved"
      case kind of
        Asymmetric -> check
          (Map.null (Core.affineBindings joined) &&
           not (Map.member permit (Core.affineBindings left)) &&
           Map.member permit (Core.affineBindings right) &&
           length locals == 1)
          "affine consumed only on left was resurrected"
        Retained -> check
          (Map.lookup permit (Core.affineBindings joined) == Just permitTy &&
           null locals)
          "affine owner common to both continuing branches was lost"
        BothLocals -> check
          (Map.null (Core.affineBindings joined) &&
           length locals == 2 && head locals /= last locals)
          "same-spelling sibling locals were conflated"
        UnrestrictedLocal -> check
          (Core.unrestrictedBindings joined ==
             Core.unrestrictedBindings before && length locals == 1)
          "unrestricted scoped local escaped pruning"
        StaleAfter -> case affineIfJoinOutcome trace of
          Left e -> check
            (Map.null (Core.affineBindings joined) &&
             surfaceErrorClass e == StructuralUse &&
             surfaceErrorDetail e ==
               "unknown or consumed binding: " <> unName permit)
            "stale affine use did not fail after real join"
          Right _ -> Left "stale affine use incorrectly passed"

reject :: String -> Either String a -> Either String ()
reject label value =
  check (case value of Left _ -> True; Right _ -> False)
    ("forged source/join witness admitted: " ++ label)

adversarial :: GrammarV1AffineIfJoinTrace -> Either String ()
adversarial t = do
  let base = initial t
      flag = binder (affineIfJoinFlagBinder t)
      payload = binder (affineIfJoinPayloadBinder t)
      permit = binder (affineIfJoinPermitBinder t)
      alien = Name "corr6-foreign"
      uWrong = base { Core.unrestrictedBindings =
                       Map.singleton flag (TyOpaque "Other") }
      lWrong = base { Core.linearBindings =
                       Map.singleton payload TyBool }
      aWrong = base { Core.affineBindings =
                       Map.singleton permit TyBool }
      borrowed = base { Core.sharedLoans = Set.singleton payload }
      missing = base { Core.affineBindings = Map.empty }
  forM_
    [("escaping loan",base,borrowed,
        Core.EscapingLoans (Set.singleton payload))
    ,("U conflict",base,uWrong,
        Core.UnrestrictedBranchMismatch
          (Core.unrestrictedBindings base) (Core.unrestrictedBindings uWrong))
    ,("L conflict",base,lWrong,
        Core.LinearBranchMismatch
          (Core.linearBindings base) (Core.linearBindings lWrong))
    ,("Affine type conflict",base,aWrong,
        Core.AffineBranchTypeMismatch permit permitTy TyBool)] $
      \(label,left,right,expected) -> do
        got <- compareJoin label left right
        check (got == Left expected) (label ++ ": exact failure incorrect")
  got <- compareJoin "Affine first-branch drop" missing aWrong
  check (got == Right missing)
    "second predecessor resurrected first-dropped affine owner"
  check (finiteJoin (snapshot borrowed) (snapshot uWrong) ==
           Left (Core.EscapingLoans (Set.singleton payload)))
    "earliest loan failure did not precede unrelated U mismatch"
  let src = snapshot base
      malformed = src { snapLoans = [alien] }
  reject "orphaned loan" (validate malformed)
  reject "duplicate binding" (validate
    (src { snapL = snapL src ++ snapL src }))
  reject "forged affine survivor" $ check
    (fullRelation (src { snapA = (alien,permitTy) : snapA src }) base)
    "forged extra affine changes joined outcome"
  reject "cross-zone duplicate" (validate
    (src { snapA = (payload,permitTy) : snapA src }))
  check (Core.joinContinuing [base,missing] == Right missing &&
         Core.joinContinuing [missing,base] == Right missing)
    "affine branch-order intersection not extensional on valid inputs"

-- Bound, nonnormative actual-source witness. All four-zone shape bits
-- come from authentic *post-prune* contexts; the native test above proves
-- they correspond to the exact actual source/checker run. No type oracle
-- is obtained from arbitrary user-provided wire bytes.
hashBytes :: ByteString.ByteString -> Text
hashBytes = Text.pack . concatMap encodeByte . ByteString.unpack
  where
    encodeByte n = let h = showHex n ""
                   in if length h == 1 then '0' : h else h

utf8Hex :: Text -> Text
utf8Hex = hashBytes . Encoding.encodeUtf8

framed :: Text -> Text
framed value = Text.pack (show (Text.length value)) <> ":" <> value

sourceWire :: Profile -> Text -> GrammarV1AffineIfJoinTrace
  -> Either String (String,Text)
sourceWire profile source trace = do
  let run = affineIfJoinRun trace
      flag = binder (affineIfJoinFlagBinder trace)
      permit = binder (affineIfJoinPermitBinder trace)
      payload = binder (affineIfJoinPayloadBinder trace)
      classify ctx = do
        check (Core.unrestrictedBindings ctx == Map.singleton flag TyBool &&
               Core.linearBindings ctx == Map.singleton payload bytes8 &&
               Set.null (Core.sharedLoans ctx) &&
               (Map.null (Core.affineBindings ctx) ||
                Core.affineBindings ctx == Map.singleton permit permitTy))
          "source-derived post-prune snapshot not in finite bridge domain"
        pure $ if Map.null (Core.affineBindings ctx)
          then "U1A0L1N0" else "U1A1L1N0"
      exact label contexts = case contexts of
        [ctx] -> classify ctx
        _ -> Left ("not one reached pruned predecessor: " ++ label)
  left <- case profile of
    LinearLeak -> check (null (scopedIfJoinThenPruned run)) "forged left" >>
                  pure "UNREACHED"
    _ -> exact "left" (scopedIfJoinThenPruned run)
  right <- case profile of
    LinearLeak -> check (null (scopedIfJoinElsePruned run)) "forged right" >>
                  pure "UNREACHED"
    _ -> exact "right" (scopedIfJoinElsePruned run)
  let disposition = case profile of
        Asymmetric -> "JOIN_EMPTY"
        Retained -> "JOIN_PERMIT"
        BothLocals -> "JOIN_EMPTY"
        UnrestrictedLocal -> "JOIN_PERMIT"
        LinearLeak -> "PREJOIN_LINEAR"
        StaleAfter -> "POSTJOIN_STALE"
      fields =
        [ hashBytes (SHA256.hash (Encoding.encodeUtf8 source))
        , utf8Hex "decl.fsem01.join.choose"
        , utf8Hex (unName flag)
        , utf8Hex (unName permit)
        , utf8Hex (unName payload)
        , left
        , right
        , disposition
        ]
      body = Text.concat (map framed fields)
      wire = "PHIL-FSEM01-CORR6-V1|" <> body
  check (length fields == 8 &&
         Text.all (\x -> x >= ' ' && x <= '~') wire)
    "noncanonical ASCII source witness"
  pure (fixture profile,wire)

main :: IO ()
main = do
  let cases = [Asymmetric,Retained,BothLocals,UnrestrictedLocal,
               LinearLeak,StaleAfter]
  args <- getArgs
  let destination = case args of
        [] -> Just Nothing
        ["--emit",dir] -> Just (Just dir)
        _ -> Nothing
  case destination of
    Nothing -> putStrLn
      "usage: Phase1FSEM01Corr6MixedJoinMain [--emit DIR]" >> exitFailure
    Just output -> do
      sources <- mapM (\k -> do
        input <- TextIO.readFile (directory ++ fixture k ++ ".phil")
        pure (k,input)) cases
      let result = do
            checked <- mapM (\(k,input) -> do
              t <- sourceTrace input
              checkSource k t
              pure (k,input,t)) sources
            case find (\(k,_,_) -> k == Retained) checked of
              Just (_,_,retained) -> adversarial retained
              Nothing -> Left "retained affine source missing"
            mapM (\(k,input,t) -> sourceWire k input t) checked
      case result of
        Left why -> putStrLn ("FAIL CORR-6: " ++ why) >> exitFailure
        Right records -> do
          case output of
            Nothing -> pure ()
            Just dir -> do
              createDirectoryIfMissing True dir
              forM_ records $ \(name,wire) ->
                TextIO.writeFile (dir </> name ++ ".mix") wire
          putStrLn
            "PASS CORR-6: six real source mixed U/A/L/loan joins, pre/post-join source refusals, independent finite native controls and emitted canonical source transcripts"
