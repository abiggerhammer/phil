{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , emptyContext
  , ensureComplete
  , insertBinding
  )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  , runtimeBytesType
  )
import Phil.Core.Value
  ( ValueError (..)
  , ValueResult (..)
  , checkValue
  , synthValue
  , transportValue
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedTypeMode
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1IntrinsicBytesType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("bare and exact Bytes parse and elaborate in one family", syntaxAndElaboration)
        , ("bare and exact Bytes are both linear", bothBytesFormsAreLinear)
        , ("exact Bytes may forget the index without evidence or owner change", exactIndexForgetting)
        , ("dynamic Bytes require explicit length transport to regain an exact index", dynamicRefinementRequiresTransport)
        , ("dynamic Bytes refine with exact len(value) evidence", dynamicRefinementWithEvidence)
        , ("wrong length evidence does not refine dynamic Bytes", dynamicRefinementRejectsWrongEvidence)
        , ("runtime-sized Bytes cannot be copied", runtimeBytesCannotBeCopied)
        , ("runtime-sized Bytes cannot be dropped", runtimeBytesCannotBeDropped)
        ]
  mapM_ report checks
  unlessAll checks
  where
    report (label, Right ()) = putStrLn ("PASS: IO-BYTES-001 " <> label)
    report (label, Left detail) = putStrLn ("FAIL: IO-BYTES-001 " <> label <> " -- " <> detail)

unlessAll :: [(String, Either String ())] -> IO ()
unlessAll checks =
  if all (either (const False) (const True) . snd) checks
    then pure ()
    else exitFailure

syntaxAndElaboration :: Either String ()
syntaxAndElaboration = do
  parsed <- mapLeft show $ parseGrammarV1StructuralSource "io-bytes-types" $ Text.unlines
    [ "type Dynamic = Bytes;"
    , "type Exact = Bytes[4];"
    ]
  case grammarV1TopLevelDecls parsed of
    [dynamicDecl, exactDecl] -> do
      dynamicType <- typeAliasTarget dynamicDecl
      exactType <- typeAliasTarget exactDecl
      assert
        (grammarV1IntrinsicBytesType dynamicType == Just runtimeBytesType)
        "bare Bytes did not elaborate to the runtime-sized member of TyBytes"
      assert
        (grammarV1IntrinsicBytesType exactType == Just exactBytes4)
        "Bytes[4] exact elaboration changed"
    other -> Left ("expected exactly two type aliases, got " <> show (length other))

bothBytesFormsAreLinear :: Either String ()
bothBytesFormsAreLinear = do
  parsed <- mapLeft show $ parseGrammarV1StructuralSource "io-bytes-mode" $ Text.unlines
    [ "type Dynamic = Bytes;"
    , "type Exact = Bytes[4];"
    ]
  case grammarV1TopLevelDecls parsed of
    [dynamicDecl, exactDecl] -> do
      dynamicType <- typeAliasTarget dynamicDecl
      exactType <- typeAliasTarget exactDecl
      dynamicMode <- checkedMode dynamicType
      exactMode <- checkedMode exactType
      assert
        (checkedBindingType dynamicMode == runtimeBytesType
          && checkedBindingMode dynamicMode == Linear)
        "bare Bytes was not checked as linear runtime-sized bytes"
      assert
        (checkedBindingType exactMode == exactBytes4
          && checkedBindingMode exactMode == Linear)
        "Bytes[4] stopped being linear"
    other -> Left ("expected exactly two type aliases, got " <> show (length other))

exactIndexForgetting :: Either String ()
exactIndexForgetting = do
  context <- mapLeft show $ insertBinding Linear payload exactBytes4 emptyContext
  result <- mapLeft show $ checkValue (VVar payload) runtimeBytesType
    (emptyCheckState { resourceContext = context })
  assert (valueResultType result == runtimeBytesType)
    "exact Bytes did not forget to bare Bytes"
  assert (valueResultTerm result == Just (RefVar payload))
    "forgetting exact length changed value identity"
  assert (Map.notMember payload (linearBindingsOf result))
    "forgetting exact length duplicated or retained the consumed linear owner"

dynamicRefinementRequiresTransport :: Either String ()
dynamicRefinementRequiresTransport = do
  context <- mapLeft show $ insertBinding Linear payload runtimeBytesType emptyContext
  case checkValue (VVar payload) exactBytes4
      (emptyCheckState { resourceContext = context }) of
    Left (ExplicitTransportRequired actual expected) ->
      assert (actual == runtimeBytesType && expected == exactBytes4)
        "dynamic-to-exact rejection named the wrong types"
    other -> Left ("dynamic Bytes refined without explicit checked evidence: " <> show other)

dynamicRefinementWithEvidence :: Either String ()
dynamicRefinementWithEvidence = do
  contextWithPayload <- mapLeft show $
    insertBinding Linear payload runtimeBytesType emptyContext
  context <- mapLeft show $
    insertBinding Unrestricted proofName lengthProofType contextWithPayload
  result <- mapLeft show $ transportValue
    (VVar payload)
    proofName
    exactBytes4
    (emptyCheckState { resourceContext = context })
  assert (valueResultType result == exactBytes4)
    "accepted length evidence did not restore Bytes[4]"
  assert (valueResultTerm result == Just (RefVar payload))
    "refining dynamic Bytes changed value identity"
  assert (Map.notMember payload (linearBindingsOf result))
    "refinement duplicated or retained the consumed linear owner"

dynamicRefinementRejectsWrongEvidence :: Either String ()
dynamicRefinementRejectsWrongEvidence = do
  contextWithPayload <- mapLeft show $
    insertBinding Linear payload runtimeBytesType emptyContext
  context <- mapLeft show $
    insertBinding Unrestricted proofName wrongLengthProofType contextWithPayload
  case transportValue
      (VVar payload)
      proofName
      exactBytes4
      (emptyCheckState { resourceContext = context }) of
    Left (ValueRefinementError _) -> Right ()
    other -> Left ("wrong len(value) evidence refined dynamic Bytes: " <> show other)

runtimeBytesCannotBeCopied :: Either String ()
runtimeBytesCannotBeCopied = do
  context <- mapLeft show $ insertBinding Linear payload runtimeBytesType emptyContext
  first <- mapLeft show $ synthValue
    (VVar payload)
    (emptyCheckState { resourceContext = context })
  case synthValue (VVar payload) (valueResultState first) of
    Left (ValueResourceError (UnknownBinding missing)) ->
      assert (missing == payload) "copy rejection named the wrong owner"
    other -> Left ("runtime-sized linear Bytes was usable twice: " <> show other)

runtimeBytesCannotBeDropped :: Either String ()
runtimeBytesCannotBeDropped = do
  context <- mapLeft show $ insertBinding Linear payload runtimeBytesType emptyContext
  case ensureComplete context of
    Left (UnconsumedLinearResources leftovers) ->
      assert
        (Map.lookup payload leftovers == Just runtimeBytesType)
        "drop rejection did not retain exact runtime Bytes owner/type"
    other -> Left ("runtime-sized linear Bytes could be silently dropped: " <> show other)

checkedMode :: GrammarV1Type -> Either String CheckedTypeMode
checkedMode sourceType =
  case grammarV1CheckedTypeMode emptyStaticContext emptySurfaceState sourceType of
    Just (Right (mode, [])) -> Right mode
    other -> Left ("could not derive checked type mode: " <> show other)

typeAliasTarget :: Located GrammarV1TopLevelDecl -> Either String GrammarV1Type
typeAliasTarget (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (locatedValue (grammarV1TypeAliasTarget aliasDecl))
    other -> Left ("expected type alias declaration, got " <> show other)

linearBindingsOf :: ValueResult -> Map.Map Name Ty
linearBindingsOf = linearBindings . resourceContext . valueResultState

payload :: Name
payload = Name "payload"

proofName :: Name
proofName = Name "length-proof"

exactBytes4 :: Ty
exactBytes4 = TyBytes (RefNat 4)

lengthProofType :: Ty
lengthProofType = TyProof (Equal (RefLen (RefVar payload)) (RefNat 4))

wrongLengthProofType :: Ty
wrongLengthProofType = TyProof (Equal (RefLen (RefVar payload)) (RefNat 5))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
