{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Static
  ( DeclarationKey (..)
  , StaticContext
  , declareOpaqueClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SemanticCallableOutcomePropositions
  ( grammarV1CheckedSemanticCallableOutcomeEnsuresAfterResult
  )
import Phil.Surface.GrammarV1.SemanticCallableOutcomeState
  ( GrammarV1SemanticCallableOutcomeResidueScope (..)
  , GrammarV1SemanticCallableOutcomeStateScope (..)
  , grammarV1SemanticCallableOutcomeScopesAfterResult
  )
import Phil.Surface.GrammarV1.SemanticCallablePropositions
  ( GrammarV1CheckedSemanticCallableProposition (..)
  )
import Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1CheckedSemanticCallableSignature (..)
  , grammarV1CheckedSemanticCallableSignature
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = case composedCallableUsesOneOrdinalStream of
  Right () -> putStrLn "PASS: SURF-009 callable result refinements compose with outcome state in one ordinal stream"
  Left detail -> putStrLn ("FAIL: SURF-009 callable composition -- " <> detail) >> exitFailure

composedCallableUsesOneOrdinalStream :: Either String ()
composedCallableUsesOneOrdinalStream = do
  callable <- onlyCallable $ Text.unlines
    [ "callable RefinedOutcome(x : U8) -> {v : U8 | v <= x} {"
    , "  outcome success Done {"
    , "    state (s : U8);"
    , "    ensures PairOk(x, s);"
    , "  }"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.SemanticCallableComposition"
  signature <- checkedSignature declarationKey callable
  xBinder <- exactlyOne "callable parameter binder"
    (map fst (checkedSemanticCallableParameters signature))
  vBinder <- maybe
    (Left "result refinement did not retain its semantic binder evidence")
    Right
    (checkedSemanticCallableResultRefinementBinder signature)
  let xName = grammarV1ResolvedBinderCoreName xBinder
      vName = grammarV1ResolvedBinderCoreName vBinder
  assert
    (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey xBinder) == 0)
    "callable parameter did not receive ordinal 0"
  assert
    (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey vBinder) == 1)
    "result refinement binder did not receive ordinal 1"
  assert
    ( checkedSemanticCallableResultType signature
        == TyRefined
          vName
          (TyUInt 8)
          (LessEqual (RefVar vName) (RefVar xName))
    )
    "callable result refinement lost exact parameter/refinement identities"
  case grammarV1ResolveLocal
      (Located (grammarV1ResolvedBinderSourceSpan vBinder) "v")
      (checkedSemanticCallableLexicalScope signature) of
    Left (GrammarV1BinderNotInScope _) -> Right ()
    other -> Left ("closed result refinement binder remained active: " <> show other)

  residueScopes <- case grammarV1SemanticCallableOutcomeScopesAfterResult
      emptyStaticContext declarationKey callable of
    Just (Right scopes) -> Right scopes
    other -> Left ("expected composed semantic outcome scopes, got " <> show other)
  residue <- exactlyOne "composed outcome residue" residueScopes
  stateScope <- exactlyOne
    "composed outcome state scope"
    (semanticCallableOutcomeResidueStateScopes residue)
  (sBinder, TyUInt 8) <- exactlyOne
    "composed outcome state binding"
    (semanticCallableOutcomeStateBindings stateScope)
  let sName = grammarV1ResolvedBinderCoreName sBinder
  assert
    (grammarV1BinderOrdinal (grammarV1ResolvedBinderKey sBinder) == 2)
    "outcome state binder reused the closed result-refinement ordinal"
  resolvedX <- mapLeft show $ grammarV1ResolveLocal
    (Located (grammarV1ResolvedBinderSourceSpan xBinder) "x")
    (semanticCallableOutcomeResidueBaseLexicalScope residue)
  assert
    (grammarV1ResolvedBinderKey resolvedX == grammarV1ResolvedBinderKey xBinder)
    "callable parameter stopped resolving after result refinement closed"
  case grammarV1ResolveLocal
      (Located (grammarV1ResolvedBinderSourceSpan vBinder) "v")
      (semanticCallableOutcomeResidueBaseLexicalScope residue) of
    Left (GrammarV1BinderNotInScope _) -> Right ()
    other -> Left ("result refinement binder leaked into outcome scope: " <> show other)

  context <- pairContext
  ensured <- case grammarV1CheckedSemanticCallableOutcomeEnsuresAfterResult
      context declarationKey callable of
    Just (Right checked) -> Right checked
    other -> Left ("expected composed semantic outcome ensures, got " <> show other)
  checked <- case ensured of
    [(GrammarV1SuccessOutcome, [value])] -> Right value
    other -> Left ("unexpected composed outcome ensures shape: " <> show other)
  assert
    (checkedSemanticCallablePropositionCore checked
      == Atom "PairOk" [RefVar xName, RefVar sName])
    "composed outcome proposition did not consume parameter/state semantic names"
  assert
    ( map referenceKey (checkedSemanticCallablePropositionReferences checked)
        == [ grammarV1ResolvedBinderKey xBinder
           , grammarV1ResolvedBinderKey sBinder
           ]
    )
    "composed outcome proposition references did not retain exact binder evidence"

checkedSignature
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either String GrammarV1CheckedSemanticCallableSignature
checkedSignature declarationKey callable =
  case grammarV1CheckedSemanticCallableSignature
      emptyStaticContext declarationKey callable of
    Just (Right (signature, [])) -> Right signature
    other -> Left ("expected checked semantic callable signature, got " <> show other)

pairContext :: Either String StaticContext
pairContext = mapLeft show $
  declareOpaqueClaim
    "PairOk"
    [(Name "x", SortUInt 8), (Name "s", SortUInt 8)]
    emptyStaticContext

referenceKey :: GrammarV1CheckedLexicalReference -> GrammarV1BinderKey
referenceKey =
  grammarV1ResolvedBinderKey . grammarV1CheckedLexicalReferenceBinder

onlyCallable :: Text.Text -> Either String GrammarV1CallableContractDecl
onlyCallable source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "semantic-callable-composition" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1CallableDeclaration callable -> Right callable
      other -> Left ("expected callable declaration, got " <> show other)
    declarations -> Left
      ("expected one callable declaration, got " <> show (length declarations))

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left
  ("expected exactly one " <> label <> ", got " <> show (length values))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
