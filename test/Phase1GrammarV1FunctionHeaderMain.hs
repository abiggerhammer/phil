{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusingError (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.CallableSignature
  ( GrammarV1CheckedFunctionHeader (..)
  , grammarV1CheckedClosedFunctionHeader
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed function headers preserve stable identity and checked signature"
        closedHeaderSemantics
    , test "SURF-008 function headers preserve the explicit recursive marker"
        recursionMarkerPreserved
    , test "SURF-008 function result focusing failures remain semantic rejections"
        resultFocusingFailurePreserved
    , test "SURF-008 function headers remain fail-closed outside bounded competence"
        competenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closedHeaderSemantics :: Either String ()
closedHeaderSemantics = do
  source <- onlyFunction $ Text.unlines
    [ "fn identity(x : U32, flag : Bool) -> U32 satisfies pkg.Identity {"
    , "  return missing;"
    , "}"
    ]
  let declarationKey = DeclarationKey "function.stable.lineage"
      definitionRevision = DefinitionRevision "function.definition.v1"
      expected = GrammarV1CheckedFunctionHeader
        { checkedFunctionDeclarationKey = declarationKey
        , checkedFunctionDefinitionRevision = definitionRevision
        , checkedFunctionRecursive = False
        , checkedFunctionDisplayName = "identity"
        , checkedFunctionParameters =
            [ (Name "x", TyUInt 32)
            , (Name "flag", TyBool)
            ]
        , checkedFunctionResultType = TyUInt 32
        , checkedFunctionSatisfiesReference =
            ReferencedGenericStaticActual "pkg.Identity"
        }
  assert
    ( grammarV1CheckedClosedFunctionHeader
        emptyStaticContext declarationKey definitionRevision source
        == Just (Right (expected, []))
    )
    "closed function header lost stable identity, parameter/result meaning, or satisfies reference"
  -- The body deliberately contains an unresolved name. Header success therefore
  -- cannot be mistaken for a claim that body semantics were checked by this slice.
  case grammarV1BlockStatements (locatedValue (grammarV1FunctionBody source)) of
    [ Located _
        (GrammarV1ReturnStatement
          (Located _ (GrammarV1NameExpression reference arguments)))
      ] -> do
        assert (null arguments)
          "deliberately unresolved body name unexpectedly acquired term arguments"
        assert (null (grammarV1StaticReferenceArguments reference))
          "deliberately unresolved body name unexpectedly acquired static arguments"
        assert
          (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == ["missing"])
          "test body no longer carries the deliberately unresolved name"
    body -> Left ("unexpected function body shape: " <> show body)

recursionMarkerPreserved :: Either String ()
recursionMarkerPreserved = do
  source <- onlyFunction
    "recursive fn recur(x : U32) -> U32 satisfies Rec { return x; }"
  let declarationKey = DeclarationKey "function.recur.lineage"
      definitionRevision = DefinitionRevision "function.recur.definition"
  case grammarV1CheckedClosedFunctionHeader
      emptyStaticContext declarationKey definitionRevision source of
    Just (Right (header, [])) -> do
      assert (checkedFunctionRecursive header)
        "recursive source marker was dropped from checked function header"
      assert
        (checkedFunctionSatisfiesReference header
          == ReferencedGenericStaticActual "Rec")
        "recursive header changed the unresolved satisfies reference"
    other -> Left ("recursive closed header did not elaborate: " <> show other)

resultFocusingFailurePreserved :: Either String ()
resultFocusingFailurePreserved = do
  source <- onlyFunction
    "fn bad() -> Proof[Missing()] satisfies C { return proof; }"
  let actual = grammarV1CheckedClosedFunctionHeader
        emptyStaticContext
        (DeclarationKey "function.bad.lineage")
        (DefinitionRevision "function.bad.definition")
        source
  assert
    (actual == Just (Left (UnknownClaim "Missing")))
    ("unknown result claim was not preserved as a Core focusing rejection: " <> show actual)

competenceBoundaries :: Either String ()
competenceBoundaries = do
  generic <- onlyFunction
    "fn generic[T : Type](x : U32) -> U32 satisfies C { return x; }"
  constrained <- onlyFunction $ Text.unlines
    [ "fn constrained requires { proposition true; }() -> U32 satisfies C {"
    , "  return 1;"
    , "}"
    ]
  namedParameter <- onlyFunction
    "fn named(x : Other) -> U32 satisfies C { return 1; }"
  duplicateParameter <- onlyFunction
    "fn duplicate(x : U32, x : Bool) -> U32 satisfies C { return x; }"
  omittedResult <- onlyFunction
    "fn inferred() satisfies C { return 1; }"
  specializedSatisfies <- onlyFunction
    "fn specialized() -> U32 satisfies C[U32] { return 1; }"
  let declarationKey = DeclarationKey "function.boundary.lineage"
      definitionRevision = DefinitionRevision "function.boundary.definition"
      check source = grammarV1CheckedClosedFunctionHeader
        emptyStaticContext declarationKey definitionRevision source
  mapM_ (\(label, source) ->
    assert (check source == Nothing)
      (label <> " escaped the bounded function-header competence boundary"))
    [ ("generic function", generic)
    , ("requirement-bearing function", constrained)
    , ("nonprimitive parameter", namedParameter)
    , ("duplicate parameter", duplicateParameter)
    , ("omitted result type", omittedResult)
    , ("specialized satisfies reference", specializedSatisfies)
    ]

onlyFunction :: Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "function-header" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1FunctionDeclaration function -> Right function
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left
      ("expected one function declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
