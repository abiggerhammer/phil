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
  ( Control (..)
  , Name (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  )
import Phil.Surface.GrammarV1.CallableSignature
  ( GrammarV1CheckedFunctionHeader (..)
  , grammarV1CheckedClosedFunctionHeader
  )
import Phil.Surface.GrammarV1.ComponentBodySurface
  ( GrammarV1CheckedClosedComponentBody (..)
  , GrammarV1ComponentBodySurfaceError (..)
  , grammarV1CheckedClosedComponentBody
  )
import Phil.Surface.GrammarV1.ComponentSurface
  ( GrammarV1CheckedComponentHeader (..)
  , grammarV1CheckedClosedComponentHeader
  )
import Phil.Surface.GrammarV1.FunctionBodySurface
  ( GrammarV1CheckedClosedFunctionBody (..)
  , GrammarV1FunctionBodySurfaceError (..)
  , grammarV1CheckedClosedFunctionBody
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
        functionCompetenceBoundaries
    , test "SURF-008 closed parameter-free function bodies route through production checking"
        closedFunctionBodySemantics
    , test "SURF-008 closed function statement sequences preserve source order through production checking"
        closedFunctionBodyStatementSequence
    , test "SURF-008 closed function bodies delegate terminal sequencing rejection to production checking"
        closedFunctionBodyControlAfterTerminal
    , test "SURF-008 closed function bodies preserve exact result-type rejection"
        closedFunctionBodyResultMismatch
    , test "SURF-008 checked function bodies cannot attach to a different checked header"
        closedFunctionBodyHeaderMismatch
    , test "SURF-008 function bodies stay fail-closed before binder and richer expression competence"
        functionBodyCompetenceBoundaries
    , test "SURF-008 closed component headers preserve stable identity and checked optional signature"
        componentHeaderSemantics
    , test "SURF-008 component headers preserve omitted versus explicit-empty parameter syntax"
        componentOptionalParameterShapePreserved
    , test "SURF-008 component provides focusing failures remain semantic rejections"
        componentProvidesFocusingFailurePreserved
    , test "SURF-008 component headers remain fail-closed outside bounded competence"
        componentCompetenceBoundaries
    , test "SURF-008 closed component bodies route through production checking"
        closedComponentBodySemantics
    , test "SURF-008 closed component bodies delegate terminal sequencing rejection to production checking"
        closedComponentBodyControlAfterTerminal
    , test "SURF-008 checked component bodies cannot attach to a different checked header"
        closedComponentBodyHeaderMismatch
    , test "SURF-008 component bodies stay fail-closed before binder and richer expression competence"
        componentBodyCompetenceBoundaries
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

functionCompetenceBoundaries :: Either String ()
functionCompetenceBoundaries = do
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

closedFunctionBodySemantics :: Either String ()
closedFunctionBodySemantics = do
  boolSource <- onlyFunction
    "fn truth() -> Bool satisfies C { return true; }"
  unitSource <- onlyFunction
    "fn noop() -> Unit satisfies C { return (unit); }"
  let declarationKey = DeclarationKey "function.body.lineage"
      definitionRevision = DefinitionRevision "function.body.definition"
  boolHeader <- checkedHeader declarationKey definitionRevision boolSource
  unitHeader <- checkedHeader declarationKey definitionRevision unitSource
  assert
    ( grammarV1CheckedClosedFunctionBody emptyStaticContext boolHeader boolSource
        == Just
          (Right GrammarV1CheckedClosedFunctionBody
            { checkedClosedFunctionBodyHeader = boolHeader
            , checkedClosedFunctionBodyControls = [Return TyBool]
            })
    )
    "closed Bool return body did not route through the production surface checker"
  assert
    ( grammarV1CheckedClosedFunctionBody emptyStaticContext unitHeader unitSource
        == Just
          (Right GrammarV1CheckedClosedFunctionBody
            { checkedClosedFunctionBodyHeader = unitHeader
            , checkedClosedFunctionBodyControls = [Return TyUnit]
            })
    )
    "parenthesized Unit return body did not preserve exact terminal control"

closedFunctionBodyStatementSequence :: Either String ()
closedFunctionBodyStatementSequence = do
  source <- onlyFunction $ Text.unlines
    [ "fn sequence() -> Bool satisfies C {"
    , "  unit;"
    , "  true;"
    , "  return false;"
    , "}"
    ]
  let declarationKey = DeclarationKey "function.body.sequence.lineage"
      definitionRevision = DefinitionRevision "function.body.sequence.definition"
  header <- checkedHeader declarationKey definitionRevision source
  assert
    ( grammarV1CheckedClosedFunctionBody emptyStaticContext header source
        == Just
          (Right GrammarV1CheckedClosedFunctionBody
            { checkedClosedFunctionBodyHeader = header
            , checkedClosedFunctionBodyControls = [Return TyBool]
            })
    )
    "closed expression-statement sequence did not preserve source order and final return"

closedFunctionBodyControlAfterTerminal :: Either String ()
closedFunctionBodyControlAfterTerminal = do
  source <- onlyFunction $ Text.unlines
    [ "fn afterReturn() -> Bool satisfies C {"
    , "  return true;"
    , "  unit;"
    , "}"
    ]
  let declarationKey = DeclarationKey "function.body.terminal.lineage"
      definitionRevision = DefinitionRevision "function.body.terminal.definition"
  header <- checkedHeader declarationKey definitionRevision source
  case grammarV1CheckedClosedFunctionBody emptyStaticContext header source of
    Just (Left (GrammarV1FunctionBodySurfaceCheckError surfaceError)) ->
      assert (surfaceErrorClass surfaceError == ControlAfterTerminal)
        "production checker did not preserve control-after-terminal rejection"
    other -> Left
      ("statement after return did not fail through production checking: " <> show other)

closedFunctionBodyResultMismatch :: Either String ()
closedFunctionBodyResultMismatch = do
  source <- onlyFunction
    "fn mismatch() -> U32 satisfies C { return true; }"
  let declarationKey = DeclarationKey "function.body.mismatch.lineage"
      definitionRevision = DefinitionRevision "function.body.mismatch.definition"
  header <- checkedHeader declarationKey definitionRevision source
  let actual = grammarV1CheckedClosedFunctionBody
        emptyStaticContext header source
  assert
    (actual == Just
      (Left (GrammarV1FunctionBodyResultMismatch (TyUInt 32) [Return TyBool])))
    ("function body result mismatch was not preserved exactly: " <> show actual)

closedFunctionBodyHeaderMismatch :: Either String ()
closedFunctionBodyHeaderMismatch = do
  first <- onlyFunction
    "fn first() -> Bool satisfies C { return true; }"
  second <- onlyFunction
    "fn second() -> Bool satisfies C { return true; }"
  let declarationKey = DeclarationKey "function.body.header.lineage"
      definitionRevision = DefinitionRevision "function.body.header.definition"
  firstHeader <- checkedHeader declarationKey definitionRevision first
  secondHeader <- checkedHeader declarationKey definitionRevision second
  let actual = grammarV1CheckedClosedFunctionBody
        emptyStaticContext firstHeader second
  assert
    (actual == Just
      (Left (GrammarV1FunctionBodyHeaderMismatch firstHeader secondHeader)))
    "body from a different source declaration attached to the supplied checked header"

functionBodyCompetenceBoundaries :: Either String ()
functionBodyCompetenceBoundaries = do
  parameterized <- onlyFunction
    "fn parameterized(x : Bool) -> Bool satisfies C { return true; }"
  integerLiteral <- onlyFunction
    "fn integerLiteral() -> U32 satisfies C { return 1; }"
  namedBody <- onlyFunction
    "fn namedBody() -> Bool satisfies C { return missing; }"
  let declarationKey = DeclarationKey "function.body.boundary.lineage"
      definitionRevision = DefinitionRevision "function.body.boundary.definition"
  mapM_ (\(label, source) -> do
    header <- checkedHeader declarationKey definitionRevision source
    assert
      (grammarV1CheckedClosedFunctionBody emptyStaticContext header source == Nothing)
      (label <> " escaped the closed body competence boundary"))
    [ ("parameter-bearing body", parameterized)
    , ("integer-literal body", integerLiteral)
    , ("name-bearing body", namedBody)
    ]

checkedHeader
  :: DeclarationKey
  -> DefinitionRevision
  -> GrammarV1FunctionDecl
  -> Either String GrammarV1CheckedFunctionHeader
checkedHeader declarationKey definitionRevision source =
  case grammarV1CheckedClosedFunctionHeader
      emptyStaticContext declarationKey definitionRevision source of
    Just (Right (header, [])) -> Right header
    other -> Left ("expected closed checked function header, got " <> show other)

componentHeaderSemantics :: Either String ()
componentHeaderSemantics = do
  component <- onlyComponent $ Text.unlines
    [ "component Worker(x : U32, flag : Bool) provides U32 {"
    , "  missing;"
    , "}"
    ]
  let declarationKey = DeclarationKey "component.stable.lineage"
      definitionRevision = DefinitionRevision "component.definition.v1"
      expected = GrammarV1CheckedComponentHeader
        { checkedComponentDeclarationKey = declarationKey
        , checkedComponentDefinitionRevision = definitionRevision
        , checkedComponentDisplayName = "Worker"
        , checkedComponentParameters = Just
            [ (Name "x", TyUInt 32)
            , (Name "flag", TyBool)
            ]
        , checkedComponentProvidesType = Just (TyUInt 32)
        }
  assert
    ( grammarV1CheckedClosedComponentHeader
        emptyStaticContext declarationKey definitionRevision component
        == Just (Right (expected, []))
    )
    "closed component header lost identity, parameter order, or checked provides type"

componentOptionalParameterShapePreserved :: Either String ()
componentOptionalParameterShapePreserved = do
  omitted <- onlyComponent "component Omitted {}"
  explicitEmpty <- onlyComponent "component Explicit() {}"
  let declarationKey = DeclarationKey "component.shape.lineage"
      definitionRevision = DefinitionRevision "component.shape.definition"
      check source = grammarV1CheckedClosedComponentHeader
        emptyStaticContext declarationKey definitionRevision source
  case check omitted of
    Just (Right (header, [])) -> do
      assert (checkedComponentParameters header == Nothing)
        "omitted component parameter syntax normalized to an explicit list"
      assert (checkedComponentProvidesType header == Nothing)
        "component without provides unexpectedly acquired a type"
    other -> Left ("omitted-parameter component did not elaborate: " <> show other)
  case check explicitEmpty of
    Just (Right (header, [])) ->
      assert (checkedComponentParameters header == Just [])
        "explicit empty component parameter list was collapsed into absence"
    other -> Left ("explicit-empty component did not elaborate: " <> show other)

componentProvidesFocusingFailurePreserved :: Either String ()
componentProvidesFocusingFailurePreserved = do
  component <- onlyComponent
    "component Bad() provides Proof[Missing()] {}"
  let actual = grammarV1CheckedClosedComponentHeader
        emptyStaticContext
        (DeclarationKey "component.bad.lineage")
        (DefinitionRevision "component.bad.definition")
        component
  assert
    (actual == Just (Left (UnknownClaim "Missing")))
    ("unknown provides claim was not preserved as a Core focusing rejection: " <> show actual)

componentCompetenceBoundaries :: Either String ()
componentCompetenceBoundaries = do
  generic <- onlyComponent
    "component Generic[T : Type] {}"
  constrained <- onlyComponent
    "component Constrained requires { proposition true; } {}"
  namedParameter <- onlyComponent
    "component Named(x : Other) {}"
  duplicateParameter <- onlyComponent
    "component Duplicate(x : U32, x : Bool) {}"
  let declarationKey = DeclarationKey "component.boundary.lineage"
      definitionRevision = DefinitionRevision "component.boundary.definition"
      check source = grammarV1CheckedClosedComponentHeader
        emptyStaticContext declarationKey definitionRevision source
  mapM_ (\(label, source) ->
    assert (check source == Nothing)
      (label <> " escaped the bounded component-header competence boundary"))
    [ ("generic component", generic)
    , ("requirement-bearing component", constrained)
    , ("nonprimitive parameter", namedParameter)
    , ("duplicate parameter", duplicateParameter)
    ]

closedComponentBodySemantics :: Either String ()
closedComponentBodySemantics = do
  omitted <- onlyComponent $ Text.unlines
    [ "component Worker {"
    , "  unit;"
    , "  return true;"
    , "}"
    ]
  explicit <- onlyComponent
    "component Typed() provides U32 { return unit; }"
  let declarationKey = DeclarationKey "component.body.lineage"
      definitionRevision = DefinitionRevision "component.body.definition"
  omittedHeader <- checkedComponentHeader declarationKey definitionRevision omitted
  explicitHeader <- checkedComponentHeader declarationKey definitionRevision explicit
  assert (checkedComponentParameters omittedHeader == Nothing)
    "omitted component parameter shape changed before body checking"
  assert
    ( grammarV1CheckedClosedComponentBody emptyStaticContext omittedHeader omitted
        == Just
          (Right GrammarV1CheckedClosedComponentBody
            { checkedClosedComponentBodyHeader = omittedHeader
            , checkedClosedComponentBodyControls = [Return TyBool]
            })
    )
    "closed omitted-parameter component body did not route through production checking"
  assert
    ( checkedComponentParameters explicitHeader == Just []
      && checkedComponentProvidesType explicitHeader == Just (TyUInt 32) )
    "explicit-empty/provides component header changed before body checking"
  assert
    ( grammarV1CheckedClosedComponentBody emptyStaticContext explicitHeader explicit
        == Just
          (Right GrammarV1CheckedClosedComponentBody
            { checkedClosedComponentBodyHeader = explicitHeader
            , checkedClosedComponentBodyControls = [Return TyUnit]
            })
    )
    "closed explicit-empty component body lost checked provides/header identity"

closedComponentBodyControlAfterTerminal :: Either String ()
closedComponentBodyControlAfterTerminal = do
  source <- onlyComponent $ Text.unlines
    [ "component Terminal {"
    , "  return unit;"
    , "  true;"
    , "}"
    ]
  let declarationKey = DeclarationKey "component.body.terminal.lineage"
      definitionRevision = DefinitionRevision "component.body.terminal.definition"
  header <- checkedComponentHeader declarationKey definitionRevision source
  case grammarV1CheckedClosedComponentBody emptyStaticContext header source of
    Just (Left (GrammarV1ComponentBodySurfaceCheckError surfaceError)) ->
      assert (surfaceErrorClass surfaceError == ControlAfterTerminal)
        "component production checker did not preserve control-after-terminal rejection"
    other -> Left
      ("component statement after return did not fail through production checking: " <> show other)

closedComponentBodyHeaderMismatch :: Either String ()
closedComponentBodyHeaderMismatch = do
  first <- onlyComponent "component First { return unit; }"
  second <- onlyComponent "component Second { return unit; }"
  let declarationKey = DeclarationKey "component.body.header.lineage"
      definitionRevision = DefinitionRevision "component.body.header.definition"
  firstHeader <- checkedComponentHeader declarationKey definitionRevision first
  secondHeader <- checkedComponentHeader declarationKey definitionRevision second
  let actual = grammarV1CheckedClosedComponentBody
        emptyStaticContext firstHeader second
  assert
    (actual == Just
      (Left (GrammarV1ComponentBodyHeaderMismatch firstHeader secondHeader)))
    "body from a different component declaration attached to the supplied checked header"

componentBodyCompetenceBoundaries :: Either String ()
componentBodyCompetenceBoundaries = do
  parameterized <- onlyComponent
    "component Parameterized(x : Bool) { return unit; }"
  integerLiteral <- onlyComponent
    "component IntegerLiteral { return 1; }"
  namedBody <- onlyComponent
    "component NamedBody { missing; }"
  let declarationKey = DeclarationKey "component.body.boundary.lineage"
      definitionRevision = DefinitionRevision "component.body.boundary.definition"
  mapM_ (\(label, source) -> do
    header <- checkedComponentHeader declarationKey definitionRevision source
    assert
      (grammarV1CheckedClosedComponentBody emptyStaticContext header source == Nothing)
      (label <> " escaped the closed component-body competence boundary"))
    [ ("parameter-bearing component body", parameterized)
    , ("integer-literal component body", integerLiteral)
    , ("name-bearing component body", namedBody)
    ]

checkedComponentHeader
  :: DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedComponentHeader
checkedComponentHeader declarationKey definitionRevision source =
  case grammarV1CheckedClosedComponentHeader
      emptyStaticContext declarationKey definitionRevision source of
    Just (Right (header, [])) -> Right header
    other -> Left ("expected closed checked component header, got " <> show other)

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

onlyComponent :: Text.Text -> Either String GrammarV1ComponentDecl
onlyComponent source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "component-header" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration component -> Right component
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one component declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
