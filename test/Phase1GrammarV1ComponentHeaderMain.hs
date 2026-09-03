{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusingError (..)
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
import Phil.Surface.GrammarV1.ComponentSurface
  ( GrammarV1CheckedComponentHeader (..)
  , grammarV1CheckedClosedComponentHeader
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed component headers preserve stable identity and checked optional signature"
        checkedHeaderSemantics
    , test "SURF-008 component headers preserve omitted versus explicit-empty parameter syntax"
        optionalParameterShapePreserved
    , test "SURF-008 component provides focusing failures remain semantic rejections"
        providesFocusingFailurePreserved
    , test "SURF-008 component headers remain fail-closed outside bounded competence"
        competenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedHeaderSemantics :: Either String ()
checkedHeaderSemantics = do
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

optionalParameterShapePreserved :: Either String ()
optionalParameterShapePreserved = do
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

providesFocusingFailurePreserved :: Either String ()
providesFocusingFailurePreserved = do
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

competenceBoundaries :: Either String ()
competenceBoundaries = do
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
