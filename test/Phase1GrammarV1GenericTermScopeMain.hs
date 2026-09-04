{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual (GenericStaticParameter (..))
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax (Name (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  )
import Phil.Surface.GrammarV1.GenericBinderScope
  ( GrammarV1ResolvedGenericParameter (..)
  )
import Phil.Surface.GrammarV1.GenericTermScope
  ( GrammarV1CheckedGenericTermScope (..)
  , GrammarV1GenericTermScopeError (..)
  , grammarV1CheckedCallableGenericTermScope
  , grammarV1CheckedClaimGenericTermScope
  , grammarV1CheckedComponentGenericTermScope
  , grammarV1CheckedFunctionGenericTermScope
  , grammarV1CheckedProtocolGenericTermScope
  , grammarV1CheckedProviderImplementationGenericTermScope
  , grammarV1TermBinderSitesInBlock
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax
  ( Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 function term parameters cannot shadow active generic parameters"
        functionParameterCannotShadowGeneric
    , test "SURF-009 nested body binders cannot shadow active generic parameters"
        nestedBodyBinderCannotShadowGeneric
    , test "SURF-009 callable claim and component term parameters share the no-shadow boundary"
        headerTermFamiliesCannotShadowGeneric
    , test "SURF-009 provider implementation body binders cannot shadow generics"
        providerBodyCannotShadowGeneric
    , test "SURF-009 protocol message binders cannot shadow protocol generics"
        protocolMessageCannotShadowGeneric
    , test "SURF-009 distinct static and runtime names retain distinct semantic identity domains"
        distinctNamespacesRetainDistinctIdentity
    , test "SURF-009 cross-domain traversal reaches every nested runtime binder family"
        nestedBinderInventoryIsComplete
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

functionParameterCannotShadowGeneric :: Either String ()
functionParameterCannotShadowGeneric = do
  functionDecl <- onlyFunction
    "fn collision[n : Nat](n : U8) -> U8 satisfies C { return n; }"
  expectStaticShadow "n" $
    grammarV1CheckedFunctionGenericTermScope
      (DeclarationKey "decl.FunctionCollision")
      functionDecl

nestedBodyBinderCannotShadowGeneric :: Either String ()
nestedBodyBinderCannotShadowGeneric = do
  functionDecl <- onlyFunction $ Text.unlines
    [ "fn nested[view : Nat](seed : U8) -> U8 satisfies C {"
    , "  borrow seed as view { return view; };"
    , "  return seed;"
    , "}"
    ]
  expectStaticShadow "view" $
    grammarV1CheckedFunctionGenericTermScope
      (DeclarationKey "decl.NestedCollision")
      functionDecl

headerTermFamiliesCannotShadowGeneric :: Either String ()
headerTermFamiliesCannotShadowGeneric = do
  callable <- onlyCallable
    "callable CallableCollision[n : Nat](n : U8) -> Unit {}"
  claim <- onlyClaim
    "claim ClaimCollision[n : Nat](n : U8) = true;"
  component <- onlyComponent
    "component ComponentCollision[n : Nat](n : U8) { return n; }"
  expectStaticShadow "n" $
    grammarV1CheckedCallableGenericTermScope
      (DeclarationKey "decl.CallableCollision")
      callable
  expectStaticShadow "n" $
    grammarV1CheckedClaimGenericTermScope
      (DeclarationKey "decl.ClaimCollision")
      claim
  expectStaticShadow "n" $
    grammarV1CheckedComponentGenericTermScope
      (DeclarationKey "decl.ComponentCollision")
      component

providerBodyCannotShadowGeneric :: Either String ()
providerBodyCannotShadowGeneric = do
  provider <- onlyProviderImplementation $ Text.unlines
    [ "provider implementation ProviderCollision[n : Nat] satisfies Contract {"
    , "  operation op satisfies C {"
    , "    let n = unit;"
    , "    return n;"
    , "  }"
    , "}"
    ]
  expectStaticShadow "n" $
    grammarV1CheckedProviderImplementationGenericTermScope
      (DeclarationKey "decl.ProviderCollision")
      provider

protocolMessageCannotShadowGeneric :: Either String ()
protocolMessageCannotShadowGeneric = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol ProtocolCollision[n : Nat] {"
    , "  role Client = send (n : U8) then end Done;"
    , "  role Server = receive (value : U8) then end Done;"
    , "}"
    ]
  expectStaticShadow "n" $
    grammarV1CheckedProtocolGenericTermScope
      (DeclarationKey "decl.ProtocolCollision")
      protocol

distinctNamespacesRetainDistinctIdentity :: Either String ()
distinctNamespacesRetainDistinctIdentity = do
  functionDecl <- onlyFunction $ Text.unlines
    [ "fn distinct[n : Nat](x : U8) -> U8 satisfies C {"
    , "  let y = x;"
    , "  return y;"
    , "}"
    ]
  checked <- mapLeft show $
    grammarV1CheckedFunctionGenericTermScope
      (DeclarationKey "decl.Distinct")
      functionDecl
  generic <- exactlyOne
    "resolved generic parameter"
    (grammarV1CheckedGenericTermParameters checked)
  assert
    (map locatedValue (grammarV1CheckedGenericTermBinderSites checked) == ["x", "y"])
    "generic/term composition lost function parameter or let binder sites"
  (termParameters, _) <- mapLeft show $
    grammarV1FunctionParameterScope (DeclarationKey "decl.Distinct") functionDecl
  termParameter <- exactlyOne "resolved term parameter" termParameters
  let GenericStaticParameterKey staticKey =
        genericStaticParameterKey (grammarV1ResolvedGenericParameter generic)
      Name termCoreName = grammarV1ResolvedBinderCoreName termParameter
  assert ("$phil.static:" `Text.isPrefixOf` staticKey)
    "generic parameter did not retain static-key identity domain"
  assert ("$phil.local:" `Text.isPrefixOf` termCoreName)
    "term parameter did not retain local Core-name identity domain"
  assert (staticKey /= termCoreName)
    "static and runtime binders collapsed to one semantic name"

nestedBinderInventoryIsComplete :: Either String ()
nestedBinderInventoryIsComplete = do
  let sites = map locatedValue (grammarV1TermBinderSitesInBlock nestedBlock)
      expected =
        [ "left"
        , "right"
        , "view"
        , "inside"
        , "item"
        , "arm_local"
        , "joined"
        , "i"
        , "arg"
        , "closure_local"
        ]
  assert (sites == expected)
    ("nested binder inventory changed source/semantic traversal: " <> show sites)

nestedBlock :: Located GrammarV1Block
nestedBlock = block
  [ letStatement
      (GrammarV1TuplePattern
        [ loc (GrammarV1IdentifierPattern (name "left"))
        , loc (GrammarV1IdentifierPattern (name "right"))
        ])
      unitExpression
  , expressionStatement $
      loc (GrammarV1BorrowExpression
        unitExpression
        (name "view")
        (block [letStatement (GrammarV1IdentifierPattern (name "inside")) unitExpression]))
  , expressionStatement $
      loc (GrammarV1MatchExpression
        unitExpression
        (Just (loc (GrammarV1JoinClause [loc (stateSlot "joined")] Nothing)))
        [loc (matchArm "item" (block
          [letStatement (GrammarV1IdentifierPattern (name "arm_local")) unitExpression]))])
  , expressionStatement $
      loc (GrammarV1LoopExpression
        [loc (stateBinding "i")]
        Nothing
        (block
          [ expressionStatement $
              loc (GrammarV1ClosureExpression
                (closure "arg" (block
                  [letStatement (GrammarV1IdentifierPattern (name "closure_local")) unitExpression])))
          ]))
  ]

stateSlot :: Text.Text -> GrammarV1StateSlot
stateSlot displayName = GrammarV1StateSlot
  (name displayName)
  (loc GrammarV1UnitType)

stateBinding :: Text.Text -> GrammarV1StateBinding
stateBinding displayName = GrammarV1StateBinding
  (name displayName)
  Nothing
  unitExpression

matchArm :: Text.Text -> Located GrammarV1Block -> GrammarV1MatchArm
matchArm displayName body = GrammarV1MatchArm
  (loc (GrammarV1CasePattern
    (loc (GrammarV1QualifiedName ["Some"]))
    (Just (GrammarV1TupleCaseBinders [name displayName]))))
  (GrammarV1MatchArmBlock body)

closure :: Text.Text -> Located GrammarV1Block -> GrammarV1Closure
closure displayName body = GrammarV1Closure
  Nothing
  [loc (GrammarV1TermParam (name displayName) (loc GrammarV1UnitType))]
  (loc GrammarV1UnitType)
  Nothing
  body

expectStaticShadow
  :: Text.Text
  -> Either GrammarV1GenericTermScopeError GrammarV1CheckedGenericTermScope
  -> Either String ()
expectStaticShadow expected result = case result of
  Left (GrammarV1GenericTermActiveStaticShadowing sourceName previous) -> do
    assert (locatedValue sourceName == expected)
      "cross-domain shadow diagnostic lost term spelling"
    assert (genericDisplayName previous == expected)
      "cross-domain shadow diagnostic lost generic binder"
  other -> Left ("expected active generic/term shadow rejection, got " <> show other)

genericDisplayName :: GrammarV1ResolvedGenericParameter -> Text.Text
genericDisplayName =
  locatedValue
  . grammarV1GenericParamName
  . locatedValue
  . grammarV1ResolvedGenericSource

onlyFunction :: Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction = onlyDeclaration select
  where
    select declaration = case declaration of
      GrammarV1FunctionDeclaration value -> Just value
      _ -> Nothing

onlyCallable :: Text.Text -> Either String GrammarV1CallableContractDecl
onlyCallable = onlyDeclaration select
  where
    select declaration = case declaration of
      GrammarV1CallableContractDeclaration value -> Just value
      _ -> Nothing

onlyClaim :: Text.Text -> Either String GrammarV1ClaimDecl
onlyClaim = onlyDeclaration select
  where
    select declaration = case declaration of
      GrammarV1ClaimDeclaration value -> Just value
      _ -> Nothing

onlyComponent :: Text.Text -> Either String GrammarV1ComponentDecl
onlyComponent = onlyDeclaration select
  where
    select declaration = case declaration of
      GrammarV1ComponentDeclaration value -> Just value
      _ -> Nothing

onlyProviderImplementation :: Text.Text -> Either String GrammarV1ProviderImplementationDecl
onlyProviderImplementation = onlyDeclaration select
  where
    select declaration = case declaration of
      GrammarV1ProviderImplementationDeclaration value -> Just value
      _ -> Nothing

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol = onlyDeclaration select
  where
    select declaration = case declaration of
      GrammarV1ProtocolDeclaration value -> Just value
      _ -> Nothing

onlyDeclaration
  :: (GrammarV1Declaration -> Maybe a)
  -> Text.Text
  -> Either String a
onlyDeclaration select source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "generic-term-scope" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] ->
      case select (locatedValue (grammarV1Declaration topLevel)) of
        Just value -> Right value
        Nothing -> Left "parsed one declaration of the wrong category"
    declarations -> Left
      ("expected one declaration, got " <> show (length declarations))

block :: [Located GrammarV1Statement] -> Located GrammarV1Block
block statements = loc (GrammarV1Block statements)

letStatement
  :: GrammarV1Pattern
  -> Located GrammarV1Expression
  -> Located GrammarV1Statement
letStatement patternSource initializer =
  loc (GrammarV1LetStatement (loc patternSource) initializer)

expressionStatement :: Located GrammarV1Expression -> Located GrammarV1Statement
expressionStatement = loc . GrammarV1ExpressionStatement

unitExpression :: Located GrammarV1Expression
unitExpression = loc GrammarV1UnitExpression

name :: Text.Text -> Located Text.Text
name = loc

loc :: a -> Located a
loc = Located syntheticSpan

syntheticSpan :: SourceSpan
syntheticSpan = SourceSpan point point
  where
    point = SourcePoint
      { sourcePointFile = "generic-term-scope"
      , sourcePointLine = 1
      , sourcePointColumn = 1
      , sourcePointOffset = 0
      }

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
