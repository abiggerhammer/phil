{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.GrammarV1.IntrinsicNamedType (grammarV1BareNamedType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 bare Grammar-v1 named types preserve exact opaque identity"
        bareNamedTypesPreserveIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

bareNamedTypesPreserveIdentity :: Either String ()
bareNamedTypesPreserveIdentity = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bare-named-types" source
  actual <- mapM namedType (grammarV1TopLevelDecls sourceFile)
  let expected =
        [ Just (TyOpaque "Payload")
        , Just (TyOpaque "Wire.Payload")
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "named-type elaboration changed qualified identity or flattened specialization: " <> show actual

namedType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
namedType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1BareNamedType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type SimpleNamed = Payload;"
  , "type QualifiedNamed = Wire.Payload;"
  , "type SpecializedNamed = Wire.Payload[U32];"
  , "type NotNamed = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
