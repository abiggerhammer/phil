{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Syntax (GrammarId (..), Ty (..))
import Phil.Surface.GrammarV1.IntrinsicFrameType (grammarV1BareFrameType)
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 bare Grammar-v1 Frame types preserve exact grammar identity"
        bareFrameTypesPreserveIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

bareFrameTypesPreserveIdentity :: Either String ()
bareFrameTypesPreserveIdentity = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bare-frame-types" source
  actual <- mapM frameType (grammarV1TopLevelDecls sourceFile)
  let expected =
        [ Just (TyFrame (GrammarId "Hello"))
        , Just (TyFrame (GrammarId "Wire.Codec"))
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "Frame elaboration changed qualified identity or flattened specialization: " <> show actual

frameType :: Located GrammarV1TopLevelDecl -> Either String (Maybe Ty)
frameType (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (grammarV1BareFrameType (locatedValue (grammarV1TypeAliasTarget aliasDecl)))
    other -> Left ("expected type alias declaration, got " <> show other)

source :: Text.Text
source = Text.unlines
  [ "type SimpleFrame = Frame[Hello];"
  , "type QualifiedFrame = Frame[Wire.Codec];"
  , "type SpecializedFrame = Frame[Wire.Codec[U32]];"
  , "type NotFrame = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
