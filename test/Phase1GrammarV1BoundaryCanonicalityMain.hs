{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.EncodingCanonicality (EncodingCanonicality (..))
import Phil.Surface.GrammarV1.BoundaryCanonicality
  ( grammarV1BoundaryCanonicality
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = case boundaryCanonicalityRoutesExactly of
  Right () -> putStrLn "PASS: SURF-008 Grammar-v1 boundary canonicality preserves exact Core requirement"
  Left detail -> putStrLn ("FAIL: SURF-008 boundary canonicality routing -- " <> detail) >> exitFailure

boundaryCanonicalityRoutesExactly :: Either String ()
boundaryCanonicalityRoutesExactly = do
  absent <- parseBoundary "boundary-canonicality-absent" $ Text.unlines
    [ "boundary Plain : U8 {"
    , "  failure U8;"
    , "  correspondence true;"
    , "}"
    ]
  required <- parseBoundary "boundary-canonicality-required"
    "boundary Canonical : U8 { canonical; }"
  repeated <- parseBoundary "boundary-canonicality-repeated" $ Text.unlines
    [ "boundary Repeated : U8 {"
    , "  canonical;"
    , "  failure U8;"
    , "  canonical;"
    , "}"
    ]
  let actual = map grammarV1BoundaryCanonicality [absent, required, repeated]
      expected =
        [ CanonicalityNotRequired
        , CanonicalEncodingRequired
        , CanonicalEncodingRequired
        ]
  assert (actual == expected) $
    "canonicality routing invented evidence, inferred canonicality from unrelated items, or changed explicit requirement meaning: "
      <> show actual

parseBoundary :: Text.Text -> Text.Text -> Either String GrammarV1BoundaryDecl
parseBoundary label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1BoundaryDeclaration boundary -> Right boundary
        other -> Left ("expected boundary declaration, got " <> show other)
    declarations -> Left ("expected one boundary declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
