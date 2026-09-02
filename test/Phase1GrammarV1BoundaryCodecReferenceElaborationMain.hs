{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Surface.GrammarV1.BoundaryCodecReferences
  ( grammarV1BoundaryReceiveCodecs
  , grammarV1BoundarySendCodecs
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 boundary codec references preserve unresolved static identity"
        boundaryCodecReferencesPreserveIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

boundaryCodecReferencesPreserveIdentity :: Either String ()
boundaryCodecReferencesPreserveIdentity = do
  none <- parseBoundary "codec-none"
    "boundary None : U8 { canonical; }"
  rich <- parseBoundary "codec-rich" $ Text.unlines
    [ "boundary Codecs : U8 {"
    , "  receive using Decoder;"
    , "  receive using wire.Decoder;"
    , "  send using Encoder;"
    , "  send using wire.Encoder;"
    , "}"
    ]
  unresolvedReceive <- parseBoundary "codec-specialized-receive" $ Text.unlines
    [ "boundary BadReceive : U8 {"
    , "  receive using Decoder[U8];"
    , "  send using Encoder;"
    , "}"
    ]
  unresolvedSend <- parseBoundary "codec-specialized-send" $ Text.unlines
    [ "boundary BadSend : U8 {"
    , "  receive using Decoder;"
    , "  send using Encoder[U8];"
    , "}"
    ]
  let boundaries = [none, rich, unresolvedReceive, unresolvedSend]
      actualReceive = map grammarV1BoundaryReceiveCodecs boundaries
      actualSend = map grammarV1BoundarySendCodecs boundaries
      expectedReceive =
        [ Just []
        , Just
            [ ReferencedGenericStaticActual "Decoder"
            , ReferencedGenericStaticActual "wire.Decoder"
            ]
        , Nothing
        , Just [ReferencedGenericStaticActual "Decoder"]
        ]
      expectedSend =
        [ Just []
        , Just
            [ ReferencedGenericStaticActual "Encoder"
            , ReferencedGenericStaticActual "wire.Encoder"
            ]
        , Just [ReferencedGenericStaticActual "Encoder"]
        , Nothing
        ]
  assert (actualReceive == expectedReceive) $
    "receive codec routing changed identity, erased specialization, or coupled to send resolution: "
      <> show actualReceive
  assert (actualSend == expectedSend) $
    "send codec routing changed identity, erased specialization, or coupled to receive resolution: "
      <> show actualSend

parseBoundary :: Text.Text -> Text.Text -> Either String GrammarV1BoundaryDecl
parseBoundary label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1BoundaryDeclaration boundary -> Right boundary
      other -> Left ("expected boundary declaration, got " <> show other)
    declarations -> Left
      ("expected one boundary declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
