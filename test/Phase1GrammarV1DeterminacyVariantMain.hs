{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = case variantPayloadDeterminacy of
  Right () -> putStrLn "PASS: SURF-005 variant payload commas have one interpretation"
  Left detail -> putStrLn ("FAIL: SURF-005 variant payload commas -- " <> detail) >> exitFailure

variantPayloadDeterminacy :: Either String ()
variantPayloadDeterminacy = do
  sourceFile <- parse "data Choice = Pair(U8, Bool) | Named{left : U8, right : Bool,};"
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1DataDeclaration dataDecl -> case grammarV1DataVariants dataDecl of
        [Located _ pair, Located _ named] -> do
          case grammarV1VariantPayload pair of
            Just (GrammarV1VariantTuple [Located _ left, Located _ right]) -> do
              assert (left == GrammarV1UnsignedType "U8") "tuple payload left type was not U8"
              assert (right == GrammarV1BoolType) "tuple payload right type was not Bool"
            other -> Left ("Pair payload was not a two-element tuple: " <> show other)
          case grammarV1VariantPayload named of
            Just (GrammarV1VariantRecord fields) ->
              assert (length fields == 2) "record payload trailing comma changed field count"
            other -> Left ("Named payload was not a two-field record: " <> show other)
        variants -> Left ("expected exactly two variants, got " <> show variants)
      other -> Left ("expected data declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show declarations)
  expectReject "data Bad = Pair(U8,);"

parse :: Text.Text -> Either String GrammarV1SourceFile
parse source = either (Left . show) Right (parseGrammarV1StructuralSource "determinacy-variant" source)

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "determinacy-variant-reject" source of
  Left _ -> Right ()
  Right value -> Left ("expected tuple trailing-comma rejection, parsed " <> show value)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
