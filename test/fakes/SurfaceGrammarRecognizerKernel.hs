module SurfaceGrammarRecognizerKernel where

import qualified Prelude

data Ascii0 =
  Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool
        Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool

data String =
    EmptyString
  | String0 Ascii0 String

data Nat =
    O
  | S Nat

data ConcreteToken =
    TLiteral String
  | TLexical String String

data ParseTree =
    PTLiteral String
  | PTLexical String String
  | PTNonterminal String ParseTree
  | PTSequence [ParseTree]
  | PTAlternative Nat ParseTree
  | PTOptionalNone
  | PTOptionalSome ParseTree
  | PTRepetition [ParseTree]

data DerivationResult =
    ResultTree ParseTree
  | ResultTrees [ParseTree]

phase1_surface_reference_parse
  :: [ConcreteToken]
  -> Prelude.Maybe ([ConcreteToken], DerivationResult)
phase1_surface_reference_parse _ = Prelude.Nothing

phase1_surface_reference_accepts :: [ConcreteToken] -> Prelude.Bool
phase1_surface_reference_accepts _ = Prelude.False
