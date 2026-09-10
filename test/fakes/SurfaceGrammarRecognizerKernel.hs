module SurfaceGrammarRecognizerKernel where

import qualified Prelude

data Ascii0 =
  Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool
        Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool

data String =
    EmptyString
  | String0 Ascii0 String

data ConcreteToken =
    TLiteral String
  | TLexical String String

phase1_surface_reference_accepts :: [ConcreteToken] -> Prelude.Bool
phase1_surface_reference_accepts _ = Prelude.False
