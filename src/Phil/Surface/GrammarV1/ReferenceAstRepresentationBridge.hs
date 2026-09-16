{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstRepresentationBridge
  ( grammarV1ReferenceSourceSpineToImplementationHeader
  , grammarV1ProductionSourceFileToImplementationHeader
  ) where

import Data.Text (Text)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1QualifiedName (..)
  , GrammarV1SourceFile
  )
import Phil.Surface.GrammarV1.ReferenceAstSpine
  ( GrammarV1ReferenceAstSpineError (..)
  , GrammarV1ReferenceImportSpine (..)
  , GrammarV1ReferenceSourceSpine (..)
  , grammarV1ProductionSourceSpine
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( textToKernelString
  )
import qualified SurfaceGrammarAstRepresentationKernel as Representation
import qualified SurfaceGrammarRecognizerKernel as Recognizer

-- | Bind the stable production/reference source spine to the exact
-- implementation-facing source-header carrier extracted from
-- GrammarAstImplementationRepresentationExtraction.v.
--
-- The extracted carrier intentionally contains only the already-refined
-- module/import header and top-level count.  It does not fabricate or claim a
-- refinement for the still-separate top-level ParseTree payloads.
grammarV1ReferenceSourceSpineToImplementationHeader
  :: GrammarV1ReferenceSourceSpine
  -> Either
      GrammarV1ReferenceAstSpineError
      Representation.Phase1SurfaceImplementationSourceHeader
grammarV1ReferenceSourceSpineToImplementationHeader spine = do
  topLevelCount <- intToRepresentationNat
    (grammarV1ReferenceTopLevelCount spine)
  pure
    (Representation.Build_Phase1SurfaceImplementationSourceHeader
      (fmap qualifiedNameToRepresentation
        (grammarV1ReferenceModuleName spine))
      (map importSpineToRepresentation
        (grammarV1ReferenceImports spine))
      topLevelCount)

-- | Production binding for the same extracted header carrier.  Going through
-- 'grammarV1ProductionSourceSpine' makes the equality boundary explicit: the
-- extracted representation is bound to exactly the span-insensitive source
-- fields already shared by certified and production parsing.
grammarV1ProductionSourceFileToImplementationHeader
  :: GrammarV1SourceFile
  -> Either
      GrammarV1ReferenceAstSpineError
      Representation.Phase1SurfaceImplementationSourceHeader
grammarV1ProductionSourceFileToImplementationHeader =
  grammarV1ReferenceSourceSpineToImplementationHeader
    . grammarV1ProductionSourceSpine

importSpineToRepresentation
  :: GrammarV1ReferenceImportSpine
  -> Representation.Phase1SurfaceImplementationImportHeader
importSpineToRepresentation importSpine =
  Representation.Build_Phase1SurfaceImplementationImportHeader
    (qualifiedNameToRepresentation
      (grammarV1ReferenceImportName importSpine))
    (fmap (map textToRepresentationString)
      (grammarV1ReferenceImportSelection importSpine))

qualifiedNameToRepresentation
  :: GrammarV1QualifiedName
  -> [Representation.String]
qualifiedNameToRepresentation (GrammarV1QualifiedName parts) =
  map textToRepresentationString parts

-- | Reuse the repository's existing explicit UTF-8 Text -> Rocq String bridge,
-- then change only the nominal extracted String carrier.  This deliberately
-- avoids introducing a second text-encoding convention at the representation
-- boundary.
textToRepresentationString :: Text -> Representation.String
textToRepresentationString =
  recognizerStringToRepresentation . textToKernelString

recognizerStringToRepresentation
  :: Recognizer.String
  -> Representation.String
recognizerStringToRepresentation value = case value of
  Recognizer.EmptyString -> Representation.EmptyString
  Recognizer.String0 ascii rest ->
    Representation.String0
      (recognizerAsciiToRepresentation ascii)
      (recognizerStringToRepresentation rest)

recognizerAsciiToRepresentation
  :: Recognizer.Ascii0
  -> Representation.Ascii0
recognizerAsciiToRepresentation ascii = case ascii of
  Recognizer.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 ->
    Representation.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7

intToRepresentationNat
  :: Int
  -> Either GrammarV1ReferenceAstSpineError Representation.Nat
intToRepresentationNat value
  | value < 0 =
      Left
        (GrammarV1ReferenceAstSpineError
          "source spine has a negative top-level count")
  | otherwise = Right (go value)
  where
    go 0 = Representation.O
    go n = Representation.S (go (n - 1))
