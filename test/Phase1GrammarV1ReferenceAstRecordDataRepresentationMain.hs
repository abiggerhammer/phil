{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer
  ( lexGrammarV1SourceTokens
  )
import Phil.Surface.GrammarV1.Parser
  ( parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceFieldCore (..)
  , GrammarV1ReferenceGenericKindCore (..)
  , GrammarV1ReferenceGenericParamCore (..)
  , GrammarV1ReferenceRequirementCore (..)
  , GrammarV1ReferenceStructuralModeCore (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstRecordData
  ( GrammarV1ReferenceRecordDataDeclaration (..)
  , GrammarV1ReferenceVariantCore (..)
  , GrammarV1ReferenceVariantPayloadCore (..)
  , grammarV1ReferenceRecordDataDeclarations
  )
import Phil.Surface.GrammarV1.ReferenceAstRecordDataRepresentationBridge
  ( grammarV1ProductionRecordDataDeclarationsToImplementation
  , grammarV1RecordDataDeclarationsToImplementation
  , grammarV1ReferenceGenericKindToImplementation
  , grammarV1ReferenceRequirementToImplementation
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( grammarV1ReferenceParseSourceTokens
  , kernelStringToText
  )
import qualified SurfaceGrammarAstRecordDataCarrierKernel as Representation
import qualified SurfaceGrammarRecognizerKernel as Recognizer
import System.Exit (exitFailure)

corpusRoot :: FilePath
corpusRoot = "test/fixtures/phase1-surface"

data CorpusCase = CorpusCase
  { corpusCaseId :: Text
  , corpusCasePath :: FilePath
  , corpusCaseExpectation :: Text
  }

data GenericKindView
  = TypeKindView
  | NatKindView
  | SessionKindView
  | MessageKindView
  | EffectsKindView
  | ProviderKindView
  | CallableKindView
  | BoundaryKindView
  | ArchitectureKindView
  deriving (Eq, Show)

data StructuralModeView
  = UnrestrictedModeView
  | AffineModeView
  | LinearModeView
  deriving (Eq, Show)

data RequirementView
  = StructuralRequirementView
  | PropositionRequirementView
  | ProviderRequirementView
  | CallableRequirementView
  | BoundaryRequirementView
  | ArchitectureRequirementView
  | EffectsRequirementView
  | AuthorityRequirementView
  | BoundaryRepresentationRequirementView
  | RepresentationRequirementView
  | PlacementRequirementView
  | CostRequirementView
  | EnvironmentRequirementView
  deriving (Eq, Show)

data VariantPayloadView
  = RecordPayloadView [Text]
  | TuplePayloadView Int
  deriving (Eq, Show)

data VariantView = VariantView Text (Maybe VariantPayloadView)
  deriving (Eq, Show)

data RecordDataView
  = RecordView
      Text
      [(Text, GenericKindView)]
      (Maybe StructuralModeView)
      [RequirementView]
      [Text]
  | DataView
      Text
      [(Text, GenericKindView)]
      (Maybe StructuralModeView)
      [RequirementView]
      [VariantView]
  deriving (Eq, Show)

main :: IO ()
main = do
  let directSources =
        [ ("empty-record", "record Empty {}")
        , ( "rich-record"
          , Text.unlines
              [ "record Pair[T: Type] mode affine requires {"
              , "  authority T;"
              , "  proposition true;"
              , "  effects E within {};"
              , "} { left: T, right: Bytes[4], }"
              ]
          )
        , ( "rich-data"
          , Text.unlines
              [ "data Packet mode linear requires { representation true; } ="
              , "  Empty{}"
              , "| Rec{tag: U8, payload: Bytes[4],}"
              , "| Tup(U8, String);"
              ]
          )
        , ( "unicode-identifiers"
          , "record Δοχείο[T: Type] {τιμή: T}"
          )
        ]
      directResults =
        [ compareSource (Text.pack label) source
        | (label, source) <- directSources
        ]
      coverageResults =
        [ genericKindCoverage
        , requirementCoverage
        ]
      directFailures = [detail | Left detail <- directResults <> coverageResults]
  mapM_ (putStrLn . ("FAIL: " <>)) directFailures
  if null directFailures then pure () else exitFailure

  input <- TextIO.getContents
  case traverse parseCaseLine (filter (not . Text.null) (Text.lines input)) of
    Left detail -> putStrLn ("FAIL: manifest stream -- " <> detail) >> exitFailure
    Right [] -> putStrLn "FAIL: manifest stream -- no corpus cases" >> exitFailure
    Right cases -> do
      results <- traverse runCase cases
      let failures = [detail | Left detail <- results]
      mapM_ (putStrLn . ("FAIL: " <>)) failures
      if null failures
        then putStrLn
          ("PASS: certified record/data production projection agrees ("
            <> show (length cases) <> " corpus fixtures)")
        else exitFailure

genericKindCoverage :: Either String ()
genericKindCoverage =
  let recursivePayload = error "recursive generic-kind payload was inspected"
      kinds =
        [ GrammarV1ReferenceTypeKindCore
        , GrammarV1ReferenceNatKindCore
        , GrammarV1ReferenceSessionKindCore
        , GrammarV1ReferenceMessageKindCore
        , GrammarV1ReferenceEffectsKindCore
        , GrammarV1ReferenceProviderKindCore recursivePayload
        , GrammarV1ReferenceCallableKindCore recursivePayload
        , GrammarV1ReferenceBoundaryKindCore recursivePayload
        , GrammarV1ReferenceArchitectureKindCore recursivePayload
        ]
      expected =
        [ TypeKindView
        , NatKindView
        , SessionKindView
        , MessageKindView
        , EffectsKindView
        , ProviderKindView
        , CallableKindView
        , BoundaryKindView
        , ArchitectureKindView
        ]
      actual = map
        (implementationGenericKindView
          . grammarV1ReferenceGenericKindToImplementation)
        kinds
  in if actual == expected
      then Right ()
      else Left
        ("generic-kind compact-carrier coverage mismatch: expected "
          <> show expected <> ", got " <> show actual)

requirementCoverage :: Either String ()
requirementCoverage =
  let recursivePayload = error "recursive requirement payload was inspected"
      requirements =
        [ GrammarV1ReferenceStructuralRequirementCore "A" "B"
        , GrammarV1ReferencePropositionRequirementCore recursivePayload
        , GrammarV1ReferenceProviderRequirementCore "P" recursivePayload
        , GrammarV1ReferenceCallableRequirementCore "C" recursivePayload
        , GrammarV1ReferenceBoundaryRequirementCore "B" recursivePayload
        , GrammarV1ReferenceArchitectureRequirementCore "A" recursivePayload
        , GrammarV1ReferenceEffectsRequirementCore "E" recursivePayload
        , GrammarV1ReferenceAuthorityRequirementCore recursivePayload
        , GrammarV1ReferenceBoundaryRepresentationRequirementCore recursivePayload
        , GrammarV1ReferenceRepresentationRequirementCore recursivePayload
        , GrammarV1ReferencePlacementRequirementCore recursivePayload
        , GrammarV1ReferenceCostRequirementCore recursivePayload
        , GrammarV1ReferenceEnvironmentRequirementCore recursivePayload
        ]
      expected =
        [ StructuralRequirementView
        , PropositionRequirementView
        , ProviderRequirementView
        , CallableRequirementView
        , BoundaryRequirementView
        , ArchitectureRequirementView
        , EffectsRequirementView
        , AuthorityRequirementView
        , BoundaryRepresentationRequirementView
        , RepresentationRequirementView
        , PlacementRequirementView
        , CostRequirementView
        , EnvironmentRequirementView
        ]
      actual = map
        (implementationRequirementView
          . grammarV1ReferenceRequirementToImplementation)
        requirements
  in if actual == expected
      then Right ()
      else Left
        ("requirement compact-carrier coverage mismatch: expected "
          <> show expected <> ", got " <> show actual)

compareSource :: Text -> Text -> Either String ()
compareSource sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  referenceTree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show
    (grammarV1ReferenceRecordDataDeclarations referenceTree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  referenceImplementation <- traverse implementationRecordDataView
    (grammarV1RecordDataDeclarationsToImplementation referenceValues)
  productionImplementation <- traverse implementationRecordDataView
    (grammarV1ProductionRecordDataDeclarationsToImplementation production)
  let expected = map referenceRecordDataView referenceValues
  if referenceImplementation /= expected
    then Left
      (Text.unpack sourceName
        <> " -- extracted certified record/data projection mismatch\nexpected: "
        <> show expected <> "\nactual: " <> show referenceImplementation)
    else if productionImplementation /= expected
      then Left
        (Text.unpack sourceName
          <> " -- production record/data projection mismatch\nexpected: "
          <> show expected <> "\nactual: " <> show productionImplementation)
      else Right ()

referenceRecordDataView
  :: GrammarV1ReferenceRecordDataDeclaration
  -> RecordDataView
referenceRecordDataView declaration = case declaration of
  GrammarV1ReferenceRecordDeclaration name params mode requirements fields ->
    RecordView
      name
      (map referenceGenericParamView params)
      (fmap referenceStructuralModeView mode)
      (map referenceRequirementView requirements)
      (map grammarV1ReferenceFieldNameCore fields)
  GrammarV1ReferenceDataDeclaration name params mode requirements variants ->
    DataView
      name
      (map referenceGenericParamView params)
      (fmap referenceStructuralModeView mode)
      (map referenceRequirementView requirements)
      (map referenceVariantView variants)

referenceGenericParamView
  :: GrammarV1ReferenceGenericParamCore
  -> (Text, GenericKindView)
referenceGenericParamView parameter =
  ( grammarV1ReferenceGenericParamNameCore parameter
  , referenceGenericKindView (grammarV1ReferenceGenericParamKindCore parameter)
  )

referenceGenericKindView :: GrammarV1ReferenceGenericKindCore -> GenericKindView
referenceGenericKindView kind = case kind of
  GrammarV1ReferenceTypeKindCore -> TypeKindView
  GrammarV1ReferenceNatKindCore -> NatKindView
  GrammarV1ReferenceSessionKindCore -> SessionKindView
  GrammarV1ReferenceMessageKindCore -> MessageKindView
  GrammarV1ReferenceEffectsKindCore -> EffectsKindView
  GrammarV1ReferenceProviderKindCore _ -> ProviderKindView
  GrammarV1ReferenceCallableKindCore _ -> CallableKindView
  GrammarV1ReferenceBoundaryKindCore _ -> BoundaryKindView
  GrammarV1ReferenceArchitectureKindCore _ -> ArchitectureKindView

referenceStructuralModeView
  :: GrammarV1ReferenceStructuralModeCore
  -> StructuralModeView
referenceStructuralModeView mode = case mode of
  GrammarV1ReferenceUnrestrictedMode -> UnrestrictedModeView
  GrammarV1ReferenceAffineMode -> AffineModeView
  GrammarV1ReferenceLinearMode -> LinearModeView

referenceRequirementView :: GrammarV1ReferenceRequirementCore -> RequirementView
referenceRequirementView requirement = case requirement of
  GrammarV1ReferenceStructuralRequirementCore _ _ -> StructuralRequirementView
  GrammarV1ReferencePropositionRequirementCore _ -> PropositionRequirementView
  GrammarV1ReferenceProviderRequirementCore _ _ -> ProviderRequirementView
  GrammarV1ReferenceCallableRequirementCore _ _ -> CallableRequirementView
  GrammarV1ReferenceBoundaryRequirementCore _ _ -> BoundaryRequirementView
  GrammarV1ReferenceArchitectureRequirementCore _ _ -> ArchitectureRequirementView
  GrammarV1ReferenceEffectsRequirementCore _ _ -> EffectsRequirementView
  GrammarV1ReferenceAuthorityRequirementCore _ -> AuthorityRequirementView
  GrammarV1ReferenceBoundaryRepresentationRequirementCore _ ->
    BoundaryRepresentationRequirementView
  GrammarV1ReferenceRepresentationRequirementCore _ -> RepresentationRequirementView
  GrammarV1ReferencePlacementRequirementCore _ -> PlacementRequirementView
  GrammarV1ReferenceCostRequirementCore _ -> CostRequirementView
  GrammarV1ReferenceEnvironmentRequirementCore _ -> EnvironmentRequirementView

referenceVariantView :: GrammarV1ReferenceVariantCore -> VariantView
referenceVariantView variant = VariantView
  (grammarV1ReferenceVariantNameCore variant)
  (fmap referenceVariantPayloadView (grammarV1ReferenceVariantPayloadCore variant))

referenceVariantPayloadView
  :: GrammarV1ReferenceVariantPayloadCore
  -> VariantPayloadView
referenceVariantPayloadView payload = case payload of
  GrammarV1ReferenceVariantRecordCore fields ->
    RecordPayloadView (map grammarV1ReferenceFieldNameCore fields)
  GrammarV1ReferenceVariantTupleCore types ->
    TuplePayloadView (length types)

implementationRecordDataView
  :: Representation.Phase1SurfaceProductionRecordDataDeclaration
  -> Either String RecordDataView
implementationRecordDataView declaration = case declaration of
  Representation.Phase1ProductionRecordDeclaration
      name params mode requirements fields ->
    RecordView
      <$> decodeRepresentationString name
      <*> traverse implementationGenericParamView params
      <*> pure (fmap implementationStructuralModeView mode)
      <*> pure (map implementationRequirementView requirements)
      <*> traverse decodeRepresentationString fields
  Representation.Phase1ProductionDataDeclaration
      name params mode requirements variants ->
    DataView
      <$> decodeRepresentationString name
      <*> traverse implementationGenericParamView params
      <*> pure (fmap implementationStructuralModeView mode)
      <*> pure (map implementationRequirementView requirements)
      <*> traverse implementationVariantView variants

implementationGenericParamView
  :: Representation.Phase1SurfaceProductionGenericParam
  -> Either String (Text, GenericKindView)
implementationGenericParamView parameter = case parameter of
  Representation.Build_Phase1SurfaceProductionGenericParam name kind ->
    (,) <$> decodeRepresentationString name <*> pure (implementationGenericKindView kind)

implementationGenericKindView
  :: Representation.Phase1SurfaceProductionGenericKind
  -> GenericKindView
implementationGenericKindView kind = case kind of
  Representation.Phase1ProductionTypeGenericKind -> TypeKindView
  Representation.Phase1ProductionNatGenericKind -> NatKindView
  Representation.Phase1ProductionSessionGenericKind -> SessionKindView
  Representation.Phase1ProductionMessageGenericKind -> MessageKindView
  Representation.Phase1ProductionEffectsGenericKind -> EffectsKindView
  Representation.Phase1ProductionProviderGenericKind -> ProviderKindView
  Representation.Phase1ProductionCallableGenericKind -> CallableKindView
  Representation.Phase1ProductionBoundaryGenericKind -> BoundaryKindView
  Representation.Phase1ProductionArchitectureGenericKind -> ArchitectureKindView

implementationStructuralModeView
  :: Representation.Phase1SurfaceProductionStructuralMode
  -> StructuralModeView
implementationStructuralModeView mode = case mode of
  Representation.Phase1ProductionUnrestrictedMode -> UnrestrictedModeView
  Representation.Phase1ProductionAffineMode -> AffineModeView
  Representation.Phase1ProductionLinearMode -> LinearModeView

implementationRequirementView
  :: Representation.Phase1SurfaceProductionRequirement
  -> RequirementView
implementationRequirementView requirement = case requirement of
  Representation.Phase1ProductionStructuralRequirement -> StructuralRequirementView
  Representation.Phase1ProductionPropositionRequirement -> PropositionRequirementView
  Representation.Phase1ProductionProviderRequirement -> ProviderRequirementView
  Representation.Phase1ProductionCallableRequirement -> CallableRequirementView
  Representation.Phase1ProductionBoundaryRequirement -> BoundaryRequirementView
  Representation.Phase1ProductionArchitectureRequirement -> ArchitectureRequirementView
  Representation.Phase1ProductionEffectsRequirement -> EffectsRequirementView
  Representation.Phase1ProductionAuthorityRequirement -> AuthorityRequirementView
  Representation.Phase1ProductionBoundaryRepresentationRequirement ->
    BoundaryRepresentationRequirementView
  Representation.Phase1ProductionRepresentationRequirement -> RepresentationRequirementView
  Representation.Phase1ProductionPlacementRequirement -> PlacementRequirementView
  Representation.Phase1ProductionCostRequirement -> CostRequirementView
  Representation.Phase1ProductionEnvironmentRequirement -> EnvironmentRequirementView

implementationVariantView
  :: Representation.Phase1SurfaceProductionVariant
  -> Either String VariantView
implementationVariantView variant = case variant of
  Representation.Build_Phase1SurfaceProductionVariant name payload ->
    VariantView
      <$> decodeRepresentationString name
      <*> traverse implementationVariantPayloadView payload

implementationVariantPayloadView
  :: Representation.Phase1SurfaceProductionVariantPayload
  -> Either String VariantPayloadView
implementationVariantPayloadView payload = case payload of
  Representation.Phase1ProductionRecordPayload fields ->
    RecordPayloadView <$> traverse decodeRepresentationString fields
  Representation.Phase1ProductionTuplePayload types ->
    pure (TuplePayloadView (length types))

decodeRepresentationString
  :: Representation.String
  -> Either String Text
decodeRepresentationString =
  mapLeft show
    . kernelStringToText
    . representationStringToRecognizer

representationStringToRecognizer
  :: Representation.String
  -> Recognizer.String
representationStringToRecognizer value = case value of
  Representation.EmptyString -> Recognizer.EmptyString
  Representation.String0 ascii rest ->
    Recognizer.String0
      (representationAsciiToRecognizer ascii)
      (representationStringToRecognizer rest)

representationAsciiToRecognizer
  :: Representation.Ascii0
  -> Recognizer.Ascii0
representationAsciiToRecognizer ascii = case ascii of
  Representation.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 ->
    Recognizer.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7

parseCaseLine :: Text -> Either String CorpusCase
parseCaseLine line = case Text.splitOn "\t" line of
  [fixtureId, path, expectation]
    | not (Text.null fixtureId)
    , not (Text.null path)
    , expectation == "parse" || expectation == "reject-syntax" ->
        Right CorpusCase
          { corpusCaseId = fixtureId
          , corpusCasePath = Text.unpack path
          , corpusCaseExpectation = expectation
          }
  _ -> Left ("invalid TSV row " <> show line)

runCase :: CorpusCase -> IO (Either String ())
runCase corpusCase
  | corpusCaseExpectation corpusCase == "reject-syntax" = pure (Right ())
  | otherwise = do
      let relativePath = corpusCasePath corpusCase
          path = corpusRoot <> "/" <> relativePath
          sourceName = Text.pack relativePath
          label = Text.unpack (corpusCaseId corpusCase) <> " " <> relativePath
      sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
      pure $ case sourceResult of
        Left exception -> Left
          (label <> " -- unable to read fixture: " <> show exception)
        Right source -> mapLeft ((label <> " -- ") <>) (compareSource sourceName source)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
