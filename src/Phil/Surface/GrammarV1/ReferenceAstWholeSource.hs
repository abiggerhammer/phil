{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstWholeSource
  ( GrammarV1ReferenceWholeSourceError (..)
  , GrammarV1ReferenceDeclarationCore (..)
  , GrammarV1ReferenceTopLevelCore (..)
  , GrammarV1ReferenceSourceCore (..)
  , grammarV1ProductionSourceCore
  , grammarV1ReferenceSourceCore
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstArchitectureProgram
  ( GrammarV1ReferenceArchitectureProgramDeclaration (..)
  , grammarV1ProductionArchitectureProgramDeclaration
  , grammarV1ReferenceArchitectureProgramDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstCallableContract
  ( GrammarV1ReferenceCallableContractDeclaration
  , grammarV1ProductionCallableContractDeclaration
  , grammarV1ReferenceCallableContractDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstCapabilityBoundary
  ( GrammarV1ReferenceCapabilityBoundaryDeclaration (..)
  , grammarV1ProductionCapabilityBoundaryDeclaration
  , grammarV1ReferenceCapabilityBoundaryDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstFunctionComponent
  ( GrammarV1ReferenceFunctionComponentDeclaration (..)
  , grammarV1ProductionFunctionComponentDeclaration
  , grammarV1ReferenceFunctionComponentDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstProtocolDeclaration
  ( GrammarV1ReferenceProtocolDeclarationCore
  , grammarV1ProductionProtocolDeclaration
  , grammarV1ReferenceProtocolDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstProviderDeclarations
  ( GrammarV1ReferenceProviderDeclaration (..)
  , grammarV1ProductionProviderDeclaration
  , grammarV1ReferenceProviderDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstRecordData
  ( GrammarV1ReferenceRecordDataDeclaration (..)
  , grammarV1ProductionRecordDataDeclaration
  , grammarV1ReferenceRecordDataDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstSpine
  ( GrammarV1ReferenceSourceSpine (..)
  , grammarV1ProductionSourceSpine
  , grammarV1ReferenceSourceSpine
  )
import qualified Phil.Surface.GrammarV1.ReferenceAstTopLevel as Top
import Phil.Surface.GrammarV1.ReferenceAstTypeClaimDeclarations
  ( GrammarV1ReferenceTypeClaimDeclaration (..)
  , grammarV1ProductionTypeClaimDeclaration
  , grammarV1ReferenceTypeClaimDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceWholeSourceError =
  GrammarV1ReferenceWholeSourceError Text
  deriving (Eq, Show)

-- | Span-insensitive complete declaration payload. Eight grouping constructors
-- cover the exact fifteen Grammar-v1 declaration alternatives without erasing
-- which family-specific correspondence layer supplied the body.
data GrammarV1ReferenceDeclarationCore
  = GrammarV1ReferenceRecordDataCore GrammarV1ReferenceRecordDataDeclaration
  | GrammarV1ReferenceTypeClaimCore GrammarV1ReferenceTypeClaimDeclaration
  | GrammarV1ReferenceCallableContractCore GrammarV1ReferenceCallableContractDeclaration
  | GrammarV1ReferenceProviderCore GrammarV1ReferenceProviderDeclaration
  | GrammarV1ReferenceCapabilityBoundaryCore GrammarV1ReferenceCapabilityBoundaryDeclaration
  | GrammarV1ReferenceFunctionComponentCore GrammarV1ReferenceFunctionComponentDeclaration
  | GrammarV1ReferenceProtocolCore GrammarV1ReferenceProtocolDeclarationCore
  | GrammarV1ReferenceArchitectureProgramCore GrammarV1ReferenceArchitectureProgramDeclaration
  deriving (Eq, Show)

data GrammarV1ReferenceTopLevelCore = GrammarV1ReferenceTopLevelCore
  { grammarV1ReferenceWholeTopLevelAttributes :: [Top.GrammarV1ReferenceAttributeSpine]
  , grammarV1ReferenceWholeTopLevelDeclaration :: GrammarV1ReferenceDeclarationCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceSourceCore = GrammarV1ReferenceSourceCore
  { grammarV1ReferenceWholeSourceSpine :: GrammarV1ReferenceSourceSpine
  , grammarV1ReferenceWholeSourceTopLevels :: [GrammarV1ReferenceTopLevelCore]
  }
  deriving (Eq, Show)

grammarV1ProductionSourceCore
  :: GrammarV1SourceFile
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceSourceCore
grammarV1ProductionSourceCore sourceFile = do
  let topLevels = grammarV1TopLevelDecls sourceFile
      topLevelSpines = Top.grammarV1ProductionTopLevelSpines sourceFile
  if length topLevels /= length topLevelSpines
    then failWhole "production top-level spine count disagrees with production AST"
    else pure ()
  wholeTopLevels <- traverse productionTopLevel (zip topLevelSpines topLevels)
  pure GrammarV1ReferenceSourceCore
    { grammarV1ReferenceWholeSourceSpine = grammarV1ProductionSourceSpine sourceFile
    , grammarV1ReferenceWholeSourceTopLevels = wholeTopLevels
    }
  where
    productionTopLevel (spine, locatedTopLevel) = do
      declaration <- productionDeclaration
        (locatedValue (grammarV1Declaration (locatedValue locatedTopLevel)))
      requireTagAgreement
        (Top.grammarV1ReferenceTopLevelDeclarationTag spine)
        declaration
      pure GrammarV1ReferenceTopLevelCore
        { grammarV1ReferenceWholeTopLevelAttributes =
            Top.grammarV1ReferenceTopLevelAttributes spine
        , grammarV1ReferenceWholeTopLevelDeclaration = declaration
        }

productionDeclaration
  :: GrammarV1Declaration
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceDeclarationCore
productionDeclaration declaration = exactlyOne "production declaration" $
  concat
    [ wrap GrammarV1ReferenceRecordDataCore
        (grammarV1ProductionRecordDataDeclaration declaration)
    , wrap GrammarV1ReferenceTypeClaimCore
        (grammarV1ProductionTypeClaimDeclaration declaration)
    , wrap GrammarV1ReferenceCallableContractCore
        (grammarV1ProductionCallableContractDeclaration declaration)
    , wrap GrammarV1ReferenceProviderCore
        (grammarV1ProductionProviderDeclaration declaration)
    , wrap GrammarV1ReferenceCapabilityBoundaryCore
        (grammarV1ProductionCapabilityBoundaryDeclaration declaration)
    , wrap GrammarV1ReferenceFunctionComponentCore
        (grammarV1ProductionFunctionComponentDeclaration declaration)
    , wrap GrammarV1ReferenceProtocolCore
        (grammarV1ProductionProtocolDeclaration declaration)
    , wrap GrammarV1ReferenceArchitectureProgramCore
        (grammarV1ProductionArchitectureProgramDeclaration declaration)
    ]

grammarV1ReferenceSourceCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceSourceCore
grammarV1ReferenceSourceCore tree = do
  spine <- mapNested "source spine" (grammarV1ReferenceSourceSpine tree)
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  topLevelTrees <- case sourceFields of
    [_moduleTree, _importsTree, topLevelsTree] ->
      expectRepetition "source_file top levels" topLevelsTree
    _ -> failWhole "source_file body is not a three-item sequence"
  if length topLevelTrees /= grammarV1ReferenceTopLevelCount spine
    then failWhole "certified top-level count disagrees with certified source spine"
    else pure ()
  wholeTopLevels <- traverse referenceTopLevel topLevelTrees
  pure GrammarV1ReferenceSourceCore
    { grammarV1ReferenceWholeSourceSpine = spine
    , grammarV1ReferenceWholeSourceTopLevels = wholeTopLevels
    }

referenceTopLevel
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceTopLevelCore
referenceTopLevel tree = do
  spine <- mapNested "top-level spine" (Top.grammarV1ReferenceTopLevelSpine tree)
  body <- expectNonterminal "top_level_decl" tree
  fields <- expectSequence "top_level_decl" body
  declarationTree <- case fields of
    [_attributesTree, value] -> pure value
    _ -> failWhole "top_level_decl body is not a two-item sequence"
  declaration <- referenceDeclaration declarationTree
  requireTagAgreement
    (Top.grammarV1ReferenceTopLevelDeclarationTag spine)
    declaration
  pure GrammarV1ReferenceTopLevelCore
    { grammarV1ReferenceWholeTopLevelAttributes =
        Top.grammarV1ReferenceTopLevelAttributes spine
    , grammarV1ReferenceWholeTopLevelDeclaration = declaration
    }

referenceDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceDeclarationCore
referenceDeclaration tree = do
  recordData <- mapNested "record/data declaration"
    (grammarV1ReferenceRecordDataDeclaration tree)
  typeClaim <- mapNested "type/claim declaration"
    (grammarV1ReferenceTypeClaimDeclaration tree)
  callable <- mapNested "callable declaration"
    (grammarV1ReferenceCallableContractDeclaration tree)
  provider <- mapNested "provider declaration"
    (grammarV1ReferenceProviderDeclaration tree)
  capabilityBoundary <- mapNested "capability/boundary declaration"
    (grammarV1ReferenceCapabilityBoundaryDeclaration tree)
  functionComponent <- mapNested "function/component declaration"
    (grammarV1ReferenceFunctionComponentDeclaration tree)
  protocol <- mapNested "protocol declaration"
    (grammarV1ReferenceProtocolDeclaration tree)
  architectureProgram <- mapNested "architecture/program declaration"
    (grammarV1ReferenceArchitectureProgramDeclaration tree)
  exactlyOne "certified declaration" $
    concat
      [ wrap GrammarV1ReferenceRecordDataCore recordData
      , wrap GrammarV1ReferenceTypeClaimCore typeClaim
      , wrap GrammarV1ReferenceCallableContractCore callable
      , wrap GrammarV1ReferenceProviderCore provider
      , wrap GrammarV1ReferenceCapabilityBoundaryCore capabilityBoundary
      , wrap GrammarV1ReferenceFunctionComponentCore functionComponent
      , wrap GrammarV1ReferenceProtocolCore protocol
      , wrap GrammarV1ReferenceArchitectureProgramCore architectureProgram
      ]

requireTagAgreement
  :: Top.GrammarV1ReferenceDeclarationTag
  -> GrammarV1ReferenceDeclarationCore
  -> Either GrammarV1ReferenceWholeSourceError ()
requireTagAgreement expected declaration
  | declarationTag declaration == expected = pure ()
  | otherwise = failWhole
      ("top-level declaration tag disagrees with body: expected "
        <> Text.pack (show expected)
        <> ", body " <> Text.pack (show (declarationTag declaration)))

declarationTag
  :: GrammarV1ReferenceDeclarationCore
  -> Top.GrammarV1ReferenceDeclarationTag
declarationTag declaration = case declaration of
  GrammarV1ReferenceRecordDataCore value -> case value of
    GrammarV1ReferenceRecordDeclaration {} -> Top.GrammarV1ReferenceRecordDeclaration
    GrammarV1ReferenceDataDeclaration {} -> Top.GrammarV1ReferenceDataDeclaration
  GrammarV1ReferenceTypeClaimCore value -> case value of
    GrammarV1ReferenceTypeAliasDeclarationCore {} -> Top.GrammarV1ReferenceTypeAliasDeclaration
    GrammarV1ReferenceClaimDeclarationCore {} -> Top.GrammarV1ReferenceClaimDeclaration
  GrammarV1ReferenceCallableContractCore _ ->
    Top.GrammarV1ReferenceCallableContractDeclaration
  GrammarV1ReferenceProviderCore value -> case value of
    GrammarV1ReferenceProviderContractDeclaration {} ->
      Top.GrammarV1ReferenceProviderContractDeclaration
    GrammarV1ReferenceProviderImplementationDeclaration {} ->
      Top.GrammarV1ReferenceProviderImplementationDeclaration
    GrammarV1ReferenceOpaqueProviderImplementationDeclaration {} ->
      Top.GrammarV1ReferenceOpaqueProviderImplementationDeclaration
  GrammarV1ReferenceCapabilityBoundaryCore value -> case value of
    GrammarV1ReferenceCapabilityDeclaration {} -> Top.GrammarV1ReferenceCapabilityDeclaration
    GrammarV1ReferenceBoundaryDeclaration {} -> Top.GrammarV1ReferenceBoundaryDeclaration
  GrammarV1ReferenceFunctionComponentCore value -> case value of
    GrammarV1ReferenceFunctionDeclarationCore {} -> Top.GrammarV1ReferenceFunctionDeclaration
    GrammarV1ReferenceComponentDeclarationCore {} -> Top.GrammarV1ReferenceComponentDeclaration
  GrammarV1ReferenceProtocolCore _ -> Top.GrammarV1ReferenceProtocolDeclaration
  GrammarV1ReferenceArchitectureProgramCore value -> case value of
    GrammarV1ReferenceArchitectureDeclarationCore {} -> Top.GrammarV1ReferenceArchitectureDeclaration
    GrammarV1ReferenceProgramDeclarationCore {} -> Top.GrammarV1ReferenceProgramDeclaration

wrap :: (a -> b) -> Maybe a -> [b]
wrap constructor value = case value of
  Nothing -> []
  Just payload -> [constructor payload]

exactlyOne
  :: Text
  -> [a]
  -> Either GrammarV1ReferenceWholeSourceError a
exactlyOne label values = case values of
  [value] -> pure value
  [] -> failWhole (label <> " matched no declaration-family translator")
  _ -> failWhole (label <> " matched more than one declaration-family translator")

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failWhole
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failWhole ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceWholeSourceError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failWhole (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceWholeSourceError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failWhole (label <> " is not a repetition node")

mapNested
  :: Show e
  => Text
  -> Either e a
  -> Either GrammarV1ReferenceWholeSourceError a
mapNested label result = case result of
  Left errorValue -> failWhole
    (label <> " correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

failWhole :: Text -> Either GrammarV1ReferenceWholeSourceError a
failWhole = Left . GrammarV1ReferenceWholeSourceError
