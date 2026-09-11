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
  ( GrammarV1ReferenceArchitectureProgramDeclaration
  , grammarV1ProductionArchitectureProgramDeclaration
  , grammarV1ReferenceArchitectureProgramDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstCallableContract
  ( GrammarV1ReferenceCallableContractDeclaration
  , grammarV1ProductionCallableContractDeclaration
  , grammarV1ReferenceCallableContractDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstCapabilityBoundary
  ( GrammarV1ReferenceCapabilityBoundaryDeclaration
  , grammarV1ProductionCapabilityBoundaryDeclaration
  , grammarV1ReferenceCapabilityBoundaryDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstFunctionComponent
  ( GrammarV1ReferenceFunctionComponentDeclaration
  , grammarV1ProductionFunctionComponentDeclaration
  , grammarV1ReferenceFunctionComponentDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstProtocolDeclaration
  ( GrammarV1ReferenceProtocolDeclarationCore
  , grammarV1ProductionProtocolDeclaration
  , grammarV1ReferenceProtocolDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstProviderDeclarations
  ( GrammarV1ReferenceProviderDeclaration
  , grammarV1ProductionProviderDeclaration
  , grammarV1ReferenceProviderDeclaration
  )
import Phil.Surface.GrammarV1.ReferenceAstRecordData
  ( GrammarV1ReferenceRecordDataDeclaration
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
  ( GrammarV1ReferenceTypeClaimDeclaration
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

-- | Span-insensitive complete declaration payload.  There is one constructor
-- for each exact Grammar-v1 declaration alternative.  Family-specific payload
-- types are deliberately reused rather than reinterpreted here.
data GrammarV1ReferenceDeclarationCore
  = GrammarV1ReferenceWholeRecord GrammarV1ReferenceRecordDataDeclaration
  | GrammarV1ReferenceWholeData GrammarV1ReferenceRecordDataDeclaration
  | GrammarV1ReferenceWholeTypeAlias GrammarV1ReferenceTypeClaimDeclaration
  | GrammarV1ReferenceWholeClaim GrammarV1ReferenceTypeClaimDeclaration
  | GrammarV1ReferenceWholeCallableContract GrammarV1ReferenceCallableContractDeclaration
  | GrammarV1ReferenceWholeFunction GrammarV1ReferenceFunctionComponentDeclaration
  | GrammarV1ReferenceWholeProviderContract GrammarV1ReferenceProviderDeclaration
  | GrammarV1ReferenceWholeProviderImplementation GrammarV1ReferenceProviderDeclaration
  | GrammarV1ReferenceWholeOpaqueProviderImplementation GrammarV1ReferenceProviderDeclaration
  | GrammarV1ReferenceWholeProtocol GrammarV1ReferenceProtocolDeclarationCore
  | GrammarV1ReferenceWholeCapability GrammarV1ReferenceCapabilityBoundaryDeclaration
  | GrammarV1ReferenceWholeBoundary GrammarV1ReferenceCapabilityBoundaryDeclaration
  | GrammarV1ReferenceWholeArchitecture GrammarV1ReferenceArchitectureProgramDeclaration
  | GrammarV1ReferenceWholeComponent GrammarV1ReferenceFunctionComponentDeclaration
  | GrammarV1ReferenceWholeProgram GrammarV1ReferenceArchitectureProgramDeclaration
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
      let tag = Top.grammarV1ReferenceTopLevelDeclarationTag spine
          declaration = locatedValue
            (grammarV1Declaration (locatedValue locatedTopLevel))
      body <- productionDeclaration tag declaration
      pure GrammarV1ReferenceTopLevelCore
        { grammarV1ReferenceWholeTopLevelAttributes =
            Top.grammarV1ReferenceTopLevelAttributes spine
        , grammarV1ReferenceWholeTopLevelDeclaration = body
        }

productionDeclaration
  :: Top.GrammarV1ReferenceDeclarationTag
  -> GrammarV1Declaration
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceDeclarationCore
productionDeclaration tag declaration = case tag of
  Top.GrammarV1ReferenceRecordDeclaration ->
    requireProduction "record" GrammarV1ReferenceWholeRecord
      (grammarV1ProductionRecordDataDeclaration declaration)
  Top.GrammarV1ReferenceDataDeclaration ->
    requireProduction "data" GrammarV1ReferenceWholeData
      (grammarV1ProductionRecordDataDeclaration declaration)
  Top.GrammarV1ReferenceTypeAliasDeclaration ->
    requireProduction "type alias" GrammarV1ReferenceWholeTypeAlias
      (grammarV1ProductionTypeClaimDeclaration declaration)
  Top.GrammarV1ReferenceClaimDeclaration ->
    requireProduction "claim" GrammarV1ReferenceWholeClaim
      (grammarV1ProductionTypeClaimDeclaration declaration)
  Top.GrammarV1ReferenceCallableContractDeclaration ->
    requireProduction "callable contract" GrammarV1ReferenceWholeCallableContract
      (grammarV1ProductionCallableContractDeclaration declaration)
  Top.GrammarV1ReferenceFunctionDeclaration ->
    requireProduction "function" GrammarV1ReferenceWholeFunction
      (grammarV1ProductionFunctionComponentDeclaration declaration)
  Top.GrammarV1ReferenceProviderContractDeclaration ->
    requireProduction "provider contract" GrammarV1ReferenceWholeProviderContract
      (grammarV1ProductionProviderDeclaration declaration)
  Top.GrammarV1ReferenceProviderImplementationDeclaration ->
    requireProduction "provider implementation" GrammarV1ReferenceWholeProviderImplementation
      (grammarV1ProductionProviderDeclaration declaration)
  Top.GrammarV1ReferenceOpaqueProviderImplementationDeclaration ->
    requireProduction "opaque provider implementation"
      GrammarV1ReferenceWholeOpaqueProviderImplementation
      (grammarV1ProductionProviderDeclaration declaration)
  Top.GrammarV1ReferenceProtocolDeclaration ->
    requireProduction "protocol" GrammarV1ReferenceWholeProtocol
      (grammarV1ProductionProtocolDeclaration declaration)
  Top.GrammarV1ReferenceCapabilityDeclaration ->
    requireProduction "capability" GrammarV1ReferenceWholeCapability
      (grammarV1ProductionCapabilityBoundaryDeclaration declaration)
  Top.GrammarV1ReferenceBoundaryDeclaration ->
    requireProduction "boundary" GrammarV1ReferenceWholeBoundary
      (grammarV1ProductionCapabilityBoundaryDeclaration declaration)
  Top.GrammarV1ReferenceArchitectureDeclaration ->
    requireProduction "architecture" GrammarV1ReferenceWholeArchitecture
      (grammarV1ProductionArchitectureProgramDeclaration declaration)
  Top.GrammarV1ReferenceComponentDeclaration ->
    requireProduction "component" GrammarV1ReferenceWholeComponent
      (grammarV1ProductionFunctionComponentDeclaration declaration)
  Top.GrammarV1ReferenceProgramDeclaration ->
    requireProduction "program" GrammarV1ReferenceWholeProgram
      (grammarV1ProductionArchitectureProgramDeclaration declaration)

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
  let tag = Top.grammarV1ReferenceTopLevelDeclarationTag spine
  declaration <- referenceDeclaration tag declarationTree
  pure GrammarV1ReferenceTopLevelCore
    { grammarV1ReferenceWholeTopLevelAttributes =
        Top.grammarV1ReferenceTopLevelAttributes spine
    , grammarV1ReferenceWholeTopLevelDeclaration = declaration
    }

referenceDeclaration
  :: Top.GrammarV1ReferenceDeclarationTag
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceDeclarationCore
referenceDeclaration tag tree = case tag of
  Top.GrammarV1ReferenceRecordDeclaration ->
    requireReference "record" GrammarV1ReferenceWholeRecord
      (grammarV1ReferenceRecordDataDeclaration tree)
  Top.GrammarV1ReferenceDataDeclaration ->
    requireReference "data" GrammarV1ReferenceWholeData
      (grammarV1ReferenceRecordDataDeclaration tree)
  Top.GrammarV1ReferenceTypeAliasDeclaration ->
    requireReference "type alias" GrammarV1ReferenceWholeTypeAlias
      (grammarV1ReferenceTypeClaimDeclaration tree)
  Top.GrammarV1ReferenceClaimDeclaration ->
    requireReference "claim" GrammarV1ReferenceWholeClaim
      (grammarV1ReferenceTypeClaimDeclaration tree)
  Top.GrammarV1ReferenceCallableContractDeclaration ->
    requireReference "callable contract" GrammarV1ReferenceWholeCallableContract
      (grammarV1ReferenceCallableContractDeclaration tree)
  Top.GrammarV1ReferenceFunctionDeclaration ->
    requireReference "function" GrammarV1ReferenceWholeFunction
      (grammarV1ReferenceFunctionComponentDeclaration tree)
  Top.GrammarV1ReferenceProviderContractDeclaration ->
    requireReference "provider contract" GrammarV1ReferenceWholeProviderContract
      (grammarV1ReferenceProviderDeclaration tree)
  Top.GrammarV1ReferenceProviderImplementationDeclaration ->
    requireReference "provider implementation" GrammarV1ReferenceWholeProviderImplementation
      (grammarV1ReferenceProviderDeclaration tree)
  Top.GrammarV1ReferenceOpaqueProviderImplementationDeclaration ->
    requireReference "opaque provider implementation"
      GrammarV1ReferenceWholeOpaqueProviderImplementation
      (grammarV1ReferenceProviderDeclaration tree)
  Top.GrammarV1ReferenceProtocolDeclaration ->
    requireReference "protocol" GrammarV1ReferenceWholeProtocol
      (grammarV1ReferenceProtocolDeclaration tree)
  Top.GrammarV1ReferenceCapabilityDeclaration ->
    requireReference "capability" GrammarV1ReferenceWholeCapability
      (grammarV1ReferenceCapabilityBoundaryDeclaration tree)
  Top.GrammarV1ReferenceBoundaryDeclaration ->
    requireReference "boundary" GrammarV1ReferenceWholeBoundary
      (grammarV1ReferenceCapabilityBoundaryDeclaration tree)
  Top.GrammarV1ReferenceArchitectureDeclaration ->
    requireReference "architecture" GrammarV1ReferenceWholeArchitecture
      (grammarV1ReferenceArchitectureProgramDeclaration tree)
  Top.GrammarV1ReferenceComponentDeclaration ->
    requireReference "component" GrammarV1ReferenceWholeComponent
      (grammarV1ReferenceFunctionComponentDeclaration tree)
  Top.GrammarV1ReferenceProgramDeclaration ->
    requireReference "program" GrammarV1ReferenceWholeProgram
      (grammarV1ReferenceArchitectureProgramDeclaration tree)

requireProduction
  :: Text
  -> (a -> GrammarV1ReferenceDeclarationCore)
  -> Maybe a
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceDeclarationCore
requireProduction label constructor value = case value of
  Just payload -> pure (constructor payload)
  Nothing -> failWhole
    ("production top-level tag selected " <> label
      <> " but its declaration translator rejected the body")

requireReference
  :: Show e
  => Text
  -> (a -> GrammarV1ReferenceDeclarationCore)
  -> Either e (Maybe a)
  -> Either GrammarV1ReferenceWholeSourceError GrammarV1ReferenceDeclarationCore
requireReference label constructor result = do
  value <- mapNested (label <> " declaration") result
  case value of
    Just payload -> pure (constructor payload)
    Nothing -> failWhole
      ("certified top-level tag selected " <> label
        <> " but its declaration translator rejected the body")

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
