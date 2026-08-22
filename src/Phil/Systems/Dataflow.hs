module Phil.Systems.Dataflow
  ( ScalarDataflowError (..)
  , verifyScalarDataflow
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Systems.IR

data ScalarDataflowError
  = ScalarDefinitionMissing Text ValueId
  | ScalarDefinitionMultiple Text ValueId [(BlockId, Int)]
  | ScalarUseBeforeDefinition Text ValueId BlockId Int BlockId Int
  deriving (Eq, Show)

data ScalarSite = ScalarSite
  { scalarSiteBlock :: BlockId
  , scalarSiteIndex :: Int
  }
  deriving (Eq, Ord, Show)

verifyScalarDataflow :: SystemsArtifact -> Either ScalarDataflowError ()
verifyScalarDataflow artifact =
  forM_ (Map.elems (systemsProgramFunctions (systemsArtifactProgram artifact))) verifyFunction

verifyFunction :: SystemsFunction -> Either ScalarDataflowError ()
verifyFunction function = do
  let functionName = systemsFunctionName function
      typedScalars = Set.fromList
        [ valueId
        | (valueId, value) <- Map.toAscList (systemsFunctionValues function)
        , TypedScalar _ <- [systemsValueRole value]
        ]
      definitions = collectDefinitions function typedScalars
      uses = collectUses function typedScalars
  forM_ (Set.toAscList typedScalars) $ \valueId ->
    case Map.findWithDefault [] valueId definitions of
      [] -> Left (ScalarDefinitionMissing functionName valueId)
      [_] -> pure ()
      sites -> Left
        (ScalarDefinitionMultiple functionName valueId
          [ (scalarSiteBlock site, scalarSiteIndex site) | site <- sites ])
  forM_ uses $ \(valueId, useSite) ->
    case Map.findWithDefault [] valueId definitions of
      [definitionSite] ->
        unless (definitionPrecedesUse function definitionSite useSite) $
          Left (ScalarUseBeforeDefinition
            functionName
            valueId
            (scalarSiteBlock definitionSite)
            (scalarSiteIndex definitionSite)
            (scalarSiteBlock useSite)
            (scalarSiteIndex useSite))
      _ -> pure ()

collectDefinitions
  :: SystemsFunction
  -> Set.Set ValueId
  -> Map.Map ValueId [ScalarSite]
collectDefinitions function typedScalars = Map.fromListWith (<>)
  [ (valueId, [ScalarSite (systemsBlockId blockValue) operationIndex])
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , (operationIndex, operation) <- zip [0 ..] (systemsBlockOps blockValue)
  , valueId <- operationDefinitions operation
  , Set.member valueId typedScalars
  ]

collectUses
  :: SystemsFunction
  -> Set.Set ValueId
  -> [(ValueId, ScalarSite)]
collectUses function typedScalars = concat
  [ operationUsesInBlock blockValue <> terminatorUsesInBlock blockValue
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  ]
  where
    operationUsesInBlock blockValue =
      [ (valueId, ScalarSite (systemsBlockId blockValue) operationIndex)
      | (operationIndex, operation) <- zip [0 ..] (systemsBlockOps blockValue)
      , valueId <- operationUses operation
      , Set.member valueId typedScalars
      ]
    terminatorUsesInBlock blockValue =
      [ (valueId, ScalarSite (systemsBlockId blockValue) (length (systemsBlockOps blockValue)))
      | valueId <- terminatorUses (systemsBlockTerminator blockValue)
      , Set.member valueId typedScalars
      ]

operationDefinitions :: SystemsOp -> [ValueId]
operationDefinitions operation = case operation of
  OpRuntimeCall { runtimeCallOutputs = outputs } -> outputs
  OpCopy { copyTarget = target } -> [target]
  OpScalarLiteral { scalarLiteralOutput = output } -> [output]
  _ -> []

operationUses :: SystemsOp -> [ValueId]
operationUses operation = case operation of
  OpRuntimeCall { runtimeCallInputs = inputs } -> inputs
  OpCopy { copySource = source } -> [source]
  _ -> []

terminatorUses :: SystemsTerminator -> [ValueId]
terminatorUses terminator = case terminator of
  TermBranch condition _ _ -> [condition]
  TermRuntimeCheck { checkInputs = inputs } -> inputs
  TermReceiveExact { exactLength = lengthValue } -> [lengthValue]
  TermReturnScalar valueId -> [valueId]
  _ -> []

definitionPrecedesUse :: SystemsFunction -> ScalarSite -> ScalarSite -> Bool
definitionPrecedesUse function definitionSite useSite
  | scalarSiteBlock definitionSite == scalarSiteBlock useSite =
      scalarSiteIndex definitionSite < scalarSiteIndex useSite
  | otherwise = blockDominates function (scalarSiteBlock definitionSite) (scalarSiteBlock useSite)

blockDominates :: SystemsFunction -> BlockId -> BlockId -> Bool
blockDominates function definitionBlock useBlock =
  not (reachableAvoiding function (Set.singleton definitionBlock) (systemsFunctionEntry function) useBlock)

reachableAvoiding
  :: SystemsFunction
  -> Set.Set BlockId
  -> BlockId
  -> BlockId
  -> Bool
reachableAvoiding function avoided start target
  | Set.member start avoided = False
  | otherwise = go Set.empty [start]
  where
    go _ [] = False
    go seen (current : rest)
      | current == target = True
      | Set.member current seen = go seen rest
      | Set.member current avoided = go seen rest
      | otherwise =
          let successors = case Map.lookup current (systemsFunctionBlocks function) of
                Nothing -> []
                Just blockValue -> blockSuccessors blockValue
          in go (Set.insert current seen) (successors <> rest)
