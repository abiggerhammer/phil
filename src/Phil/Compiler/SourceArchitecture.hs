{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.SourceArchitecture
  ( SourceArchitectureRootMap
  , CheckedSourceArchitecture (..)
  , SourceArchitectureError (..)
  , buildCheckedSourceArchitecture
  , sourceComponentInterfaceSemantics
  , sourceComponentDefinitionSemantics
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.SourceBundle
  ( CheckedSourceBundle (..)
  , CheckedSourceUnit (..)
  )
import Phil.Core.Static
  ( ArchitectureInstanceGraph
  , ArchitectureInstantiationError
  , ArchitectureNodeSpec (..)
  , CheckedArchitectureInstance
  , DeclarationDescriptor (..)
  , DeclarationIdentity
  , DeclarationPresentation (..)
  , InstanceKey
  , SemanticForm (..)
  , deriveDeclarationIdentity
  , instantiateArchitecture
  , lookupArchitectureInstance
  )
import Phil.Surface.Lineage
  ( InstanceLineageSiteId
  , ResolvedSourceBundleLineage (..)
  )
import Phil.Surface.Syntax

-- | Explicit selected-root binding from portable root name to persisted
-- instance-lineage site.  The compiler never derives an InstanceKey from a
-- witness name, file name, component display name, or source position.
type SourceArchitectureRootMap = Map Text InstanceLineageSiteId

-- | Exact checked Architecture occurrence derived from one already checked
-- ordinary-source bundle.  The declaration key and instance key come from
-- persisted SourceBundle lineage; presentation stays outside semantic identity.
data CheckedSourceArchitecture = CheckedSourceArchitecture
  { checkedSourceArchitectureBundle :: CheckedSourceBundle
  , checkedSourceArchitectureDeclaration :: DeclarationIdentity
  , checkedSourceArchitectureInstanceKey :: InstanceKey
  , checkedSourceArchitectureGraph :: ArchitectureInstanceGraph
  , checkedSourceArchitectureRoot :: CheckedArchitectureInstance
  }
  deriving (Eq, Show)

data SourceArchitectureError
  = SourceArchitectureRootBindingMissing Text
  | SourceArchitectureInstanceLineageMissing InstanceLineageSiteId
  | SourceArchitectureRootUnitMissing
  | SourceArchitectureInstantiationError ArchitectureInstantiationError
  | SourceArchitectureRootInstanceMissing InstanceKey
  deriving (Eq, Show)

-- | Bind the selected checked source declaration to one exact architecture
-- occurrence.  Interface and definition revisions are derived from a canonical,
-- span-free semantic projection of the parsed source.  Carrier whitespace,
-- comments, SourceUnitId, paths, and component presentation names are absent.
buildCheckedSourceArchitecture
  :: SourceArchitectureRootMap
  -> CheckedSourceBundle
  -> Either SourceArchitectureError CheckedSourceArchitecture
buildCheckedSourceArchitecture rootInstances checkedBundle = do
  let rootName = checkedSourceSelectedRoot checkedBundle
      rootDeclarationKey = checkedSourceSelectedRootKey checkedBundle
      lineage = checkedSourceLineage checkedBundle
  instanceSite <- maybe
    (Left (SourceArchitectureRootBindingMissing rootName))
    Right
    (Map.lookup rootName rootInstances)
  instanceKey <- maybe
    (Left (SourceArchitectureInstanceLineageMissing instanceSite))
    Right
    (Map.lookup instanceSite (resolvedInstanceKeys lineage))
  sourceUnit <- maybe
    (Left SourceArchitectureRootUnitMissing)
    Right
    (selectedUnit rootDeclarationKey (checkedSourceUnits checkedBundle))
  let component = locatedValue (checkedSourceComponent sourceUnit)
      declaration = deriveDeclarationIdentity DeclarationDescriptor
        { declarationPresentation = DeclarationPresentation
            { declarationDisplayName = componentName component
            , declarationModulePath = []
            }
        , declarationKey = rootDeclarationKey
        , declarationInterfaceSemantics = sourceComponentInterfaceSemantics component
        , declarationDefinitionSemantics = sourceComponentDefinitionSemantics component
        }
      node = ArchitectureNodeSpec
        { architectureNodeDeclaration = declaration
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren = []
        , architectureNodeReferences = []
        }
  graph <- mapLeft SourceArchitectureInstantiationError
    (instantiateArchitecture instanceKey node)
  root <- maybe
    (Left (SourceArchitectureRootInstanceMissing instanceKey))
    Right
    (lookupArchitectureInstance instanceKey graph)
  Right CheckedSourceArchitecture
    { checkedSourceArchitectureBundle = checkedBundle
    , checkedSourceArchitectureDeclaration = declaration
    , checkedSourceArchitectureInstanceKey = instanceKey
    , checkedSourceArchitectureGraph = graph
    , checkedSourceArchitectureRoot = root
    }
  where
    selectedUnit key = go
      where
        go [] = Nothing
        go (unit : rest)
          | checkedSourceDeclarationKey unit == key = Just unit
          | otherwise = go rest

-- | Public source contract semantics.  The component's display name is
-- intentionally excluded; parameter names/types and provides type remain part
-- of the checked public contract in the current Phase 1 surface.
sourceComponentInterfaceSemantics :: Component -> SemanticForm
sourceComponentInterfaceSemantics component = semanticRecord
  [ ("parameters", SemanticOrdered
      (map (parameterSemantics . locatedValue) (componentParameters component)))
  , ("provides", semanticMaybe (typeSemantics . locatedValue)
      (componentProvides component))
  ]

-- | Checked body semantics with all SourceSpan/SourcePoint presentation erased.
sourceComponentDefinitionSemantics :: Component -> SemanticForm
sourceComponentDefinitionSemantics = blockSemantics . locatedValue . componentBody

parameterSemantics :: Parameter -> SemanticForm
parameterSemantics parameter = semanticRecord
  [ ("name", atom (parameterName parameter))
  , ("type", semanticMaybe (typeSemantics . locatedValue) (parameterType parameter))
  ]

blockSemantics :: Block -> SemanticForm
blockSemantics block = SemanticOrdered
  (map (statementSemantics . locatedValue) (blockStatements block))

statementSemantics :: Statement -> SemanticForm
statementSemantics statement = case statement of
  LetStatement patternValue expression -> tagged "let"
    [ patternSemantics (locatedValue patternValue)
    , expressionSemantics (locatedValue expression)
    ]
  ReturnStatement expression -> tagged "return"
    [expressionSemantics (locatedValue expression)]
  ExpressionStatement expression -> tagged "expression"
    [expressionSemantics (locatedValue expression)]

patternSemantics :: Pattern -> SemanticForm
patternSemantics patternValue = case patternValue of
  BindPattern name -> tagged "bind" [atom name]
  TuplePattern patterns -> tagged "tuple-pattern"
    [SemanticOrdered (map (patternSemantics . locatedValue) patterns)]

typeSemantics :: SurfaceType -> SemanticForm
typeSemantics surfaceType = case surfaceType of
  SurfaceUnitType -> tagged "Unit" []
  SurfaceBoolType -> tagged "Bool" []
  SurfaceUIntType width -> tagged "UInt" [integerAtom (toInteger width)]
  SurfaceBytesType index -> tagged "Bytes"
    [expressionSemantics (locatedValue index)]
  SurfaceFrameType grammar -> tagged "Frame" [atom grammar]
  SurfaceProofType proposition -> tagged "Proof"
    [propositionSemantics (locatedValue proposition)]
  SurfaceValidatedType claim context subject -> tagged "Validated"
    [ atom claim
    , expressionSemantics (locatedValue context)
    , expressionSemantics (locatedValue subject)
    ]
  SurfaceNamedType name arguments -> tagged "named-type"
    [ atom name
    , SemanticOrdered (map (expressionSemantics . locatedValue) arguments)
    ]

expressionSemantics :: SurfaceExpression -> SemanticForm
expressionSemantics expression = case expression of
  VariableExpression name -> tagged "variable" [atom name]
  IntegerExpression value -> tagged "integer" [integerAtom value]
  BooleanExpression value -> tagged "boolean" [atom (if value then "true" else "false")]
  UnitExpression -> tagged "unit" []
  TupleExpression values -> tagged "tuple"
    [SemanticOrdered (map (expressionSemantics . locatedValue) values)]
  CallExpression name arguments -> tagged "call"
    [ atom name
    , SemanticOrdered (map (expressionSemantics . locatedValue) arguments)
    ]
  FieldExpression base field -> tagged "field"
    [expressionSemantics (locatedValue base), atom field]
  BinaryExpression operation left right -> tagged "binary"
    [ atom (binaryOperatorText operation)
    , expressionSemantics (locatedValue left)
    , expressionSemantics (locatedValue right)
    ]
  ConstructExpression constructor fields -> tagged "construct"
    [ atom constructor
    , SemanticOrdered
        [ semanticRecord
            [ ("field", atom field)
            , ("value", expressionSemantics (locatedValue value))
            ]
        | (field, value) <- fields
        ]
    ]
  ReceiveExpression messageType endpoint -> tagged "receive"
    [ typeSemantics (locatedValue messageType)
    , expressionSemantics (locatedValue endpoint)
    ]
  ReceiveFrameExpression endpoint -> tagged "receive-frame"
    [expressionSemantics (locatedValue endpoint)]
  RecognizeExpression grammar raw -> tagged "recognize"
    [atom grammar, expressionSemantics (locatedValue raw)]
  ValidateExpression claim context subject -> tagged "validate"
    [ atom claim
    , semanticMaybe (expressionSemantics . locatedValue) context
    , expressionSemantics (locatedValue subject)
    ]
  SendExpression value endpoint -> tagged "send"
    [ expressionSemantics (locatedValue value)
    , expressionSemantics (locatedValue endpoint)
    ]
  SendExactExpression value endpoint -> tagged "send-exact"
    [ expressionSemantics (locatedValue value)
    , expressionSemantics (locatedValue endpoint)
    ]
  ReceiveExactExpression count endpoint evidence -> tagged "receive-exact"
    [ expressionSemantics (locatedValue count)
    , expressionSemantics (locatedValue endpoint)
    , semanticMaybe (expressionSemantics . locatedValue) evidence
    ]
  SelectExpression branch endpoint evidence -> tagged "select"
    [ branchValueSemantics branch
    , expressionSemantics (locatedValue endpoint)
    , semanticMaybe (expressionSemantics . locatedValue) evidence
    ]
  CommitReceiveExpression pending evidence -> tagged "commit-receive"
    [ expressionSemantics (locatedValue pending)
    , expressionSemantics (locatedValue evidence)
    ]
  BorrowExpression owner view body -> tagged "borrow"
    [ expressionSemantics (locatedValue owner)
    , atom view
    , blockSemantics (locatedValue body)
    ]
  DecideExpression scrutinee arms -> tagged "decide"
    [ expressionSemantics (locatedValue scrutinee)
    , SemanticOrdered (map (caseArmSemantics . locatedValue) arms)
    ]
  OfferExpression endpoint arms -> tagged "offer"
    [ expressionSemantics (locatedValue endpoint)
    , SemanticOrdered (map (caseArmSemantics . locatedValue) arms)
    ]
  FailExpression target resource -> tagged "fail"
    [ failureTargetSemantics target
    , expressionSemantics (locatedValue resource)
    ]
  CloseExpression endpoint -> tagged "close"
    [expressionSemantics (locatedValue endpoint)]
  ReleaseExpression owner -> tagged "release"
    [expressionSemantics (locatedValue owner)]
  AcceptExpression value acceptedType -> tagged "accept"
    [ expressionSemantics (locatedValue value)
    , typeSemantics (locatedValue acceptedType)
    ]
  ProveExpression proposition -> tagged "prove"
    [propositionSemantics (locatedValue proposition)]
  FallbackExpression primary fallback -> tagged "fallback"
    [ expressionSemantics (locatedValue primary)
    , fallbackSemantics fallback
    ]

propositionSemantics :: SurfaceProposition -> SemanticForm
propositionSemantics proposition = case proposition of
  PropositionTrue -> tagged "true" []
  PropositionFalse -> tagged "false" []
  PropositionEqual left right -> binaryProposition "equal" left right
  PropositionNotEqual left right -> binaryProposition "not-equal" left right
  PropositionLessThan left right -> binaryProposition "less-than" left right
  PropositionLessEqual left right -> binaryProposition "less-equal" left right
  PropositionGreaterThan left right -> binaryProposition "greater-than" left right
  PropositionGreaterEqual left right -> binaryProposition "greater-equal" left right
  PropositionAtom claim arguments -> tagged "atom"
    [ atom claim
    , SemanticOrdered (map (expressionSemantics . locatedValue) arguments)
    ]
  PropositionConjunction left right -> binaryNestedProposition "and" left right
  PropositionDisjunction left right -> binaryNestedProposition "or" left right
  PropositionNegation inner -> tagged "not"
    [propositionSemantics (locatedValue inner)]
  where
    binaryProposition tagName left right = tagged tagName
      [ expressionSemantics (locatedValue left)
      , expressionSemantics (locatedValue right)
      ]
    binaryNestedProposition tagName left right = tagged tagName
      [ propositionSemantics (locatedValue left)
      , propositionSemantics (locatedValue right)
      ]

caseArmSemantics :: CaseArm -> SemanticForm
caseArmSemantics arm = semanticRecord
  [ ("pattern", casePatternSemantics (caseArmPattern arm))
  , ("body", blockSemantics (locatedValue (caseArmBody arm)))
  ]

casePatternSemantics :: CasePattern -> SemanticForm
casePatternSemantics patternValue = semanticRecord
  [ ("label", atom (casePatternLabel patternValue))
  , ("binders", SemanticOrdered (map atom (casePatternBinders patternValue)))
  ]

branchValueSemantics :: BranchValue -> SemanticForm
branchValueSemantics branch = semanticRecord
  [ ("label", atom (branchValueLabel branch))
  , ("arguments", SemanticOrdered
      (map (expressionSemantics . locatedValue) (branchValueArguments branch)))
  ]

failureTargetSemantics :: FailureTarget -> SemanticForm
failureTargetSemantics target = semanticRecord
  [ ("class", atom (failureTargetClass target))
  , ("arguments", SemanticOrdered
      (map (expressionSemantics . locatedValue) (failureTargetArguments target)))
  ]

fallbackSemantics :: Fallback -> SemanticForm
fallbackSemantics fallback = case fallback of
  FailFallback failureClass -> tagged "fail" [atom failureClass]
  RejectFallback expression -> tagged "reject"
    [expressionSemantics (locatedValue expression)]

binaryOperatorText :: BinaryOperator -> Text
binaryOperatorText operation = case operation of
  Add -> "add"
  Subtract -> "subtract"
  Multiply -> "multiply"

semanticMaybe :: (a -> SemanticForm) -> Maybe a -> SemanticForm
semanticMaybe _ Nothing = tagged "none" []
semanticMaybe f (Just value) = tagged "some" [f value]

semanticRecord :: [(Text, SemanticForm)] -> SemanticForm
semanticRecord = SemanticRecord . Map.fromList

tagged :: Text -> [SemanticForm] -> SemanticForm
tagged tagName fields = semanticRecord
  [ ("tag", atom tagName)
  , ("fields", SemanticOrdered fields)
  ]

atom :: Text -> SemanticForm
atom = SemanticAtom

integerAtom :: Integer -> SemanticForm
integerAtom = atom . Text.pack . show

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
