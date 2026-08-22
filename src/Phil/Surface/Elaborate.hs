{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Elaborate
  ( ElaborationEnv (..)
  , ElaborationIssue (..)
  , ElaborationError (..)
  , emptyElaborationEnv
  , withProjectionSort
  , elaborateRefTerm
  , elaborateProposition
  , elaborateType
  , elaborateValue
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState)
import Phil.Core.Focusing
  ( FocusingError
  , canonicalizeProposition
  , elaborateRefTermAs
  )
import Phil.Core.SortCheck
  ( SortError
  , checkTypeSorts
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( GrammarId (GrammarId)
  , Name (Name)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Surface.Syntax
  ( BinaryOperator (..)
  , Located (..)
  , SourceSpan
  , SurfaceExpression (..)
  , SurfaceProposition (..)
  , SurfaceType (..)
  )

data ElaborationEnv = ElaborationEnv
  { elaborationStaticContext :: StaticContext
  , elaborationCheckState :: CheckState
  , elaborationProjectionSorts :: Map [Text] RefSort
  }
  deriving (Eq, Show)

data ElaborationIssue
  = UnsupportedRefinementExpression SurfaceExpression
  | UnsupportedRefinementCall Text Int
  | UnknownProjectionSort [Text]
  | UnsupportedSymbolicMultiplication
  | ElaborationFocusingError FocusingError
  | ElaborationSortError SortError
  | ValidatedIdentityMustBeName Text
  | AmbiguousIntegerLiteral Integer
  | ValueExpressionNotSupported SurfaceExpression
  | UnsupportedOpaqueTypeArgument SurfaceExpression
  deriving (Eq, Show)

data ElaborationError = ElaborationError
  { elaborationErrorSpan :: SourceSpan
  , elaborationErrorIssue :: ElaborationIssue
  }
  deriving (Eq, Show)

emptyElaborationEnv :: StaticContext -> CheckState -> ElaborationEnv
emptyElaborationEnv staticContext state = ElaborationEnv
  { elaborationStaticContext = staticContext
  , elaborationCheckState = state
  , elaborationProjectionSorts = Map.empty
  }

withProjectionSort :: [Text] -> RefSort -> ElaborationEnv -> ElaborationEnv
withProjectionSort path sort environment = environment
  { elaborationProjectionSorts = Map.insert path sort (elaborationProjectionSorts environment)
  }

elaborateRefTerm
  :: ElaborationEnv
  -> Located SurfaceExpression
  -> Either ElaborationError RefTerm
elaborateRefTerm environment locatedExpression =
  case locatedValue locatedExpression of
    VariableExpression name -> Right (RefVar (Name name))
    IntegerExpression literal -> Right (RefNat literal)
    BooleanExpression value -> Right (RefBool value)
    FieldExpression base field -> do
      baseTerm <- elaborateRefTerm environment base
      path <-
        case projectionPath locatedExpression of
          Just result -> Right result
          Nothing -> failHere (UnsupportedRefinementExpression (locatedValue locatedExpression))
      resultSort <-
        case Map.lookup path (elaborationProjectionSorts environment) of
          Just sort -> Right sort
          Nothing -> failHere (UnknownProjectionSort path)
      Right (RefField baseTerm field resultSort)
    CallExpression "len" [value] -> RefLen <$> elaborateRefTerm environment value
    CallExpression "toNat" [value] -> RefToNat <$> elaborateRefTerm environment value
    CallExpression name arguments ->
      failHere (UnsupportedRefinementCall name (length arguments))
    BinaryExpression Add left right ->
      RefAdd <$> elaborateRefTerm environment left <*> elaborateRefTerm environment right
    BinaryExpression Subtract left right ->
      RefSub <$> elaborateRefTerm environment left <*> elaborateRefTerm environment right
    BinaryExpression Multiply left right -> elaborateScale left right
    other -> failHere (UnsupportedRefinementExpression other)
  where
    failHere = Left . ElaborationError (locatedSpan locatedExpression)

    elaborateScale left right =
      case (integerLiteral left, integerLiteral right) of
        (Just coefficient, _) -> RefScale coefficient <$> elaborateRefTerm environment right
        (_, Just coefficient) -> RefScale coefficient <$> elaborateRefTerm environment left
        _ -> failHere UnsupportedSymbolicMultiplication

elaborateProposition
  :: ElaborationEnv
  -> Located SurfaceProposition
  -> Either ElaborationError Proposition
elaborateProposition environment locatedProposition = do
  raw <- rawProposition locatedProposition
  (canonical, _) <- mapFocusing (locatedSpan locatedProposition) $
    canonicalizeProposition
      (elaborationStaticContext environment)
      (elaborationCheckState environment)
      raw
  Right canonical
  where
    rawProposition proposition =
      case locatedValue proposition of
        PropositionTrue -> Right Truth
        PropositionFalse -> Right Falsehood
        PropositionEqual left right -> Equal <$> term left <*> term right
        PropositionNotEqual left right -> NotEqual <$> term left <*> term right
        PropositionLessThan left right -> LessThan <$> term left <*> term right
        PropositionLessEqual left right -> LessEqual <$> term left <*> term right
        PropositionGreaterThan left right -> LessThan <$> term right <*> term left
        PropositionGreaterEqual left right -> LessEqual <$> term right <*> term left
        PropositionAtom "member" [value, collection] -> Member <$> term value <*> term collection
        PropositionAtom "disjoint" [left, right] -> Disjoint <$> term left <*> term right
        PropositionAtom claim arguments -> Atom claim <$> mapM term arguments
        PropositionConjunction left right ->
          Conjunction <$> rawProposition left <*> rawProposition right
        PropositionDisjunction left right ->
          Disjunction <$> rawProposition left <*> rawProposition right
        PropositionNegation inner -> Negation <$> rawProposition inner

    term = elaborateRefTerm environment

elaborateType
  :: ElaborationEnv
  -> Located SurfaceType
  -> Either ElaborationError Ty
elaborateType environment locatedType = do
  result <-
    case locatedValue locatedType of
      SurfaceUnitType -> Right TyUnit
      SurfaceBoolType -> Right TyBool
      SurfaceUIntType width -> Right (TyUInt width)
      SurfaceBytesType indexExpression -> do
        rawIndex <- elaborateRefTerm environment indexExpression
        (index, _) <- mapFocusing (locatedSpan indexExpression) $
          elaborateRefTermAs
            (elaborationStaticContext environment)
            (elaborationCheckState environment)
            SortNat
            rawIndex
        Right (TyBytes index)
      SurfaceFrameType grammar -> Right (TyFrame (GrammarId grammar))
      SurfaceProofType proposition -> TyProof <$> elaborateProposition environment proposition
      SurfaceValidatedType claim context subject -> do
        contextName <- identityName "validation context" context
        subjectName <- identityName "validation subject" subject
        Right (TyValidated claim contextName subjectName)
      SurfaceNamedType name arguments ->
        TyOpaque <$> renderNamedType name arguments
  mapSort (locatedSpan locatedType) $
    checkTypeSorts (elaborationCheckState environment) result
  Right result
  where
    identityName role expression =
      case locatedValue expression of
        VariableExpression name -> Right (Name name)
        _ -> Left (ElaborationError (locatedSpan expression) (ValidatedIdentityMustBeName role))

elaborateValue
  :: ElaborationEnv
  -> Maybe Ty
  -> Located SurfaceExpression
  -> Either ElaborationError Value
elaborateValue _environment expected locatedExpression =
  case locatedValue locatedExpression of
    VariableExpression name -> Right (VVar (Name name))
    BooleanExpression value -> Right (VBool value)
    UnitExpression -> Right VUnit
    IntegerExpression literal ->
      case expectedUIntWidth expected of
        Just width -> Right (VUInt width literal)
        Nothing -> Left
          (ElaborationError
            (locatedSpan locatedExpression)
            (AmbiguousIntegerLiteral literal))
    other -> Left
      (ElaborationError
        (locatedSpan locatedExpression)
        (ValueExpressionNotSupported other))

expectedUIntWidth :: Maybe Ty -> Maybe Int
expectedUIntWidth expected =
  case expected of
    Just (TyUInt width) -> Just width
    Just (TyRefined _ base _) -> expectedUIntWidth (Just base)
    _ -> Nothing

projectionPath :: Located SurfaceExpression -> Maybe [Text]
projectionPath expression =
  case locatedValue expression of
    VariableExpression name -> Just [name]
    FieldExpression base field -> (++ [field]) <$> projectionPath base
    _ -> Nothing

integerLiteral :: Located SurfaceExpression -> Maybe Integer
integerLiteral expression =
  case locatedValue expression of
    IntegerExpression literal -> Just literal
    _ -> Nothing

renderNamedType
  :: Text
  -> [Located SurfaceExpression]
  -> Either ElaborationError Text
renderNamedType name [] = Right name
renderNamedType name arguments = do
  rendered <- mapM renderTypeArgument arguments
  Right (name <> "[" <> Text.intercalate "," rendered <> "]")

renderTypeArgument :: Located SurfaceExpression -> Either ElaborationError Text
renderTypeArgument expression =
  case locatedValue expression of
    VariableExpression name -> Right name
    IntegerExpression literal -> Right (Text.pack (show literal))
    BooleanExpression True -> Right "true"
    BooleanExpression False -> Right "false"
    UnitExpression -> Right "unit"
    TupleExpression values -> do
      rendered <- mapM renderTypeArgument values
      Right ("(" <> Text.intercalate "," rendered <> ")")
    FieldExpression base field -> do
      renderedBase <- renderTypeArgument base
      Right (renderedBase <> "." <> field)
    CallExpression name arguments -> do
      rendered <- mapM renderTypeArgument arguments
      Right (name <> "(" <> Text.intercalate "," rendered <> ")")
    BinaryExpression operation left right -> do
      renderedLeft <- renderTypeArgument left
      renderedRight <- renderTypeArgument right
      Right
        ("(" <> renderedLeft <> renderOperator operation <> renderedRight <> ")")
    other -> Left
      (ElaborationError
        (locatedSpan expression)
        (UnsupportedOpaqueTypeArgument other))
  where
    renderOperator Add = "+"
    renderOperator Subtract = "-"
    renderOperator Multiply = "*"

mapFocusing :: SourceSpan -> Either FocusingError a -> Either ElaborationError a
mapFocusing span' = either
  (Left . ElaborationError span' . ElaborationFocusingError)
  Right

mapSort :: SourceSpan -> Either SortError a -> Either ElaborationError a
mapSort span' = either
  (Left . ElaborationError span' . ElaborationSortError)
  Right
