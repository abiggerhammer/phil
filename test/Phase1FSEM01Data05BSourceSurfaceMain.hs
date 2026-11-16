{-# LANGUAGE OverloadedStrings #-}
-- FSEM-01 DATA-05B: original-source nested pattern through TWO actual
-- flat product steps of the production Surface checker. The nested type
-- projection remains test-only and does not grant general source authority.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import qualified Phil.Core.DataMode as DataMode
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Name (..), ProductElementType (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( ProductEliminationRun (..), checkSurfaceComponent
  , traceSurfaceProductEliminationComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), RejectionClass (..), SurfaceCheckError (..)
  , SurfaceCheckResult (..), SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..), grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..), grammarV1CheckedLetPatternBlockInScope )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1FunctionDecl (..), GrammarV1Pattern (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..), GrammarV1Type (..)
  , GrammarV1SourceFile (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Declaration (..), parseGrammarV1StructuralSource )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Pattern (..)
  , SourceSpan, Statement (..), SurfaceExpression (..) )
import System.Exit (exitFailure)

data Orientation = NestedLeft | NestedRight deriving (Eq, Show)

data Plan = Plan
  { packet :: Name, intermediate :: Name, flag :: Name
  , payload :: Name, spare :: Name, orientation :: Orientation
  , packetType :: Ty
  , sourceLetSpan :: SourceSpan
  , sourceInnerSpan :: SourceSpan
  , sourceReturnSpan :: SourceSpan
  } deriving (Eq, Show)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.data05a.unpack"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

nestedElements :: [ProductElementType]
nestedElements =
  [ProductElementType Linear bytes8, ProductElementType Unrestricted TyUnit]

nestedType :: Ty
nestedType = TyProduct nestedElements

productElements :: Orientation -> [ProductElementType]
productElements NestedRight =
  [ProductElementType Unrestricted TyBool, ProductElementType Linear nestedType]
productElements NestedLeft =
  [ProductElementType Linear nestedType, ProductElementType Unrestricted TyBool]

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

same :: GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder -> Bool
same x y = grammarV1ResolvedBinderKey x == grammarV1ResolvedBinderKey y

isIdentifier :: Located GrammarV1Pattern -> Bool
isIdentifier (Located _ (GrammarV1IdentifierPattern _)) = True
isIdentifier _ = False

isPairOfIdentifiers :: Located GrammarV1Pattern -> Bool
isPairOfIdentifiers (Located _ (GrammarV1TuplePattern [x,y])) =
  isIdentifier x && isIdentifier y
isPairOfIdentifiers _ = False

patternOrientation :: Located GrammarV1Pattern -> Maybe Orientation
patternOrientation (Located _ (GrammarV1TuplePattern [x,y]))
  | isIdentifier x && isPairOfIdentifiers y = Just NestedRight
  | isPairOfIdentifiers x && isIdentifier y = Just NestedLeft
patternOrientation _ = Nothing

-- Only test-local recursion: real primitive leaf type/mode checking is reused,
-- never replaced by spelling-based trust or a new production elaborator.
checkedNestedType :: Located GrammarV1Type -> Maybe CheckedTypeMode
checkedNestedType (Located _ sourceType) = case sourceType of
  GrammarV1TupleType [x,y] -> do
    left <- checkedNestedType x
    right <- checkedNestedType y
    let members =
          [ ProductElementType (checkedBindingMode checked)
              (checkedBindingType checked)
          | checked <- [left,right] ]
    pure (CheckedTypeMode (TyProduct members) (DataMode.productMode members))
  GrammarV1TupleType _ -> Nothing
  _ -> do
    Right (checked,_) <-
      grammarV1CheckedTypeMode emptyStaticContext emptySurfaceState sourceType
    pure checked

sourcePlanOf :: GrammarV1FunctionDecl -> Maybe (Either String Plan)
sourcePlanOf fn = do
  if grammarV1FunctionRecursive fn ||
     not (null (grammarV1FunctionGenericParams fn)) ||
     not (null (grammarV1FunctionRequirements fn))
    then Nothing else Just ()
  [Located _ param] <- pure (grammarV1FunctionTermParams fn)
  declaredReturn <- grammarV1FunctionResultType fn
  [Located originalLetSpan (GrammarV1LetStatement patternSource _),
   Located originalReturnSpan (GrammarV1ReturnStatement _)] <-
    pure (grammarV1BlockStatements (locatedValue (grammarV1FunctionBody fn)))
  shape <- patternOrientation patternSource
  typedPacket <- checkedNestedType (grammarV1TermParamType param)
  typedReturn <- checkedNestedType declaredReturn
  case grammarV1FunctionParameterScope root fn of
    Left err -> Just (Left ("parameter lexical scope: " ++ show err))
    Right ([owner],scope) ->
      case grammarV1CheckedLetPatternBlockInScope scope (grammarV1FunctionBody fn) of
        Nothing -> Nothing
        Just (Left err) -> Just (Left ("let/pattern scope: " ++ show err))
        Just (Right ([GrammarV1CheckedLetBindingStep _ input names,
                      GrammarV1CheckedLetOccurrenceStep _ returned],_)) ->
          let inputOwner = grammarV1CheckedLocalValueBinder input
              returnedOwner = grammarV1CheckedLocalValueBinder returned
              ordered = case (shape,names) of
                (NestedRight,[a,b,c]) -> Just (a,b,c)
                (NestedLeft,[a,b,c]) -> Just (c,a,b)
                _ -> Nothing
              expected = CheckedTypeMode (TyProduct (productElements shape)) Linear
          in case ordered of
               Nothing -> Nothing
               Just (flagBinder,payloadBinder,spareBinder)
                 | not (same inputOwner owner) ->
                     Just (Left "let initializer was not the checked packet owner")
                 | typedPacket /= expected ->
                     Just (Left ("nested packet leaf/type/mode mismatch: " ++ show typedPacket))
                 | typedReturn /= CheckedTypeMode bytes8 Linear ->
                     Just (Left "declared return was not Linear Bytes[8]")
                 | not (same returnedOwner payloadBinder) ->
                     Just (Left "returned source identity was not the Bytes[8] leaf")
                 | otherwise ->
                     let inputName = name owner
                         innerName = Name ("$phil.data05a.inner:" <> unName inputName)
                         leaves = map name names
                         innerSpan = case locatedValue patternSource of
                           GrammarV1TuplePattern [first,second] ->
                             locatedSpan (if shape == NestedRight then second else first)
                           _ -> locatedSpan patternSource
                     in if elem innerName (inputName:leaves)
                        then Just (Left "intermediate Core name not globally fresh")
                        else Just (Right Plan
                          { packet = inputName, intermediate = innerName
                          , flag = name flagBinder, payload = name payloadBinder
                          , spare = name spareBinder, orientation = shape
                          , packetType = checkedBindingType typedPacket
                          , sourceLetSpan = originalLetSpan
                          , sourceInnerSpan = innerSpan
                          , sourceReturnSpan = originalReturnSpan })
        Just (Right _) -> Nothing
    Right _ -> Nothing

parse :: Text -> Either String GrammarV1FunctionDecl
parse source = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "data05a-original-source" source)
  case grammarV1TopLevelDecls file of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("not a source function: " ++ show other)
    other -> Left ("expected one source declaration: " ++ show (length other))

check :: Bool -> String -> Either String ()
check ok why = if ok then Right () else Left why

-- Both actual Core.DataMode eliminations must succeed, each with exact
-- native Map/Set snapshots and strict no-resurrection/negative controls.
runPlan :: Plan -> Either String ()
runPlan plan = do
  let packetName = packet plan
      mid = intermediate plan
      flagName = flag plan
      payloadName = payload plan
      spareName = spare plan
      outerNames = case orientation plan of
        NestedRight -> [flagName,mid]
        NestedLeft -> [mid,flagName]
      innerNames = [payloadName,spareName]
      initialExpected = Core.ResourceContext Map.empty Map.empty
        (Map.singleton packetName (packetType plan)) Set.empty
      outerExpected = Core.ResourceContext
        (Map.singleton flagName TyBool) Map.empty
        (Map.singleton mid nestedType) Set.empty
      innerExpected = Core.ResourceContext
        (Map.fromList [(flagName,TyBool),(spareName,TyUnit)]) Map.empty
        (Map.singleton payloadName bytes8) Set.empty
      returnedExpected = innerExpected { Core.linearBindings = Map.empty }
  initial <- either (Left . show) Right
    (Core.insertBinding Linear packetName (packetType plan) Core.emptyContext)
  check (initial == initialExpected) "initial native product context differed"
  outer <- either (Left . show) Right
    (DataMode.eliminateProductBinding packetName outerNames initial)
  check (outer == outerExpected) "outer product elimination state differed"
  inner <- either (Left . show) Right
    (DataMode.eliminateProductBinding mid innerNames outer)
  check (inner == innerExpected) "inner product elimination state differed"
  (returnedTy,done) <- either (Left . show) Right
    (Core.consumeLinear payloadName inner)
  check (returnedTy == bytes8 && done == returnedExpected &&
         Core.ensureComplete done == Right ())
    "returned payload not consumed once or terminal debt remained"
  check (Core.useBinding packetName outer == Left (Core.UnknownBinding packetName) &&
         Core.useBinding packetName inner == Left (Core.UnknownBinding packetName) &&
         Core.useBinding mid inner == Left (Core.UnknownBinding mid) &&
         Core.consumeLinear payloadName done == Left (Core.UnknownBinding payloadName))
    "original, intermediate or returned Linear owner resurrected"
  let wrongMode = Core.emptyContext { Core.unrestrictedBindings =
        Map.singleton packetName (packetType plan) }
      wrongType = Core.emptyContext { Core.linearBindings =
        Map.singleton packetName TyBool }
  check (DataMode.eliminateProductBinding packetName [flagName] initial ==
           Left (DataMode.ProductArityMismatch 2 1) &&
         DataMode.eliminateProductBinding packetName [flagName,mid,spareName] initial ==
           Left (DataMode.ProductArityMismatch 2 3) &&
         DataMode.eliminateProductBinding mid [payloadName] outer ==
           Left (DataMode.ProductArityMismatch 2 1) &&
         DataMode.eliminateProductBinding mid [payloadName,spareName,flagName] outer ==
           Left (DataMode.ProductArityMismatch 2 3))
    "nested product arity failure did not reject at exact stage"
  check (DataMode.eliminateProductBinding packetName [flagName,flagName] initial ==
           Left (DataMode.ProductContextError (Core.DuplicateBinding flagName)) &&
         DataMode.eliminateProductBinding mid [payloadName,payloadName] outer ==
           Left (DataMode.ProductContextError (Core.DuplicateBinding payloadName)) &&
         DataMode.eliminateProductBinding mid [flagName,spareName] outer ==
           Left (DataMode.ProductContextError (Core.DuplicateBinding flagName)))
    "duplicate or already-live product successor admitted"
  check (DataMode.eliminateProductBinding packetName outerNames wrongMode ==
           Left (DataMode.ProductModeMismatch packetName Linear Unrestricted) &&
         DataMode.eliminateProductBinding packetName outerNames wrongType ==
           Left (DataMode.ProductExpected packetName TyBool) &&
         DataMode.eliminateProductBinding packetName outerNames outer ==
           Left (DataMode.ProductContextError (Core.UnknownBinding packetName)) &&
         DataMode.eliminateProductBinding mid innerNames inner ==
           Left (DataMode.ProductContextError (Core.UnknownBinding mid)))
    "wrong type/mode or stale product elimination was admitted"
  borrowed <- either (Left . show) Right (Core.startSharedLoan mid outer)
  check (DataMode.eliminateProductBinding mid innerNames borrowed ==
           Left (DataMode.ProductContextError (Core.OwnerBorrowed mid)) &&
         Core.ensureComplete inner ==
           Left (Core.UnconsumedLinearResources (Map.singleton payloadName bytes8)) &&
         Core.ensureComplete done == Right ())
    "live loan or unpaid nested Linear debt reached completion"
  checkRealSurface plan initial outer inner


-- DATA-05B source-checked flat projection. Every Surface step below is run
-- through the actual production Engine: no implementation of that transition
-- is duplicated in this test. Source lexical identities and primitive type
-- modes come solely from sourcePlanOf and existing binder/type checkers.
outerContract :: Plan -> [ProductElementType]
outerContract p = productElements (orientation p)

typeContract :: Mode -> Ty -> InitialBinding
typeContract mode ty = InitialBinding mode ty (shapeForType ty)

surfaceEnv :: Plan -> SurfaceEnvironment
surfaceEnv p = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton
      (unName (packet p)) (typeContract Linear (packetType p))
  , surfaceExpectedProductEliminations = Map.fromList
      [ (unName (packet p), outerContract p)
      , (unName (intermediate p), nestedElements) ]
  }

secondStageEnv :: Plan -> SurfaceEnvironment
secondStageEnv p = (surfaceEnv p)
  { surfaceInitialBindings = Map.fromList
      [ (unName (flag p), typeContract Unrestricted TyBool)
      , (unName (intermediate p), typeContract Linear nestedType) ]
  }

sourceFlatLet :: SourceSpan -> Name -> [Name] -> Located Statement
sourceFlatLet span' owner names =
  Located span' (LetStatement
    (Located span' (TuplePattern
      [Located span' (BindPattern (unName n)) | n <- names]))
    (Located span' (VariableExpression (unName owner))))

sourceReturn :: SourceSpan -> Name -> Located Statement
sourceReturn span' owner = Located span'
  (ReturnStatement (Located span' (VariableExpression (unName owner))))

sourceComponent :: Plan -> [Located Statement] -> Located Component
sourceComponent p statements = Located (sourceLetSpan p)
  (Component
    { componentName = "unpack"
    , componentParameters = []
    , componentProvides = Nothing
    , componentBody = Located (sourceLetSpan p) (Block statements)
    })

firstStage :: Plan -> Located Statement
firstStage p = sourceFlatLet (sourceLetSpan p) (packet p) $
  case orientation p of
    NestedRight -> [flag p,intermediate p]
    NestedLeft -> [intermediate p,flag p]

secondStage :: Plan -> Located Statement
secondStage p = sourceFlatLet (sourceInnerSpan p) (intermediate p)
  [payload p,spare p]

fullStage :: Plan -> Located Component
fullStage p = sourceComponent p
  [ firstStage p
  , secondStage p
  , sourceReturn (sourceReturnSpan p) (payload p) ]

checkError :: RejectionClass
  -> Either SurfaceCheckError SurfaceCheckResult
  -> Either String ()
checkError expected (Left err) = check (surfaceErrorClass err == expected)
  ("wrong production Surface rejection class: " ++ show err)
checkError _ (Right succeeded) =
  Left ("invalid projected source admitted: " ++ show succeeded)

checkSurfaceRejected :: Either SurfaceCheckError SurfaceCheckResult -> Either String ()
checkSurfaceRejected (Left _) = Right ()
checkSurfaceRejected (Right succeeded) =
  Left ("invalid projected source produced successor: " ++ show succeeded)

-- The first checkpoint is recorded by the production trace interface after
-- the first let (before its deliberately failing return). The second checkpoint
-- is independently recorded by that SAME production trace for the second let,
-- under the exact resource predecessor obtained after the first.
checkRealSurface
  :: Plan -> Core.ResourceContext -> Core.ResourceContext
  -> Core.ResourceContext -> Either String ()
checkRealSurface p initial outer inner = do
  let env = surfaceEnv p
      env2 = secondStageEnv p
      first = sourceComponent p
        [firstStage p,sourceReturn (sourceReturnSpan p) (flag p)]
      second = sourceComponent p
        [secondStage p,sourceReturn (sourceReturnSpan p) (payload p)]
      full = fullStage p
      firstOutcome = checkSurfaceComponent env first
      secondOutcome = checkSurfaceComponent env2 second
      fullOutcome = checkSurfaceComponent env full
  -- One-shotness here depends on both products being Linear. The generated
  -- inner Core name is fresh and never presented as a source binder.
  check (DataMode.productMode (outerContract p) == Linear &&
         DataMode.productMode nestedElements == Linear &&
         Set.size (Set.fromList
           [packet p,intermediate p,flag p,payload p,spare p]) == 5)
    "source identities collided or nested product ceased to be Linear"
  trace1 <- maybe (Left "first Surface product trace is noncompetent") Right
    (traceSurfaceProductEliminationComponent env first)
  check (productEliminationBefore trace1 == Just initial &&
         productEliminationAfter trace1 == Just outer &&
         productEliminationOutcome trace1 == firstOutcome)
    "first *actual* Surface elimination diverged from native Core"
  -- The first staged negative still owns the Linear inner product.
  checkError LinearCompletion firstOutcome
  trace2 <- maybe (Left "second Surface product trace is noncompetent") Right
    (traceSurfaceProductEliminationComponent env2 second)
  check (productEliminationBefore trace2 == Just outer &&
         productEliminationAfter trace2 == Just inner &&
         productEliminationOutcome trace2 == secondOutcome)
    "second *actual* Surface elimination diverged from native Core"
  check (secondOutcome == Right (SurfaceCheckResult "unpack" [Return bytes8]) &&
         fullOutcome == secondOutcome)
    ("complete *actual* two-let Surface projection rejected: " ++ show fullOutcome)

  -- Hostile/missing source-checked product contracts must never accidentally
  -- authorize the flat production adapter. These are real Engine errors.
  let contracts = surfaceExpectedProductEliminations env
      wrongFirst = env { surfaceExpectedProductEliminations =
        Map.insert (unName (packet p)) nestedElements contracts }
      wrongSecond = env { surfaceExpectedProductEliminations =
        Map.insert (unName (intermediate p)) (outerContract p) contracts }
      noSecond = env { surfaceExpectedProductEliminations =
        Map.delete (unName (intermediate p)) contracts }
      noContracts = env { surfaceExpectedProductEliminations = Map.empty }
      firstArity = sourceComponent p
        [sourceFlatLet (sourceLetSpan p) (packet p) [flag p],
         secondStage p,sourceReturn (sourceReturnSpan p) (payload p)]
      secondArity = sourceComponent p
        [firstStage p,
         sourceFlatLet (sourceInnerSpan p) (intermediate p) [payload p],
         sourceReturn (sourceReturnSpan p) (payload p)]
      duplicateSecond = sourceComponent p
        [firstStage p,
         sourceFlatLet (sourceInnerSpan p) (intermediate p)
           [payload p,payload p],
         sourceReturn (sourceReturnSpan p) (payload p)]
      liveCollision = sourceComponent p
        [firstStage p,
         sourceFlatLet (sourceInnerSpan p) (intermediate p)
           [flag p,spare p],
         sourceReturn (sourceReturnSpan p) (payload p)]
      staleOriginal = sourceComponent p
        [firstStage p,
         sourceFlatLet (sourceInnerSpan p) (packet p) [payload p,spare p],
         sourceReturn (sourceReturnSpan p) (payload p)]
      wrongReturn = sourceComponent p
        [firstStage p,secondStage p,sourceReturn (sourceReturnSpan p) (flag p)]
  checkError TypeMismatch (checkSurfaceComponent wrongFirst full)
  checkError TypeMismatch (checkSurfaceComponent wrongSecond full)
  checkError TypeMismatch (checkSurfaceComponent env firstArity)
  checkError TypeMismatch (checkSurfaceComponent env secondArity)
  checkError StructuralUse (checkSurfaceComponent env duplicateSecond)
  checkError StructuralUse (checkSurfaceComponent env liveCollision)
  checkError LinearCompletion (checkSurfaceComponent env wrongReturn)
  checkSurfaceRejected (checkSurfaceComponent noSecond full)
  checkSurfaceRejected (checkSurfaceComponent noContracts full)
  checkSurfaceRejected (checkSurfaceComponent env staleOriginal)

fixturePath :: String -> FilePath
fixturePath key = "test/fixtures/fsem01-data05a-nested-product-v1/" ++ key ++ ".phil"

checkAccepted :: String -> Orientation -> IO (Either String ())
checkAccepted key shape = do
  source <- TextIO.readFile (fixturePath key)
  pure $ do
    fn <- parse source
    plan <- case sourcePlanOf fn of
      Just (Right p) -> Right p
      other -> Left ("accepted source outside fragment: " ++ show other)
    check (orientation plan == shape) "wrong source-tree orientation"
    runPlan plan

checkRejected :: String -> String -> IO (Either String ())
checkRejected key fragment = do
  source <- TextIO.readFile (fixturePath key)
  pure $ do
    fn <- parse source
    case sourcePlanOf fn of
      Just (Left why)
        | Text.isInfixOf (Text.pack fragment) (Text.pack why) -> Right ()
      other -> Left ("wrong source-only negative: " ++ key ++ " " ++ show other)

checkUnsupported :: String -> IO (Either String ())
checkUnsupported key = do
  source <- TextIO.readFile (fixturePath key)
  pure $ do
    fn <- parse source
    check (sourcePlanOf fn == Nothing)
      ("out-of-fragment nested program was admitted: " ++ key)

main :: IO ()
main = do
  checked <- sequence
    [ checkAccepted "accepted-right" NestedRight
    , checkAccepted "accepted-left" NestedLeft
    , checkRejected "duplicate-leaf" "let/pattern scope"
    , checkRejected "shadow-packet" "let/pattern scope"
    , checkRejected "wrong-return-owner" "returned source identity"
    , checkRejected "wrong-return-type" "declared return"
    , checkRejected "wrong-leaf-width" "nested packet leaf/type/mode"
    , checkRejected "wrong-leaf-shape" "nested packet leaf/type/mode"
    , checkRejected "wrong-pattern-side" "nested packet leaf/type/mode"
    , checkUnsupported "wide-inner-pattern"
    , checkUnsupported "flat-pattern"
    , checkUnsupported "unknown-return"
    , checkUnsupported "extra-source-statement"
    ]
  case sequence checked of
    Left why -> putStrLn ("FAIL DATA-05A: " ++ why) >> exitFailure
    Right _ -> putStrLn
      "PASS DATA-05B: two original nested source orientations, two actual Surface elimination snapshots, independent native Core parity, 11 source negatives and 10 Surface negative controls"
