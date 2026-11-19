{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 REC-01: source-owned *closed* record field disposition and
-- native Core.DataDestruction bridge. This is not production Surface record
-- elaboration: Core has no TyRecord and Surface.Syntax has no record Pattern.
-- The opaque record binding is an explicitly INTERNAL representation premise,
-- not a newly admitted nominal type or a proof of source-to-Core refinement.
module Phil.Surface.GrammarV1.SourceRecordFieldDisposition
  ( GrammarV1RecordDispositionError (..)
  , GrammarV1RecordFieldTransfer (..)
  , GrammarV1RecordDispositionTrace (..)
  , grammarV1CheckedSourceRecordDisposition
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import qualified Phil.Core.Context as Core
import Phil.Core.DataDestruction
  ( DataDestructionError
  , FieldDisposition (..)
  , OwnedField (..)
  , checkFieldDispositions
  , consumeAggregateFields
  )
import Phil.Core.Focusing (FocusingError)
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..)
  , GrammarV1LetPatternScopeError
  , grammarV1CheckedLetPatternBlockInScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Declaration (..)
  , GrammarV1Field (..)
  , GrammarV1FieldPattern (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1Pattern (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1RecordDecl (..)
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TermParam (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.GrammarV1.RecordFields
  ( GrammarV1CheckedRecordMode (..)
  , GrammarV1CheckedRecordModeError
  , grammarV1CheckedClosedRecordMode
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1RecordDispositionError
  = SourceRecordModeError GrammarV1CheckedRecordModeError
  | SourceRecordReturnTypeError FocusingError
  | SourceRecordParameterError GrammarV1BinderScopeError
  | SourceRecordLetError GrammarV1LetPatternScopeError
  | SourceRecordDispositionError DataDestructionError
  | SourceRecordNativeError Core.CheckError
  | SourceRecordMismatch Text
  deriving (Eq, Show)

-- | Original declared label and the exact source-rooted destination binder.
-- A Nothing destination is an omitted Unrestricted field. A declared Linear
-- field must instead have a fresh, single owned source destination.
data GrammarV1RecordFieldTransfer = GrammarV1RecordFieldTransfer
  { recordTransferLabel :: Text
  , recordTransferMode :: Mode
  , recordTransferType :: Ty
  , recordTransferDestination :: Maybe GrammarV1ResolvedBinder
  } deriving (Eq, Show)

-- | The actual DataDestruction/Context transition is observed using the
-- exact field schema derived from the original parsed record declaration.
-- Record nominal type identity and Surface record-pattern lowering remain
-- external proof obligations; the carrier has no public type authority.
data GrammarV1RecordDispositionTrace = GrammarV1RecordDispositionTrace
  { recordDispositionDeclarationKey :: DeclarationKey
  , recordDispositionRecordName :: Text
  , recordDispositionStructuralMode :: Mode
  , recordDispositionOwner :: GrammarV1ResolvedBinder
  , recordDispositionFields :: [GrammarV1RecordFieldTransfer]
  , recordDispositionReturnedBinder :: GrammarV1ResolvedBinder
  , recordDispositionReturnedType :: Ty
  , recordDispositionOpaqueCarrier :: Ty
  , recordDispositionBefore :: Core.ResourceContext
  , recordDispositionAfter :: Core.ResourceContext
  , recordDispositionTerminal :: Core.ResourceContext
  } deriving (Eq, Show)

sourceMismatch :: Text -> Either GrammarV1RecordDispositionError a
sourceMismatch = Left . SourceRecordMismatch

-- | Only original flat record field shorthand/identifier-alias patterns.
-- Nested field products, record aliases and incomplete static meanings are
-- outside this adapter, never automatically source-invalid.
sourceField :: Located GrammarV1FieldPattern -> Maybe (Text, Text)
sourceField (Located _ field) =
  case grammarV1FieldPatternValue field of
    Nothing -> Just (label,label)
    Just (Located _ (GrammarV1IdentifierPattern (Located _ alias))) ->
      Just (label,alias)
    _ -> Nothing
  where
    label = locatedValue (grammarV1FieldPatternName field)

isIntrinsicUnrestricted :: Ty -> Bool
isIntrinsicUnrestricted ty = case ty of
  TyUnit -> True
  TyBool -> True
  TyUInt _ -> True
  _ -> False

isLinearBytes :: Ty -> Bool
isLinearBytes ty = case ty of
  TyBytes _ -> True
  _ -> False

-- | Stage one: check actual source identity, exact intrinsic field modes,
-- original record label order and exact lexical binder identities. Stage two:
-- check source-owned dispositions through the real certified native consumer.
-- Stage three: compare its output against independent Core operations and
-- require a one-shot Linear return. No caller-authored owner/schema/plan.
grammarV1CheckedSourceRecordDisposition
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1SourceFile
  -> Maybe (Either GrammarV1RecordDispositionError GrammarV1RecordDispositionTrace)
grammarV1CheckedSourceRecordDisposition static declarationKey file
  | grammarV1ModuleDecl file /= Nothing = Nothing
  | not (null (grammarV1ImportDecls file)) = Nothing
  | otherwise = do
      [GrammarV1RecordDeclaration record,
       GrammarV1FunctionDeclaration fn] <-
        pure
          [ locatedValue (grammarV1Declaration (locatedValue item))
          | item <- grammarV1TopLevelDecls file
          ]
      if not (null (grammarV1RecordGenericParams record)) ||
         not (null (grammarV1RecordRequirements record)) ||
         grammarV1FunctionRecursive fn ||
         not (null (grammarV1FunctionGenericParams fn)) ||
         not (null (grammarV1FunctionRequirements fn))
        then Nothing else Just ()
      [Located _ parameter] <- pure (grammarV1FunctionTermParams fn)
      resultSource <- grammarV1FunctionResultType fn
      [Located _ (GrammarV1LetStatement pattern' _),
       Located _ (GrammarV1ReturnStatement _)] <-
        pure (grammarV1BlockStatements (locatedValue (grammarV1FunctionBody fn)))
      let recordName = locatedValue (grammarV1RecordName record)
      case locatedValue (grammarV1TermParamType parameter) of
        GrammarV1NamedType reference
          | grammarV1StaticReferenceArguments reference == [] &&
            grammarV1QualifiedNameParts
              (grammarV1StaticReferenceName reference) == [recordName] ->
              Just ()
        _ -> Nothing
      sourceSelections <- case locatedValue pattern' of
        GrammarV1RecordPattern (Located _ qualified) fields
          | grammarV1QualifiedNameParts qualified == [recordName] ->
              mapM sourceField fields
        _ -> Nothing
      -- Unknown local value occurrences may denote static names. Do not use
      -- this bounded lexical adapter to pronounce such source invalid.
      case grammarV1FunctionParameterScope declarationKey fn of
        Right (_,scope) ->
          case grammarV1CheckedLetPatternBlockInScope scope
              (grammarV1FunctionBody fn) of
            Nothing -> Nothing
            _ -> Just ()
        Left _ -> Just ()
      checkedRecord <- grammarV1CheckedClosedRecordMode static Nothing record
      checkedResult <- grammarV1CheckedTypeMode
        static emptySurfaceState (locatedValue resultSource)
      case (checkedRecord,checkedResult) of
        (Left err,_) -> Just (Left (SourceRecordModeError err))
        (_,Left err) -> Just (Left (SourceRecordReturnTypeError err))
        (Right recordMode,Right (returnType,_)) -> do
          let checkedFields = checkedRecordModeFields recordMode
              linearFields =
                [ (label,checkedBindingType fieldMode)
                | (label,fieldMode,_) <- checkedFields
                , checkedBindingMode fieldMode == Linear ]
              allPrimitive =
                all (\(_,fm,_) ->
                  let ty = checkedBindingType fm
                      mode = checkedBindingMode fm
                  in (mode == Unrestricted && isIntrinsicUnrestricted ty) ||
                     (mode == Linear && isLinearBytes ty))
                  checkedFields
          case linearFields of
            [(_,linearTy)]
              | allPrimitive &&
                checkedRecordStructuralMode recordMode == Linear &&
                returnType == CheckedTypeMode linearTy Linear ->
                  Just ()
            [(_,linearTy)] | allPrimitive &&
                checkedRecordStructuralMode recordMode == Linear &&
                checkedBindingType returnType /= linearTy ->
                  Just ()
            _ -> Nothing
          Just $ do
            (owner,binders,returned) <-
              case grammarV1FunctionParameterScope declarationKey fn of
                Left err -> Left (SourceRecordParameterError err)
                Right ([parameterOwner],scope) ->
                  case grammarV1CheckedLetPatternBlockInScope scope
                      (grammarV1FunctionBody fn) of
                    Nothing -> sourceMismatch "record lexical body is unsupported"
                    Just (Left err) -> Left (SourceRecordLetError err)
                    Just (Right
                      ([GrammarV1CheckedLetBindingStep _ initializer newBinders,
                        GrammarV1CheckedLetOccurrenceStep _ returnedOccurrence],_))
                      | grammarV1ResolvedBinderKey
                          (grammarV1CheckedLocalValueBinder initializer) ==
                            grammarV1ResolvedBinderKey parameterOwner ->
                          Right
                            (parameterOwner,newBinders,
                              grammarV1CheckedLocalValueBinder returnedOccurrence)
                      | otherwise -> sourceMismatch
                          "record initializer differs from checked original parameter"
                    Just (Right _) -> sourceMismatch
                      "record source must have one record-let and final return"
                Right _ -> sourceMismatch "exactly one checked parameter required"
            if length sourceSelections /= length binders
              then sourceMismatch "record field binder arity disagrees with lexical source"
              else Right ()
            let selected = zip sourceSelections binders
            if any (\((_,display),binder) ->
                grammarV1ResolvedBinderDisplayName binder /= display) selected
              then sourceMismatch "record pattern alias does not match lexical binder"
              else Right ()

            let declaredSchema =
                  [ OwnedField (Name label)
                      (checkedBindingMode typed) (checkedBindingType typed)
                  | (label,typed,_) <- checkedFields ]
                selectedDisposition =
                  [ (Name label,FieldBound) | ((label,_),_) <- selected ]
            case checkFieldDispositions declaredSchema selectedDisposition of
              Left err -> Left (SourceRecordDispositionError err)
              Right () -> Right ()

            let selectedMap = Map.fromList
                  [ (label,binder) | ((label,_),binder) <- selected ]
                transfers =
                  [ GrammarV1RecordFieldTransfer label
                      (checkedBindingMode typed) (checkedBindingType typed)
                      (Map.lookup label selectedMap)
                  | (label,typed,_) <- checkedFields ]
            (linearLabel,linearType) <- case linearFields of
              [only] -> Right only
              _ -> sourceMismatch "exactly one checked Linear Bytes[N] source field required"
            payload <- case Map.lookup linearLabel selectedMap of
              Nothing -> sourceMismatch "linear source field has no restored binder"
              Just binder -> Right binder
            if grammarV1ResolvedBinderCoreName payload /=
                grammarV1ResolvedBinderCoreName returned
              then sourceMismatch "returned original source binder is not the Linear record field"
              else Right ()
            if returnType /= CheckedTypeMode linearType Linear
              then sourceMismatch "declared return type differs from Linear record field"
              else Right ()
            let packet = grammarV1ResolvedBinderCoreName owner
                syntheticOmitted label =
                  Name ("$phil.rec01.omitted:" <> unName packet <> ":" <> label)
                dataFields =
                  [ OwnedField
                      (maybe (syntheticOmitted (recordTransferLabel field))
                        grammarV1ResolvedBinderCoreName
                        (recordTransferDestination field))
                      (recordTransferMode field)
                      (recordTransferType field)
                  | field <- transfers ]
                restored =
                  [ (ownedFieldName field, FieldBound)
                  | field <- dataFields
                  , any (\bound -> grammarV1ResolvedBinderCoreName bound ==
                        ownedFieldName field) binders ]
                allNames = packet : map ownedFieldName dataFields
            if Set.size (Set.fromList allNames) /= length allNames
              then sourceMismatch "source or generated Core destination identities collide"
              else Right ()
            -- TyOpaque is an INTERNAL Core carrier. No nominal record
            -- identity/sound source construction claim follows from it.
            let opaqueCarrier = TyOpaque
                  ("$phil.rec01.record-carrier:" <> recordName <> ":" <> unName packet)
            initial <- case Core.insertBinding
                Linear packet opaqueCarrier Core.emptyContext of
              Left err -> Left (SourceRecordNativeError err)
              Right ctx -> Right ctx
            after <- case consumeAggregateFields
                packet dataFields restored initial of
              Left err -> Left (SourceRecordDispositionError err)
              Right ctx -> Right ctx

            (mode,usedType,popped) <- case Core.useBinding packet initial of
              Left err -> Left (SourceRecordNativeError err)
              Right step -> Right step
            if mode /= Linear || usedType /= opaqueCarrier
              then sourceMismatch "native Core consumed wrong record carrier"
              else Right ()
            independent <- foldM (\ctx field ->
                if (ownedFieldName field,FieldBound) `elem` restored
                  then case Core.insertBinding
                      (ownedFieldMode field)
                      (ownedFieldName field)
                      (ownedFieldType field) ctx of
                    Left err -> Left (SourceRecordNativeError err)
                    Right next -> Right next
                  else Right ctx) popped dataFields
            if independent /= after ||
               Core.useBinding packet after /= Left (Core.UnknownBinding packet)
              then sourceMismatch "native record owner was resurrected or fields differed"
              else Right ()
            (returnedType,terminal) <- case Core.consumeLinear
                (grammarV1ResolvedBinderCoreName returned) after of
              Left err -> Left (SourceRecordNativeError err)
              Right consumed -> Right consumed
            if returnedType /= linearType ||
               Core.ensureComplete terminal /= Right () ||
               Core.consumeLinear
                 (grammarV1ResolvedBinderCoreName returned) terminal /=
                   Left (Core.UnknownBinding
                     (grammarV1ResolvedBinderCoreName returned))
              then sourceMismatch "Linear record field was not returned exactly once"
              else Right ()
            Right GrammarV1RecordDispositionTrace
              { recordDispositionDeclarationKey = declarationKey
              , recordDispositionRecordName = recordName
              , recordDispositionStructuralMode =
                  checkedRecordStructuralMode recordMode
              , recordDispositionOwner = owner
              , recordDispositionFields = transfers
              , recordDispositionReturnedBinder = returned
              , recordDispositionReturnedType = linearType
              , recordDispositionOpaqueCarrier = opaqueCarrier
              , recordDispositionBefore = initial
              , recordDispositionAfter = after
              , recordDispositionTerminal = terminal
              }
