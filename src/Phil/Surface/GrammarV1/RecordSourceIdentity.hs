{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.RecordSourceIdentity
  ( RecordSourceError (..)
  , ConditionallyCheckedRecord
  , checkSelectedRecordSource
  , checkedRecordIdentity
  , checkedFunctionIdentity
  , checkedOwner
  , checkedOwnerType
  , checkedReturnedBinder
  , eliminateCheckedRecord
  ) where

import Control.Monad (unless)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as Bytes
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Numeric (showHex)
import Phil.Core.Context (ResourceContext)
import Phil.Core.DataDestruction
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder, grammarV1ResolvedBinderCoreName )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SourceRecordFieldDisposition
import Phil.Surface.Syntax (Located (..), SourcePoint (..), SourceSpan (..))
import Text.Read (readMaybe)

data RecordSourceError
  = SelectedOriginMismatch
  | MalformedRecordManifest
  | RecordDeclarationSitesMismatch
  | MalformedRecordSource GrammarV1ParseDiagnostic
  | MalformedRecordSourceEncoding
  | RecordSourceOutsideFragment
  | RecordNominalReferenceMismatch
  | RecordSourceDispositionRejected GrammarV1RecordDispositionError
  | RecordNativeRejection DataDestructionError
  deriving (Eq, Show)

-- Positional fields keep external record update from rewriting the checked association.
data ConditionallyCheckedRecord = ConditionallyCheckedRecord
  DeclarationIdentity DeclarationIdentity GrammarV1ResolvedBinder
  GrammarV1ResolvedBinder [(OwnedField, Maybe Name)]

checkedRecordIdentity :: ConditionallyCheckedRecord -> DeclarationIdentity
checkedRecordIdentity (ConditionallyCheckedRecord identity _ _ _ _) = identity

checkedFunctionIdentity :: ConditionallyCheckedRecord -> DeclarationIdentity
checkedFunctionIdentity (ConditionallyCheckedRecord _ identity _ _ _) = identity

checkedOwner :: ConditionallyCheckedRecord -> GrammarV1ResolvedBinder
checkedOwner (ConditionallyCheckedRecord _ _ owner _ _) = owner

checkedReturnedBinder :: ConditionallyCheckedRecord -> GrammarV1ResolvedBinder
checkedReturnedBinder (ConditionallyCheckedRecord _ _ _ returned _) = returned

checkedOwnerType :: ConditionallyCheckedRecord -> Ty
checkedOwnerType checked =
  let identity = checkedRecordIdentity checked
  in TyRecordNominal (identityDeclarationKey identity) (identityInterfaceRevision identity)

-- | The selection path and expected byte strings must come from an
-- independently selected authority. This function checks correspondence, not
-- authenticity of that selection. The sidecar's SHA-256 is a consistency
-- commitment, with collision resistance assumed for that commitment alone.
checkSelectedRecordSource
  :: StaticContext
  -> Text
  -> (Bytes.ByteString, Bytes.ByteString)
  -> (Bytes.ByteString, Bytes.ByteString)
  -> Either RecordSourceError ConditionallyCheckedRecord
checkSelectedRecordSource static path selected actual@(sourceBytes, manifestBytes) = do
  unless (actual == selected) $ Left SelectedOriginMismatch
  manifest <- mapLeft (const MalformedRecordManifest) $ Text.decodeUtf8' manifestBytes
  (recordSite, functionSite) <- parseManifest path (sourceDigest sourceBytes) manifest
  source <- mapLeft (const MalformedRecordSourceEncoding) $ Text.decodeUtf8' sourceBytes
  parsed <- mapLeft MalformedRecordSource $ parseGrammarV1StructuralSource path source
  unless (grammarV1ModuleDecl parsed == Nothing && null (grammarV1ImportDecls parsed)) $
    Left RecordSourceOutsideFragment
  case grammarV1TopLevelDecls parsed of
    [recordTop, functionTop]
      | GrammarV1RecordDeclaration record <- declaration recordTop
      , GrammarV1FunctionDeclaration fn <- declaration functionTop -> do
          unless (matchesSite path recordSite recordTop && matchesSite path functionSite functionTop) $
            Left RecordDeclarationSitesMismatch
          checkReferences record fn
          trace <- case grammarV1CheckedSourceRecordDisposition static (siteKey functionSite) parsed of
            Nothing -> Left RecordSourceOutsideFragment
            Just checked -> mapLeft RecordSourceDispositionRejected checked
          let toPlan field =
                ( OwnedField (Name (recordTransferLabel field))
                    (recordTransferMode field) (recordTransferType field)
                , grammarV1ResolvedBinderCoreName <$> recordTransferDestination field
                )
              plan = map toPlan (recordDispositionFields trace)
          identity <- mapLeft RecordNativeRejection $ nominalRecordIdentity (siteKey recordSite) (map fst plan)
          let parameterType = TyRecordNominal
                (identityDeclarationKey identity) (identityInterfaceRevision identity)
              signature = SemanticOrdered
                [ SemanticAtom "closed-record-function-v1"
                , SemanticAtom (Text.pack (show parameterType))
                , SemanticAtom (Text.pack (show (recordDispositionReturnedType trace)))
                ]
              functionIdentity = deriveDeclarationIdentity $ DeclarationDescriptor
                (DeclarationPresentation (locatedValue (grammarV1FunctionName fn)) [])
                (siteKey functionSite) signature (SemanticOrdered [signature, SemanticAtom source])
          Right $ ConditionallyCheckedRecord identity functionIdentity
            (recordDispositionOwner trace) (recordDispositionReturnedBinder trace) plan
    _ -> Left RecordSourceOutsideFragment
  where
    declaration = locatedValue . grammarV1Declaration . locatedValue

eliminateCheckedRecord
  :: ConditionallyCheckedRecord -> ResourceContext -> Either RecordSourceError ResourceContext
eliminateCheckedRecord (ConditionallyCheckedRecord identity _ owner _ plan) =
  mapLeft RecordNativeRejection .
    consumeNominalRecordFields (identityDeclarationKey identity)
      (grammarV1ResolvedBinderCoreName owner) plan

data DeclarationSite = DeclarationSite Text DeclarationKey Int Int

siteKey :: DeclarationSite -> DeclarationKey
siteKey (DeclarationSite _ key _ _) = key

-- Canonical rows are TAB-delimited. Offsets are zero-based Unicode code-point
-- offsets, with an exclusive end, as emitted by the original lexer.
parseManifest :: Text -> Text -> Text -> Either RecordSourceError (DeclarationSite, DeclarationSite)
parseManifest path digest manifest =
  case map (Text.splitOn "\t") (Text.splitOn "\n" manifest) of
    [ ["phil-record-origin-v1", "grammar-v1", file, commitment]
      , ["record", recordId, recordKey, recordStart, recordEnd]
      , ["fn", functionId, functionKey, functionStart, functionEnd]
      , [""] ] -> do
        unless (file == path && commitment == digest) $ Left SelectedOriginMismatch
        record <- site recordId recordKey recordStart recordEnd
        fn <- site functionId functionKey functionStart functionEnd
        unless (recordId /= functionId && recordKey /= functionKey) $ Left MalformedRecordManifest
        Right (record, fn)
    _ -> Left MalformedRecordManifest
  where
    site identifier key start end
      | valid identifier && valid key
      , Just first <- offset start
      , Just lastPoint <- offset end
      , first < lastPoint = Right (DeclarationSite identifier (DeclarationKey key) first lastPoint)
      | otherwise = Left MalformedRecordManifest
    offset value = do
      n <- readMaybe (Text.unpack value)
      if n >= (0 :: Int) && Text.pack (show n) == value then Just n else Nothing
    valid value = not (Text.null value) && Text.all
      (\c -> c >= 'a' && c <= 'z' || c >= '0' && c <= '9' || c == '.' || c == '-') value

matchesSite :: Text -> DeclarationSite -> Located a -> Bool
matchesSite path (DeclarationSite _ _ start end) (Located (SourceSpan lo hi) _) =
  sourcePointFile lo == path && sourcePointFile hi == path
    && sourcePointOffset lo == start && sourcePointOffset hi == end

checkReferences :: GrammarV1RecordDecl -> GrammarV1FunctionDecl -> Either RecordSourceError ()
checkReferences record fn =
  case (grammarV1FunctionTermParams fn, body) of
    ([Located _ parameter], Located _ (GrammarV1LetStatement pattern' _) : _) ->
      case (locatedValue (grammarV1TermParamType parameter), locatedValue pattern') of
        (GrammarV1NamedType reference, GrammarV1RecordPattern (Located _ qualified) _)
          | grammarV1StaticReferenceArguments reference == []
          , grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == expected
          , grammarV1QualifiedNameParts qualified == expected -> Right ()
        _ -> Left RecordNominalReferenceMismatch
    _ -> Left RecordSourceOutsideFragment
  where
    expected = [locatedValue (grammarV1RecordName record)]
    body = grammarV1BlockStatements (locatedValue (grammarV1FunctionBody fn))

sourceDigest :: Bytes.ByteString -> Text
sourceDigest = Text.pack . concatMap hex . Bytes.unpack . SHA256.hash
  where
    hex byte = let digits = showHex byte "" in if byte < 16 then '0' : digits else digits

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
