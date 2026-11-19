{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as Bytes
import qualified Data.ByteString.Char8 as ASCII
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Numeric (showHex)
import qualified Phil.Core.Context as Core
import Phil.Core.DataDestruction
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Core.Value (EqualityBoundary (..), compareTypes)
import Phil.Surface.Check (SurfaceEnvironment (..), SurfaceCheckError (..), RejectionClass (..), checkSurfaceComponent, emptySurfaceEnvironment)
import Phil.Surface.Check.Support (messageMode)
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import Phil.Surface.GrammarV1.BinderScope
import Phil.Surface.GrammarV1.RecordSourceIdentity

main :: IO ()
main = do
  let path = "test/fixtures/fsem01-rec01-source-record-v1/accepted-full.phil"
      key = DeclarationKey "decl.fsem01.rec02a.packet"
      fnKey = DeclarationKey "decl.fsem01.rec02a.unpack"
  source <- Bytes.readFile (Text.unpack path)
  manifest <- Bytes.readFile "test/fixtures/fsem01-rec02a-record-origin-v1/accepted.tsv"
  assert "original source and independent manifest pins"
    (digest source == "5a7853282fdf151245a8def87242e1edeabd7253f97de023bbc822b1e57b3593"
      && digest manifest == "7c7e3e79fe8d3b2dc9b0343c25ec0723585a366b4568a510e341f076fca4c9c8")
  let selected = (source,manifest)
      check = checkSelectedRecordSource emptyStaticContext path
      checkPinned = check selected
      reject expected result = case result of
        Left actual -> actual == expected
        Right _ -> False
      withManifest transform = let changed = (source,transform manifest) in check changed changed
      field = OwnedField (Name "payload") Linear (TyBytes (RefNat 8))
      tag = OwnedField (Name "tag") Unrestricted (TyUInt 8)
      flag = OwnedField (Name "flag") Unrestricted TyBool
  checked <- require (checkPinned selected)
  let owner = grammarV1ResolvedBinderCoreName (checkedOwner checked)
      returned = grammarV1ResolvedBinderCoreName (checkedReturnedBinder checked)
      ty = checkedOwnerType checked
      revision = identityInterfaceRevision (checkedRecordIdentity checked)
      withOwner mode ownerType = require $ Core.insertBinding mode owner ownerType Core.emptyContext
  assert "distinct persisted identities and source binder roots"
    (identityDeclarationKey (checkedRecordIdentity checked) == key
      && identityDeclarationKey (checkedFunctionIdentity checked) == fnKey
      && fnKey == grammarV1BinderDeclarationRoot (grammarV1ResolvedBinderKey (checkedOwner checked)))
  original <- withOwner Linear ty
  context <- require $ Core.insertBinding Affine (Name "spectator") TyUnit original
  successors <- require (eliminateCheckedRecord checked context)
  assert "native successor, unrestricted fields, affine frame and empty loans"
    (Core.linearBindings successors == Map.singleton returned (ownedFieldType field)
      && sort (Map.elems (Core.unrestrictedBindings successors)) == sort [TyBool,TyUInt 8]
      && Core.affineBindings successors == Core.affineBindings context
      && Core.sharedLoans successors == Core.sharedLoans context)
  (returnedType, terminal) <- require (Core.consumeLinear returned successors)
  (_, complete) <- require (Core.consumeAffine (Name "spectator") terminal)
  assert "terminal return completes and cannot be repeated"
    (returnedType == ownedFieldType field && Core.ensureComplete complete == Right ()
      && Core.consumeLinear returned terminal == Left (Core.UnknownBinding returned))
  assert "stale owner"
    (reject (RecordNativeRejection (DataDestructionContextError (Core.UnknownBinding owner)))
      (eliminateCheckedRecord checked successors))
  loaned <- require (Core.startSharedLoan owner context)
  assert "active loan"
    (reject (RecordNativeRejection (DataDestructionContextError (Core.OwnerBorrowed owner)))
      (eliminateCheckedRecord checked loaned))
  collision <- require (Core.insertBinding Unrestricted returned TyUnit context)
  assert "destination collision"
    (reject (RecordNativeRejection (DataDestructionContextError (Core.DuplicateBinding returned)))
      (eliminateCheckedRecord checked collision))
  let mismatch = RecordNativeRejection (NominalRecordOwnerMismatch owner)
      otherKey = TyRecordNominal (DeclarationKey "decl.other.packet") revision
      otherRevision = TyRecordNominal key (InterfaceRevision "wrong-revision")
  mapM_ (\(mode,wrong) -> do
      wrongContext <- withOwner mode wrong
      assert "wrong native owner" (reject mismatch (eliminateCheckedRecord checked wrongContext)))
    [(Unrestricted,ty), (Affine,ty), (Linear,otherKey), (Linear,otherRevision), (Linear,TyOpaque "Packet")
    , (Linear,ownedFieldType field)]
  let refined = TyRefined (Name "self") ty (Equal (RefNat 0) (RefNat 0))
  parsed <- require (parseSurfaceFile "nominal-alias.phil" "component Drop(p: Packet) {}")
  case parsed of
    SurfaceFile [component] -> mapM_ (\alias ->
      let environment = (emptySurfaceEnvironment emptyStaticContext)
            { surfaceTypeAliases = Map.singleton "Packet" alias }
      in assert "legacy alias and payload mode reject bare and refined nominal types"
          (messageMode alias == Nothing &&
            case checkSurfaceComponent environment component of
              Left err -> surfaceErrorClass err == TypeMismatch
                && surfaceErrorDetail err == "nominal record requires a checked structural mode"
              Right _ -> False)) [ty,refined]
    _ -> fail "expected one parsed component"
  refinedOwner <- withOwner Linear refined
  assert "refined nominal rejects legacy field elimination"
    (consumeAggregateFields owner [field] [(ownedFieldName field,FieldBound)] refinedOwner
      == Left (NominalRecordRequiresTypedElimination owner))
  wrongOwner <- withOwner Linear otherKey
  assert "missing Linear disposition precedes wrong-owner lookup"
    (consumeNominalRecordFields key owner [(field,Nothing)] wrongOwner
      == Left (MissingLinearFieldDisposition (ownedFieldName field)))
  assert "changed field mode is rejected"
    (consumeNominalRecordFields key owner [(tag {ownedFieldMode = Affine},Nothing),(field,Just returned)] context
      == Left NominalRecordSchemaUnsupported)
  unrelated <- require (Core.insertBinding Linear (Name "other") ty Core.emptyContext)
  assert "same type under unrelated owner"
    (reject (RecordNativeRejection (DataDestructionContextError (Core.UnknownBinding owner)))
      (eliminateCheckedRecord checked unrelated))
  assert "nominal equality and legacy rejection"
    (compareTypes ty ty == DefinitionallyEqual
      && all ((/= DefinitionallyEqual) . compareTypes ty) [otherKey,otherRevision,TyOpaque "Packet"]
      && consumeAggregateFields owner [field] [(ownedFieldName field,FieldBound)] context
        == Left (NominalRecordRequiresTypedElimination owner))
  let consume fields = consumeNominalRecordFields key owner fields context
  assert "valid dispositions over changed schema cannot consume original owner"
    (all (== Left (NominalRecordOwnerMismatch owner))
      [ consume [(tag,Nothing),(flag,Nothing),(field,Just returned)]
      , consume [(tag {ownedFieldType = TyUInt 16},Nothing),(field,Just returned),(flag,Nothing)]
      , consume [(tag {ownedFieldName = Name "renamed"},Nothing),(field,Just returned),(flag,Nothing)]
      ])
  assert "Linear omission and duplicate destinations"
    (consume [(tag,Nothing),(field,Nothing),(flag,Nothing)]
      == Left (MissingLinearFieldDisposition (ownedFieldName field))
      && consume [(tag,Just returned),(field,Just returned),(flag,Nothing)]
      == Left (DuplicateOwnedField returned))
  assert "selected bytes and selected path"
    (reject SelectedOriginMismatch (checkPinned (source <> "\n",manifest))
      && reject SelectedOriginMismatch (checkPinned (source,replace "packet-site" "copied-site" manifest))
      && reject SelectedOriginMismatch (checkSelectedRecordSource emptyStaticContext "other.phil" selected selected))
  assert "distinct sites, kinds and exact spans"
    (reject MalformedRecordManifest (withManifest (replace "unpack-site" "packet-site"))
      && reject MalformedRecordManifest (withManifest (replace "decl.fsem01.rec02a.unpack" "decl.fsem01.rec02a.packet"))
      && reject MalformedRecordManifest (withManifest (replace "\nfn\t" "\nrecord\t"))
      && reject RecordDeclarationSitesMismatch (withManifest (replace "\t60\t179" "\t59\t179")))
  let changed = replace "packet : Packet" "packet : Foobar" source
      changedManifest = replace (ASCII.pack (digest source)) (ASCII.pack (digest changed)) manifest
  assert "independently selected source with wrong parameter reference"
    (reject RecordNominalReferenceMismatch (check (changed,changedManifest) (changed,changedManifest)))
  let checkSelected nextSource =
        let nextManifest = replace (ASCII.pack (digest source)) (ASCII.pack (digest nextSource)) manifest
        in check (nextSource,nextManifest) (nextSource,nextManifest)
  (header, recordRow, functionRow) <- case ASCII.lines manifest of
    [a,b,c] -> pure (a,b,c)
    _ -> fail "expected three manifest rows"
  mapM_ (\(label, expected, manifestMutation) ->
      assert label (reject expected (withManifest manifestMutation)))
    [ ("stale source commitment", SelectedOriginMismatch, replace (ASCII.pack (digest source)) "stale")
    , ("unsupported format", MalformedRecordManifest, replace "phil-record-origin-v1" "phil-record-origin-v2")
    , ("unsupported grammar", MalformedRecordManifest, replace "grammar-v1" "grammar-v2")
    , ("omitted row", MalformedRecordManifest, const (ASCII.unlines [header, recordRow]))
    , ("additional row", MalformedRecordManifest, (<> functionRow <> "\n"))
    , ("swapped rows", MalformedRecordManifest, const (ASCII.unlines [header, functionRow, recordRow]))
    , ("reversed span", MalformedRecordManifest, replace "\t60\t179" "\t179\t60")
    , ("nested span", RecordDeclarationSitesMismatch, replace "\t60\t179" "\t1\t58")
    , ("phantom end offset", RecordDeclarationSitesMismatch, replace "\t60\t179" "\t60\t180")
    , ("manifest UTF-8", MalformedRecordManifest, (<> Bytes.singleton 255))
    ]
  assert "source UTF-8" (reject MalformedRecordSourceEncoding (checkSelected (Bytes.cons 255 source)))
  assert "malformed source syntax" $ case checkSelected (replace "record" "recxrd" source) of
    Left (MalformedRecordSource _) -> True
    _ -> False
  assert "wrong pattern constructor"
    (reject RecordNominalReferenceMismatch (checkSelected (replace "let Packet" "let Foobar" source)))
  let wrongKey = replace "decl.fsem01.rec02a.packet" "decl.fsem01.rec02a.other" manifest
  assert "a copied declaration's different key cannot replace the independently selected manifest"
    (reject SelectedOriginMismatch (checkPinned (source,wrongKey)))
  reselected <- require (check (source,wrongKey) (source,wrongKey))
  assert "an independently selected different key gives a distinct nominal type"
    (compareTypes ty (checkedOwnerType reselected) == IncompatibleTypes)
  let aliasSource = replace "let Packet { tag, payload, flag } = packet;\n  return payload;"
        "let Packet { tag, payload = b, flag } = packet;\n  return b;" source
      aliasManifest = replace "\t60\t179" "\t60\t177" $
        replace (ASCII.pack (digest source)) (ASCII.pack (digest aliasSource)) manifest
  aliased <- require (check (aliasSource,aliasManifest) (aliasSource,aliasManifest))
  assert "an explicit alpha alias preserves the nominal schema and binder identity"
    (checkedOwnerType aliased == ty
      && grammarV1ResolvedBinderCoreName (checkedReturnedBinder aliased) == returned)
  _ <- require (eliminateCheckedRecord aliased context)
  putStrLn "REC-02A native record origin, nominal identity and owner elimination passed"

replace :: Bytes.ByteString -> Bytes.ByteString -> Bytes.ByteString -> Bytes.ByteString
replace from to input =
  let (prefix, suffix) = Bytes.breakSubstring from input
  in if Bytes.null suffix then input else prefix <> to <> Bytes.drop (Bytes.length from) suffix

digest :: Bytes.ByteString -> String
digest = concatMap hex . Bytes.unpack . SHA256.hash
  where hex byte = let digits = showHex byte "" in if byte < 16 then '0' : digits else digits

assert :: String -> Bool -> IO ()
assert label condition = unless condition (fail label)

require :: Show e => Either e a -> IO a
require = either (fail . show) pure
