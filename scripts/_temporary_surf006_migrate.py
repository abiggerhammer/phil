from pathlib import Path

digest = "1bc73beb296475f96d739181c0a7609eaf53a61362b2aa0cf7bd7184d06e67ac"
revision = f"sha256:{digest}"

path = Path('src/Phil/Surface/Lineage.hs')
text = path.read_text()
text = text.replace(
    '  , ProcessLineageSiteId (..)\n  , PortableSourceUnit (..)\n',
    '  , ProcessLineageSiteId (..)\n  , GrammarRevision (..)\n  , canonicalGrammarRevisionV1\n  , PortableSourceUnit (..)\n',
    1)
text = text.replace(
    '  , decodePortableSourceBundle\n  , resolveSourceBundleLineage\n',
    '  , decodePortableSourceBundle\n  , decodePortableSourceBundleForGrammar\n  , resolveSourceBundleLineage\n',
    1)
text = text.replace(
    'import Data.Char (isAlphaNum, isControl, isLetter, isSpace)\n',
    'import Data.Char (isAlphaNum, isControl, isDigit, isLetter, isSpace)\n',
    1)
marker = '''newtype ProcessLineageSiteId = ProcessLineageSiteId { unProcessLineageSiteId :: Text }
  deriving (Eq, Ord, Show)
'''
assert text.count(marker) == 1, text.count(marker)
text = text.replace(marker, marker + f'''
-- | Exact concrete-grammar identity carried by a portable SourceBundle.
-- Grammar compatibility is not inferred from this value: Phase 1 accepts only
-- the exact revision selected by the current front end.
newtype GrammarRevision = GrammarRevision {{ unGrammarRevision :: Text }}
  deriving (Eq, Ord, Show)

canonicalGrammarRevisionV1 :: GrammarRevision
canonicalGrammarRevisionV1 = GrammarRevision "{revision}"
''', 1)
old = '''data PortableSourceBundle = PortableSourceBundle
  { portableSelectedProgramRoot :: Text
'''
assert text.count(old) == 1, text.count(old)
text = text.replace(old, '''data PortableSourceBundle = PortableSourceBundle
  { portableGrammarRevision :: GrammarRevision
  , portableSelectedProgramRoot :: Text
''', 1)
old = '''  = InvalidBundleHeader Text
  | MissingSelectedProgramRoot
'''
assert text.count(old) == 1, text.count(old)
text = text.replace(old, '''  = InvalidBundleHeader Text
  | MissingGrammarRevision
  | DuplicateGrammarRevision GrammarRevision GrammarRevision
  | MalformedGrammarRevision Text
  | IncompatibleGrammarRevision GrammarRevision GrammarRevision
  | MissingSelectedProgramRoot
''', 1)
old = '''portableHeader :: Text
portableHeader = "PHIL-SOURCE-BUNDLE-LINEAGE-V1"

data DecodeState = DecodeState
  { decodeRoot :: Maybe Text
'''
assert text.count(old) == 1, text.count(old)
text = text.replace(old, '''portableHeader :: Text
portableHeader = "PHIL-SOURCE-BUNDLE-LINEAGE-V1"

validateGrammarRevision :: Text -> Either LineageError GrammarRevision
validateGrammarRevision raw =
  case Text.stripPrefix "sha256:" raw of
    Just digestValue
      | raw == Text.strip raw
      , Text.length digestValue == 64
      , Text.all isLowerHex digestValue -> Right (GrammarRevision raw)
    _ -> Left (MalformedGrammarRevision raw)
  where
    isLowerHex character = isDigit character || (character >= 'a' && character <= 'f')

data DecodeState = DecodeState
  { decodeGrammar :: Maybe GrammarRevision
  , decodeRoot :: Maybe Text
''', 1)
old = '''emptyDecodeState = DecodeState
  { decodeRoot = Nothing
'''
assert text.count(old) == 1, text.count(old)
text = text.replace(old, '''emptyDecodeState = DecodeState
  { decodeGrammar = Nothing
  , decodeRoot = Nothing
''', 1)
start = text.index('-- | Decode the bounded, line-oriented Phase-1 conformance/handoff fixture.')
end = text.index('\ndecodeRecord :: DecodeState', start)
replacement = '''-- | Decode the bounded, line-oriented Phase-1 conformance/handoff fixture.
-- This is test/interchange infrastructure, not permanent Phil source syntax or
-- a commitment to a long-term stable-key wire encoding.
decodePortableSourceBundle :: Text -> Either LineageError PortableSourceBundle
decodePortableSourceBundle = decodePortableSourceBundleForGrammar canonicalGrammarRevisionV1

-- | Decode for one explicitly selected concrete-grammar revision. Phase 1 has
-- no implicit migration or compatibility relation: a different exact digest is
-- an incompatible input and fails before source lineage can be resolved.
decodePortableSourceBundleForGrammar
  :: GrammarRevision
  -> Text
  -> Either LineageError PortableSourceBundle
decodePortableSourceBundleForGrammar expectedGrammar input =
  case Text.lines input of
    [] -> Left (InvalidBundleHeader "")
    header : records
      | Text.strip header /= portableHeader ->
          Left (InvalidBundleHeader (Text.strip header))
      | otherwise -> do
          decoded <- foldM decodeRecord emptyDecodeState (zip [2 ..] records)
          grammarRevision <- maybe (Left MissingGrammarRevision) Right (decodeGrammar decoded)
          if grammarRevision == expectedGrammar
            then Right ()
            else Left (IncompatibleGrammarRevision expectedGrammar grammarRevision)
          root <- maybe (Left MissingSelectedProgramRoot) Right (decodeRoot decoded)
          Right PortableSourceBundle
            { portableGrammarRevision = grammarRevision
            , portableSelectedProgramRoot = root
            , portableSourceUnits = reverse (decodeUnits decoded)
            , portableInstanceLineage = reverse (decodeInstances decoded)
            , portableProcessLineage = reverse (decodeProcesses decoded)
            }
'''
text = text[:start] + replacement + text[end:]
anchor = '''      case Text.splitOn "\\t" rawLine of
        ["root", root] ->
'''
assert text.count(anchor) == 1, text.count(anchor)
text = text.replace(anchor, '''      case Text.splitOn "\\t" rawLine of
        ["grammar", rawRevision] -> do
          revisionValue <- validateGrammarRevision (Text.strip rawRevision)
          case decodeGrammar state of
            Nothing -> Right state { decodeGrammar = Just revisionValue }
            Just existing -> Left (DuplicateGrammarRevision existing revisionValue)
        ["root", root] ->
''', 1)
path.write_text(text)

for fixture in [
    Path('test/fixtures/phase1/surf010-inline.bundle'),
    Path('test/fixtures/phase1/surf010-metadata.bundle'),
]:
    lines = fixture.read_text().splitlines()
    assert lines[0] == 'PHIL-SOURCE-BUNDLE-LINEAGE-V1'
    if len(lines) < 2 or not lines[1].startswith('grammar\t'):
        lines.insert(1, 'grammar\t' + revision)
    fixture.write_text('\n'.join(lines) + '\n')

path = Path('test/Phase1PortableSourceLineageMain.hs')
text = path.read_text()
old = '''  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "root\\tprogram:test"
'''
assert text.count(old) == 1, text.count(old)
path.write_text(text.replace(old, '''  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "grammar\\t" <> unGrammarRevision canonicalGrammarRevisionV1
  , "root\\tprogram:test"
''', 1))

Path('test/Phase1GrammarRevisionBindingMain.hs').write_text(r'''{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as ByteString
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Data.Word (Word8)
import Numeric (showHex)
import Phil.Surface.Lineage
import System.Exit (exitFailure)

main :: IO ()
main = do
  fixture <- TextIO.readFile "test/fixtures/phase1/surf010-inline.bundle"
  results <- sequence
    [ testIO "SURF-006 canonical revision is the exact Grammar-v1 SHA-256" canonicalRevisionMatchesGrammar
    , test "SURF-006 exact grammar revision is admitted" (exactRevisionAccepted fixture)
    , test "SURF-006 missing grammar revision fails closed" missingRevisionRejects
    , test "SURF-006 duplicate grammar revision fails closed" duplicateRevisionRejects
    , test "SURF-006 malformed grammar revision fails closed" malformedRevisionRejects
    , test "SURF-006 incompatible exact grammar revision fails closed" incompatibleRevisionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

canonicalRevisionMatchesGrammar :: IO (Either String ())
canonicalRevisionMatchesGrammar = do
  grammarBytes <- ByteString.readFile "grammar/phase1-surface.ebnf"
  pure $ assert
    (revisionForBytes grammarBytes == canonicalGrammarRevisionV1)
    "canonicalGrammarRevisionV1 does not match grammar/phase1-surface.ebnf"

exactRevisionAccepted :: Text -> Either String ()
exactRevisionAccepted source = case decodePortableSourceBundle source of
  Left errorValue -> Left ("exact revision rejected: " <> show errorValue)
  Right bundle -> assert
    (portableGrammarRevision bundle == canonicalGrammarRevisionV1)
    "decoded bundle did not retain the canonical grammar revision"

missingRevisionRejects :: Either String ()
missingRevisionRejects = expectError isMissing $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    isMissing MissingGrammarRevision = True
    isMissing _ = False

duplicateRevisionRejects :: Either String ()
duplicateRevisionRejects = expectError isDuplicate $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , grammarRecord canonicalGrammarRevisionV1
  , grammarRecord canonicalGrammarRevisionV1
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    isDuplicate DuplicateGrammarRevision {} = True
    isDuplicate _ = False

malformedRevisionRejects :: Either String ()
malformedRevisionRejects = expectError isMalformed $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , "grammar\tsha256:ABC"
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    isMalformed MalformedGrammarRevision {} = True
    isMalformed _ = False

incompatibleRevisionRejects :: Either String ()
incompatibleRevisionRejects = expectError isMismatch $ Text.unlines
  [ "PHIL-SOURCE-BUNDLE-LINEAGE-V1"
  , grammarRecord incompatible
  , "root\tprogram:test"
  , "unit\tunit.test\tsite.test\tdecl:test\trecord Test {}"
  ]
  where
    incompatible = GrammarRevision ("sha256:" <> Text.replicate 64 "0")
    isMismatch (IncompatibleGrammarRevision expected actual) =
      expected == canonicalGrammarRevisionV1 && actual == incompatible
    isMismatch _ = False

expectError :: (LineageError -> Bool) -> Text -> Either String ()
expectError predicate source = case decodePortableSourceBundle source of
  Left errorValue
    | predicate errorValue -> Right ()
    | otherwise -> Left ("unexpected revision error: " <> show errorValue)
  Right bundle -> Left ("expected revision rejection, decoded: " <> show bundle)

grammarRecord :: GrammarRevision -> Text
grammarRecord revisionValue = "grammar\t" <> unGrammarRevision revisionValue

revisionForBytes :: ByteString.ByteString -> GrammarRevision
revisionForBytes bytes = GrammarRevision
  ("sha256:" <> Text.pack (concatMap hexByte (ByteString.unpack (SHA256.hash bytes))))

hexByte :: Word8 -> String
hexByte value = case showHex value "" of
  [digit] -> ['0', digit]
  digits -> digits

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
''')

path = Path('.github/workflows/phase1-surface-grammar.yml')
text = path.read_text()
grammar_path = "      - 'src/Phil/Surface/GrammarV1/**'\n"
assert text.count(grammar_path) == 2, text.count(grammar_path)
text = text.replace(grammar_path, grammar_path + "      - 'src/Phil/Surface/Lineage.hs'\n      - 'test/Phase1GrammarRevisionBindingMain.hs'\n      - 'test/fixtures/phase1/*.bundle'\n")
step_marker = '''      - name: Check Grammar-v1 determinacy shape pressure
        run: cabal exec -- runghc -Wall -Werror -isrc test/Phase1GrammarV1DeterminacyMain.hs
'''
assert text.count(step_marker) == 1, text.count(step_marker)
text = text.replace(step_marker, '''      - name: Check exact Grammar-v1 source-bundle revision binding
        run: cabal exec -- runghc -Wall -Werror -isrc test/Phase1GrammarRevisionBindingMain.hs

''' + step_marker, 1)
path.write_text(text)

path = Path('docs/phase-1/surface-grammar-v1.md')
text = path.read_text()
old = 'A future incompatible syntax change must be explicit rather than silently changing parser behavior.\n'
assert text.count(old) == 1, text.count(old)
new = '''Portable SourceBundle interchange therefore carries a required exact grammar-revision record, `grammar\\tsha256:<64-lowercase-hex>`. The current Phase 1 front end accepts only `canonicalGrammarRevisionV1`, which is mechanically checked against the SHA-256 of `grammar/phase1-surface.ebnf`. Missing, duplicate, malformed, or incompatible revision metadata fails closed before source lineage resolution or parsing. This binding is SourceBundle/front-end metadata, not `.phil` syntax, and Phase 1 defines no implicit cross-revision compatibility relation.

A future incompatible syntax change must be explicit rather than silently changing parser behavior.
'''
path.write_text(text.replace(old, new, 1))
