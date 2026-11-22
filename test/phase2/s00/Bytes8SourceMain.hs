{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as Bytes
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Numeric (showHex)
import Phil.Core.Static (DeclarationKey (..), identityDeclarationKey)
import Phil.Core.Syntax (Control (..), RefTerm (..), Ty (..))
import Phil.Experimental.Bytes8.Source
import Phil.Surface.Check.Engine (BorrowTraceCheckpoint (..), BorrowTracePhase (..))
import Phil.Surface.Check.Types (RejectionClass (..), SurfaceCheckError (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.BorrowResourceSurface (GrammarV1BorrowResourceError (..))
import Phil.Surface.GrammarV1.Parser
  (GrammarV1QualifiedName (..), GrammarV1StaticReference (..), GrammarV1Type (..))
import Phil.Surface.Syntax (Located (..), SourcePoint (..), SourceSpan (..))

main :: IO ()
main = do
  original <- readSource originalPin
  escaping <- readSource escapePin
  checked <- either (fail . show) pure (checkSelectedSource OriginalLoan originalPin original)
  let body = observeCheckedBody checked
      owner = bodyOwner body
      view = bodyView body
  pass "sealed original, exact owner/view/return and production checkpoints" $
    bodyOrigin body == originalPin &&
    identityDeclarationKey (bodyIdentity body) == originDeclarationKey originalPin &&
    spanOffsets (bodyDeclarationSpan body) == (0, 104) &&
    spanOffsets (bodyReturnSpan body) == (95, 100) &&
    sourcePointFile (sourceSpanStart (bodyReturnSpan body)) == originPath originalPin &&
    owner == bodyReturnedOwner body &&
    grammarV1ResolvedBinderKey owner /= grammarV1ResolvedBinderKey view &&
    bodyTerminal body == Return (TyBytes (RefNat 8)) &&
    map tracePhase (bodyCheckpoints body) ==
      [TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False, TraceLoanClosed, TraceOwnerReturned]

  let fabricatedReport = body {bodyReturnedOwner = view, bodyCheckpoints = []}
  pass "copying or editing a report leaves sealed body and contract STOP intact" $
    fabricatedReport /= observeCheckedBody checked &&
    case requireContractAuthority checked of
      Left (UnresolvedContractAuthority identity contract) ->
        identity == bodyIdentity body && contract == bodyContractReference body &&
        locatedValue contract ==
          GrammarV1NamedType (GrammarV1StaticReference (GrammarV1QualifiedName ["C"]) [])
      Right _ -> False

  case checkSelectedSource EscapeControl escapePin escaping of
    Left (ResourceRejected (GrammarV1BorrowResourceProductionError err)) ->
      pass "production BorrowEscape: shared view escapes its lexical scope" $
        surfaceErrorClass err == BorrowEscape &&
        surfaceErrorDetail err == "shared view escapes its lexical scope"
    other -> fail ("expected production BorrowEscape, got " <> outcome other)

  let reject label origin bytes expected =
        expect label expected (checkSelectedSource OriginalLoan origin bytes)
      replace old new = Text.encodeUtf8 (Text.replace old new (Text.decodeUtf8 original))
      rehashed bytes = originalPin {originSHA256 = digest bytes}
      rejectsRehash label bytes expected = reject label (rehashed bytes) bytes expected

  reject "trailing byte mutation" originalPin (original <> "\n") (== SourceBytesMismatch)
  reject "wrong selected path" (originalPin {originPath = originPath escapePin}) original
    (== SourcePathMismatch)
  reject "wrong declaration key" (originalPin {originDeclarationKey = originDeclarationKey escapePin})
    original (== DeclarationKeyMismatch)
  reject "wrong occurrence start" (originalPin {originStart = 1}) original
    (== DeclarationOccurrenceMismatch)
  reject "wrong occurrence end" (originalPin {originEnd = 103}) original
    (== DeclarationOccurrenceMismatch)
  reject "wrong grammar revision" (originalPin {originGrammarBlob = "forged"}) original
    (== SourceRevisionMismatch)
  reject "wrong parser revision" (originalPin {originParserBlob = "forged"}) original
    (== SourceRevisionMismatch)
  reject "wrong digest claim" (originalPin {originSHA256 = originSHA256 escapePin}) original
    (== SourceBytesMismatch)
  reject "negative bytes replayed under positive selection" originalPin escaping (== SourceBytesMismatch)
  expect "positive bytes replayed under negative selection" (== SourceBytesMismatch)
    (checkSelectedSource EscapeControl escapePin original)
  rejectsRehash "self-consistent rehashed sidecar" (original <> "\n") (== SourceBytesMismatch)
  rejectsRehash "substituted contract reference" (replace "satisfies C" "satisfies D")
    (== SourceBytesMismatch)
  rejectsRehash "extra declaration" (original <> replace "fn loan" "fn copy") (== UnsupportedSource)
  rejectsRehash "swapped declaration" (replace "fn loan" "fn copy") (== UnsupportedSource)
  rejectsRehash "recursive declaration" (replace "fn loan" "recursive fn loan") (== UnsupportedSource)
  rejectsRehash "generic declaration" (replace "loan(" "loan[T : Type](") (== UnsupportedSource)
  rejectsRehash "requirement" (replace "loan(" "loan requires { callable x : C; }(")
    (== UnsupportedSource)
  rejectsRehash "import" ("import Other;\n" <> original) (== UnsupportedSource)
  rejectsRehash "wrong owner parameter" (replace "owner" "other") (== UnsupportedSource)
  rejectsRehash "wrong byte extent" (replace "Bytes[8]" "Bytes[9]") (== UnsupportedSource)
  rejectsRehash "wrong intrinsic mode" (replace "Bytes[8]" "U8") (== UnsupportedSource)
  rejectsRehash "named type alias" (replace "Bytes[8]" "Octets") (== UnsupportedSource)
  rejectsRehash "wrong return binder" (replace "return owner" "return view") (== SourceBytesMismatch)
  rejectsRehash "wrong borrow owner" (replace "borrow owner" "borrow other") (== SourceBytesMismatch)
  rejectsRehash "wrong view name" (replace "as view" "as other") (== SourceBytesMismatch)
  rejectsRehash "reordered statements"
    (replace "  borrow owner as view { unit; };\n  return owner;" "  return owner;\n  borrow owner as view { unit; };")
    (== SourceBytesMismatch)
  reject "invalid UTF-8" originalPin (original <> Bytes.singleton 255)
    (== MalformedSourceEncoding)
  reject "malformed source" originalPin (Bytes.take 10 original)
    (\err -> case err of MalformedSource _ -> True; _ -> False)

originalPin, escapePin :: SourceOrigin
originalPin = testPin "loan.phil" "decl.phase2.s00.l0.e1.loan"
  "02732835529e2b4de7a3dec878c6bf8e5532e7f587fbaa85eac79e4405b5de0a"
escapePin = testPin "loan-escape.phil" "decl.phase2.s00.l0.e1.escape-control"
  "9224b9580607f977b9cc6780503a2e49b235e5eba9ec61d0364aa820308c8c20"

testPin :: Text.Text -> Text.Text -> Text.Text -> SourceOrigin
testPin name key hash = SourceOrigin ("test/phase2/s00/fixtures/" <> name) hash
  (DeclarationKey key) 0 104
  "933fa282487eeae6ba224d68a8d49b9691c4e1dd" "70aabbf9ea95271b1ed6852dfe5ace049bbda959"

readSource :: SourceOrigin -> IO Bytes.ByteString
readSource pin = do
  bytes <- Bytes.readFile (Text.unpack (originPath pin))
  pass ("independent fixture pin " <> Text.unpack (originPath pin)) (digest bytes == originSHA256 pin)
  pure bytes

digest :: Bytes.ByteString -> Text.Text
digest = Text.pack . concatMap hex . Bytes.unpack . SHA256.hash
  where
    hex byte = let digits = showHex byte "" in if byte < 16 then '0' : digits else digits

spanOffsets :: SourceSpan -> (Int, Int)
spanOffsets (SourceSpan start end) = (sourcePointOffset start, sourcePointOffset end)

pass :: String -> Bool -> IO ()
pass label ok = do
  unless ok (fail label)
  putStrLn ("PASS " <> label)

expect :: String -> (SourceError -> Bool) -> Either SourceError CheckedBody -> IO ()
expect label predicate result = case result of
  Left err | predicate err -> putStrLn ("PASS " <> label <> " -- " <> show err)
  _ -> fail (label <> " -- unexpected result " <> outcome result)

outcome :: Either SourceError CheckedBody -> String
outcome = either show (const "sealed body")
