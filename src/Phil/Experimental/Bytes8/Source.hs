{-# LANGUAGE OverloadedStrings #-}

-- | Experimental PH2-S00-L0-E1 source evidence. The only selections are
-- the independently pinned issue witness and its diagnostic control.
module Phil.Experimental.Bytes8.Source
  ( SelectedSource (..)
  , SourceOrigin (..)
  , SourceError (..)
  , CheckedBody
  , BodyObservation (..)
  , ContractStop (..)
  , checkSelectedSource
  , observeCheckedBody
  , requireContractAuthority
  ) where

import Control.Monad (unless)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as Bytes
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Void (Void)
import Numeric (showHex)
import Phil.Core.Static
  ( DeclarationDescriptor (..)
  , DeclarationIdentity
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  , emptyStaticContext
  )
import Phil.Core.Syntax (Control (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint
  , BorrowTracePhase (..)
  , BorrowTraceResourceObservation (..)
  , observeBorrowTraceResource
  )
import Phil.Surface.Check.Types (checkedTerminalControls)
import Phil.Surface.GrammarV1.BinderScope
  (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError
  , GrammarV1BorrowResourceTrace (..)
  , grammarV1CheckedBorrowResourceFunction
  , grammarV1CheckedBorrowResourceFunctionTrace
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1ParseDiagnostic
  , GrammarV1QualifiedName (..)
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TermParam (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.Syntax (Located (..), SourcePoint (..), SourceSpan (..))

data SelectedSource = OriginalLoan | EscapeControl
  deriving (Eq, Show)

-- | Untrusted origin claims. This record cannot introduce a selection.
-- The range is zero-based Unicode code points with an exclusive end.
data SourceOrigin = SourceOrigin
  { originPath :: Text
  , originSHA256 :: Text
  , originDeclarationKey :: DeclarationKey
  , originStart :: Int
  , originEnd :: Int
  , originGrammarBlob :: Text
  , originParserBlob :: Text
  }
  deriving (Eq, Show)

data SourceError
  = MalformedSourceEncoding
  | MalformedSource GrammarV1ParseDiagnostic
  | UnsupportedSource
  | SourcePathMismatch
  | SourceBytesMismatch
  | DeclarationKeyMismatch
  | DeclarationOccurrenceMismatch
  | SourceRevisionMismatch
  | ResourceRejected GrammarV1BorrowResourceError
  | TraceMismatch
  deriving (Eq, Show)

-- The observation is a copyable report. The private positional wrapper has
-- no record selectors, Generic, Read, or API to restore it from a report.
data CheckedBody = CheckedBody BodyObservation

data BodyObservation = BodyObservation
  { bodyOrigin :: SourceOrigin
  , bodyIdentity :: DeclarationIdentity
  , bodyDeclarationSpan :: SourceSpan
  , bodyOwner :: GrammarV1ResolvedBinder
  , bodyView :: GrammarV1ResolvedBinder
  , bodyReturnSpan :: SourceSpan
  , bodyReturnedOwner :: GrammarV1ResolvedBinder
  , bodyTerminal :: Control
  , bodyCheckpoints :: [BorrowTraceCheckpoint]
  , bodyContractReference :: Located GrammarV1Type
  }
  deriving (Eq, Show)

data ContractStop = UnresolvedContractAuthority DeclarationIdentity (Located GrammarV1Type)
  deriving (Eq, Show)

observeCheckedBody :: CheckedBody -> BodyObservation
observeCheckedBody (CheckedBody observation) = observation

-- | This tranche has no competent authority for C and no success capability.
requireContractAuthority :: CheckedBody -> Either ContractStop Void
requireContractAuthority (CheckedBody observation) =
  Left (UnresolvedContractAuthority (bodyIdentity observation) (bodyContractReference observation))

checkSelectedSource
  :: SelectedSource -> SourceOrigin -> Bytes.ByteString -> Either SourceError CheckedBody
checkSelectedSource selection claimed bytes = do
  let (pin, selectedBytes) = selectedOriginal selection
      path = originPath pin
      key = originDeclarationKey pin
  unless (originPath claimed == path) $ Left SourcePathMismatch
  unless (originDeclarationKey claimed == key) $ Left DeclarationKeyMismatch
  unless (originGrammarBlob claimed == originGrammarBlob pin &&
          originParserBlob claimed == originParserBlob pin) $ Left SourceRevisionMismatch
  unless (offsets claimed == offsets pin) $ Left DeclarationOccurrenceMismatch
  source <- either (const (Left MalformedSourceEncoding)) Right (Text.decodeUtf8' bytes)
  parsed <- either (Left . MalformedSource) Right (parseGrammarV1StructuralSource path source)
  (span', fn) <- selectFunction parsed
  let actualDigest = sourceDigest bytes
  unless (bytes == selectedBytes && actualDigest == originSHA256 pin &&
          actualDigest == originSHA256 claimed) $ Left SourceBytesMismatch
  unless (matchesSpan pin span') $ Left DeclarationOccurrenceMismatch
  let checked = grammarV1CheckedBorrowResourceFunction emptyStaticContext key fn
      traced = grammarV1CheckedBorrowResourceFunctionTrace emptyStaticContext key fn
  case (checked, traced) of
    (Just normal, Just (Right trace))
      | normal == grammarV1TraceOutcome trace ->
          either (Left . ResourceRejected)
            (\result -> sealBody pin span' source fn (checkedTerminalControls result) trace) normal
    (Just (Left err), Just (Left tracedError))
      | err == tracedError -> Left (ResourceRejected err)
    (Nothing, Nothing) -> Left UnsupportedSource
    _ -> Left TraceMismatch

selectFunction :: GrammarV1SourceFile -> Either SourceError (SourceSpan, GrammarV1FunctionDecl)
selectFunction parsed
  | grammarV1ModuleDecl parsed == Nothing
  , null (grammarV1ImportDecls parsed)
  , [Located topSpan top] <- grammarV1TopLevelDecls parsed
  , null (grammarV1Attributes top)
  , Located span' (GrammarV1FunctionDeclaration fn) <- grammarV1Declaration top
  , locatedValue (grammarV1FunctionName fn) == "loan"
  , not (grammarV1FunctionRecursive fn)
  , null (grammarV1FunctionGenericParams fn)
  , null (grammarV1FunctionRequirements fn)
  , [Located _ parameter] <- grammarV1FunctionTermParams fn
  , locatedValue (grammarV1TermParamName parameter) == "owner"
  , isBytes8 (grammarV1TermParamType parameter)
  , Just result <- grammarV1FunctionResultType fn
  , isBytes8 result = do
      unless (span' == topSpan) $ Left DeclarationOccurrenceMismatch
      Right (span', fn)
  | otherwise = Left UnsupportedSource
  where
    isBytes8 (Located _ (GrammarV1BytesType (Located _ (GrammarV1IntegerExpression "8")))) = True
    isBytes8 _ = False

sealBody
  :: SourceOrigin -> SourceSpan -> Text -> GrammarV1FunctionDecl -> [Control]
  -> GrammarV1BorrowResourceTrace -> Either SourceError CheckedBody
sealBody origin span' source fn terminals trace
  | [ Located _ (GrammarV1ExpressionStatement
          (Located _ (GrammarV1BorrowExpression _ viewSite (Located _ block))))
    , Located _ (GrammarV1ReturnStatement returned)
    ] <- grammarV1BlockStatements (locatedValue (grammarV1FunctionBody fn))
  , [Located _ (GrammarV1ExpressionStatement (Located _ GrammarV1UnitExpression))]
      <- grammarV1BlockStatements block
  , locatedValue viewSite == "view"
  , locatedValue (grammarV1FunctionSatisfies fn) ==
      GrammarV1NamedType (GrammarV1StaticReference (GrammarV1QualifiedName ["C"]) [])
  , [terminal] <- terminals
  , terminal == Return ty = do
      unless (grammarV1ResolvedBinderKey owner /= grammarV1ResolvedBinderKey view &&
              ownerName /= viewName) $ Left TraceMismatch
      unless (traverse (observeBorrowTraceResource ownerName viewName ty) cuts ==
              Just expectedCuts) $ Left TraceMismatch
      -- The production bridge resolved the returned occurrence to this very
      -- parameter before invoking the resource checker.
      Right $ CheckedBody $ BodyObservation origin identity span' owner view
        (locatedSpan returned) owner terminal cuts (grammarV1FunctionSatisfies fn)
  | otherwise = Left UnsupportedSource
  where
    owner = grammarV1TraceOwnerBinder trace
    view = grammarV1TraceViewBinder trace
    ownerName = grammarV1ResolvedBinderCoreName owner
    viewName = grammarV1ResolvedBinderCoreName view
    ty = TyBytes (RefNat 8)
    cuts = grammarV1TraceCheckpoints trace
    expectedCuts =
      [ BorrowTraceResourceObservation TraceBeforeLoan True False
      , BorrowTraceResourceObservation TraceLoanStarted True True
      , BorrowTraceResourceObservation (TraceBodyResult False) True True
      , BorrowTraceResourceObservation TraceLoanClosed True False
      , BorrowTraceResourceObservation TraceOwnerReturned False False
      ]
    -- Experimental revision domain, with C retained as an unresolved reference.
    signature = SemanticOrdered (map SemanticAtom
      ["phase2-s00-l0-e1", "Linear Bytes[8]", "Linear Bytes[8]", "satisfies C"])
    identity = deriveDeclarationIdentity $ DeclarationDescriptor
      (DeclarationPresentation "loan" []) (originDeclarationKey origin)
      signature (SemanticOrdered [signature, SemanticAtom source])

offsets :: SourceOrigin -> (Int, Int)
offsets origin = (originStart origin, originEnd origin)

matchesSpan :: SourceOrigin -> SourceSpan -> Bool
matchesSpan origin (SourceSpan start end) =
  sourcePointFile start == originPath origin &&
  sourcePointFile end == originPath origin &&
  (sourcePointOffset start, sourcePointOffset end) == offsets origin

selectedOriginal :: SelectedSource -> (SourceOrigin, Bytes.ByteString)
selectedOriginal selection =
  ( SourceOrigin ("test/phase2/s00/fixtures/" <> file) digest (DeclarationKey key)
      0 104 "933fa282487eeae6ba224d68a8d49b9691c4e1dd" "70aabbf9ea95271b1ed6852dfe5ace049bbda959"
  , "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {\n" <>
    "  borrow owner as view { " <> expression <> "; };\n  return owner;\n}\n"
  )
  where
    (file, digest, key, expression) = case selection of
      OriginalLoan ->
        ( "loan.phil", "02732835529e2b4de7a3dec878c6bf8e5532e7f587fbaa85eac79e4405b5de0a"
        , "decl.phase2.s00.l0.e1.loan", "unit"
        )
      EscapeControl ->
        ( "loan-escape.phil", "9224b9580607f977b9cc6780503a2e49b235e5eba9ec61d0364aa820308c8c20"
        , "decl.phase2.s00.l0.e1.escape-control", "view"
        )

sourceDigest :: Bytes.ByteString -> Text
sourceDigest = Text.pack . concatMap hex . Bytes.unpack . SHA256.hash
  where
    hex byte = let digits = showHex byte "" in if byte < 16 then '0' : digits else digits
