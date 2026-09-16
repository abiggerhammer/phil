{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstSessions
  ( GrammarV1ReferenceSessionError (..)
  , GrammarV1ReferenceTermParamCore (..)
  , GrammarV1ReferenceSessionBranchCore (..)
  , GrammarV1ReferenceSessionCore (..)
  , GrammarV1ReferenceRoleSessionCore (..)
  , grammarV1ProductionSessionCore
  , grammarV1ReferenceSessionCore
  , grammarV1ProductionProtocolSessions
  , grammarV1ReferenceProtocolSessions
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TermParam (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore
  , GrammarV1ReferencePropositionError
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticReferenceError
  , GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ProductionStaticReferenceSpine
  , grammarV1ReferenceStaticReferenceSpine
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceDeclarationTag (..)
  , grammarV1ReferenceDeclarationTag
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceTypePayload
  , GrammarV1ReferenceTypePayloadError
  , grammarV1ProductionTypePayload
  , grammarV1ReferenceTypePayload
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceSessionError =
  GrammarV1ReferenceSessionError Text
  deriving (Eq, Show)

data GrammarV1ReferenceTermParamCore = GrammarV1ReferenceTermParamCore
  { grammarV1ReferenceTermParamName :: Text
  , grammarV1ReferenceTermParamType :: GrammarV1ReferenceTypePayload
  }
  deriving (Eq, Show)

data GrammarV1ReferenceSessionBranchCore = GrammarV1ReferenceSessionBranchCore
  { grammarV1ReferenceSessionBranchLabel :: Text
  , grammarV1ReferenceSessionBranchParams :: Maybe [GrammarV1ReferenceTermParamCore]
  , grammarV1ReferenceSessionBranchBoundary :: Maybe GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ReferenceSessionBranchGuard :: Maybe GrammarV1ReferencePropositionCore
  , grammarV1ReferenceSessionBranchContinuation :: GrammarV1ReferenceSessionCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceSessionCore
  = GrammarV1ReferenceSessionReference GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferenceSessionSend
      GrammarV1ReferenceTermParamCore
      (Maybe GrammarV1ReferenceStaticReferenceSpine)
      (Maybe GrammarV1ReferencePropositionCore)
      GrammarV1ReferenceSessionCore
  | GrammarV1ReferenceSessionReceive
      GrammarV1ReferenceTermParamCore
      (Maybe GrammarV1ReferenceStaticReferenceSpine)
      (Maybe GrammarV1ReferencePropositionCore)
      GrammarV1ReferenceSessionCore
  | GrammarV1ReferenceSessionSelect [GrammarV1ReferenceSessionBranchCore]
  | GrammarV1ReferenceSessionOffer [GrammarV1ReferenceSessionBranchCore]
  | GrammarV1ReferenceSessionEnd Text
  | GrammarV1ReferenceSessionRecursive Text GrammarV1ReferenceSessionCore
  | GrammarV1ReferenceSessionContinue Text
  deriving (Eq, Show)

data GrammarV1ReferenceRoleSessionCore = GrammarV1ReferenceRoleSessionCore
  { grammarV1ReferenceRoleSessionName :: Text
  , grammarV1ReferenceRoleSessionValue :: GrammarV1ReferenceSessionCore
  }
  deriving (Eq, Show)

grammarV1ProductionSessionCore
  :: GrammarV1SessionExpression
  -> GrammarV1ReferenceSessionCore
grammarV1ProductionSessionCore session = case session of
  GrammarV1SessionReference reference ->
    GrammarV1ReferenceSessionReference
      (grammarV1ProductionStaticReferenceSpine reference)
  GrammarV1SessionSend parameter boundary guard continuation ->
    GrammarV1ReferenceSessionSend
      (productionTermParam (locatedValue parameter))
      (fmap (grammarV1ProductionStaticReferenceSpine . locatedValue) boundary)
      (fmap (grammarV1ProductionPropositionCore . locatedValue) guard)
      (grammarV1ProductionSessionCore (locatedValue continuation))
  GrammarV1SessionReceive parameter boundary guard continuation ->
    GrammarV1ReferenceSessionReceive
      (productionTermParam (locatedValue parameter))
      (fmap (grammarV1ProductionStaticReferenceSpine . locatedValue) boundary)
      (fmap (grammarV1ProductionPropositionCore . locatedValue) guard)
      (grammarV1ProductionSessionCore (locatedValue continuation))
  GrammarV1SessionSelect branches ->
    GrammarV1ReferenceSessionSelect
      (map (productionSessionBranch . locatedValue) branches)
  GrammarV1SessionOffer branches ->
    GrammarV1ReferenceSessionOffer
      (map (productionSessionBranch . locatedValue) branches)
  GrammarV1SessionEnd label ->
    GrammarV1ReferenceSessionEnd (locatedValue label)
  GrammarV1SessionRecursive label body ->
    GrammarV1ReferenceSessionRecursive
      (locatedValue label)
      (grammarV1ProductionSessionCore (locatedValue body))
  GrammarV1SessionContinue label ->
    GrammarV1ReferenceSessionContinue (locatedValue label)

productionTermParam :: GrammarV1TermParam -> GrammarV1ReferenceTermParamCore
productionTermParam parameter = GrammarV1ReferenceTermParamCore
  { grammarV1ReferenceTermParamName =
      locatedValue (grammarV1TermParamName parameter)
  , grammarV1ReferenceTermParamType =
      grammarV1ProductionTypePayload
        (locatedValue (grammarV1TermParamType parameter))
  }

productionSessionBranch
  :: GrammarV1SessionBranch
  -> GrammarV1ReferenceSessionBranchCore
productionSessionBranch branch = GrammarV1ReferenceSessionBranchCore
  { grammarV1ReferenceSessionBranchLabel =
      locatedValue (grammarV1SessionBranchLabel branch)
  , grammarV1ReferenceSessionBranchParams =
      fmap (map (productionTermParam . locatedValue))
        (grammarV1SessionBranchParams branch)
  , grammarV1ReferenceSessionBranchBoundary =
      fmap (grammarV1ProductionStaticReferenceSpine . locatedValue)
        (grammarV1SessionBranchBoundary branch)
  , grammarV1ReferenceSessionBranchGuard =
      fmap (grammarV1ProductionPropositionCore . locatedValue)
        (grammarV1SessionBranchGuard branch)
  , grammarV1ReferenceSessionBranchContinuation =
      grammarV1ProductionSessionCore
        (locatedValue (grammarV1SessionBranchContinuation branch))
  }

grammarV1ReferenceSessionCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionCore
grammarV1ReferenceSessionCore tree = do
  body <- expectNonterminal "session_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 nonreferenceTree ->
      parseNonreferenceSession nonreferenceTree
    GrammarV1ReferenceAlternative 1 referenceTree ->
      GrammarV1ReferenceSessionReference
        <$> mapStaticReferenceError
              (grammarV1ReferenceStaticReferenceSpine referenceTree)
    GrammarV1ReferenceAlternative index _ ->
      failSession ("session_expression alternative out of range: " <> showText index)
    _ -> failSession "session_expression body is not an alternative node"

parseNonreferenceSession
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionCore
parseNonreferenceSession tree = do
  body <- expectNonterminal "nonreference_session_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> parseSessionTransfer "send" GrammarV1ReferenceSessionSend selected
      1 -> parseSessionTransfer "receive" GrammarV1ReferenceSessionReceive selected
      2 -> parseSessionChoice "select" GrammarV1ReferenceSessionSelect selected
      3 -> parseSessionChoice "offer" GrammarV1ReferenceSessionOffer selected
      4 -> parseSessionEnd selected
      5 -> parseSessionRecursive selected
      6 -> parseSessionContinue selected
      _ -> failSession
        ("nonreference_session_expression alternative out of range: " <> showText index)
    _ -> failSession "nonreference_session_expression body is not an alternative node"

parseSessionTransfer
  :: Text
  -> ( GrammarV1ReferenceTermParamCore
       -> Maybe GrammarV1ReferenceStaticReferenceSpine
       -> Maybe GrammarV1ReferencePropositionCore
       -> GrammarV1ReferenceSessionCore
       -> GrammarV1ReferenceSessionCore
     )
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionCore
parseSessionTransfer keyword constructor tree = do
  fields <- expectSequence (keyword <> " session") tree
  case fields of
    [keywordTree, openParen, parameterTree, closeParen, boundaryTree, guardTree, thenKeyword, continuationTree] -> do
      expectLiteral keyword keywordTree
      expectLiteral "(" openParen
      parameter <- parseTermParam parameterTree
      expectLiteral ")" closeParen
      boundary <- parseOptionalUsing boundaryTree
      guard <- parseOptionalGuard guardTree
      expectLiteral "then" thenKeyword
      continuation <- grammarV1ReferenceSessionCore continuationTree
      pure (constructor parameter boundary guard continuation)
    _ -> failSession (keyword <> " session is not an eight-item sequence")

parseSessionChoice
  :: Text
  -> ([GrammarV1ReferenceSessionBranchCore] -> GrammarV1ReferenceSessionCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionCore
parseSessionChoice keyword constructor tree = do
  fields <- expectSequence (keyword <> " session") tree
  case fields of
    [keywordTree, openBrace, firstTree, restTree, closeBrace] -> do
      expectLiteral keyword keywordTree
      expectLiteral "{" openBrace
      first <- parseSessionBranch firstTree
      suffixes <- expectRepetition (keyword <> " session branch suffixes") restTree
      rest <- traverse parseSessionBranchSuffix suffixes
      expectLiteral "}" closeBrace
      pure (constructor (first : rest))
    _ -> failSession (keyword <> " session is not a five-item sequence")

parseSessionBranchSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionBranchCore
parseSessionBranchSuffix tree = do
  fields <- expectSequence "session branch suffix" tree
  case fields of
    [pipe, branchTree] -> do
      expectLiteral "|" pipe
      parseSessionBranch branchTree
    _ -> failSession "session branch suffix is not a two-item sequence"

parseSessionBranch
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionBranchCore
parseSessionBranch tree = do
  body <- expectNonterminal "session_branch" tree
  fields <- expectSequence "session_branch" body
  case fields of
    [labelTree, paramsTree, boundaryTree, guardTree, arrow, continuationTree] -> do
      label <- parseIdentifier labelTree
      params <- parseOptionalBranchParams paramsTree
      boundary <- parseOptionalUsing boundaryTree
      guard <- parseOptionalGuard guardTree
      expectLiteral "=>" arrow
      continuation <- grammarV1ReferenceSessionCore continuationTree
      pure GrammarV1ReferenceSessionBranchCore
        { grammarV1ReferenceSessionBranchLabel = label
        , grammarV1ReferenceSessionBranchParams = params
        , grammarV1ReferenceSessionBranchBoundary = boundary
        , grammarV1ReferenceSessionBranchGuard = guard
        , grammarV1ReferenceSessionBranchContinuation = continuation
        }
    _ -> failSession "session_branch body is not a six-item sequence"

parseOptionalBranchParams
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError (Maybe [GrammarV1ReferenceTermParamCore])
parseOptionalBranchParams tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome paramsTree -> do
    fields <- expectSequence "session branch parameter list" paramsTree
    case fields of
      [openParen, optionalParams, closeParen] -> do
        expectLiteral "(" openParen
        params <- parseOptionalTermParamList optionalParams
        expectLiteral ")" closeParen
        pure (Just params)
      _ -> failSession "session branch parameter list is not a three-item sequence"
  _ -> failSession "session branch parameter slot is not optional"

parseOptionalTermParamList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError [GrammarV1ReferenceTermParamCore]
parseOptionalTermParamList tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome valuesTree -> do
    fields <- expectSequence "session branch parameters" valuesTree
    case fields of
      [firstTree, restTree] -> do
        first <- parseTermParam firstTree
        suffixes <- expectRepetition "session branch parameter suffixes" restTree
        rest <- traverse parseTermParamSuffix suffixes
        pure (first : rest)
      _ -> failSession "session branch parameters are not a two-item sequence"
  _ -> failSession "session branch inner parameter slot is not optional"

parseTermParamSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceTermParamCore
parseTermParamSuffix tree = do
  fields <- expectSequence "term parameter suffix" tree
  case fields of
    [comma, parameterTree] -> do
      expectLiteral "," comma
      parseTermParam parameterTree
    _ -> failSession "term parameter suffix is not a two-item sequence"

parseTermParam
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceTermParamCore
parseTermParam tree = do
  body <- expectNonterminal "term_param" tree
  fields <- expectSequence "term_param" body
  case fields of
    [nameTree, colon, typeTree] -> do
      name <- parseIdentifier nameTree
      expectLiteral ":" colon
      sourceType <- mapTypePayloadError (grammarV1ReferenceTypePayload typeTree)
      pure GrammarV1ReferenceTermParamCore
        { grammarV1ReferenceTermParamName = name
        , grammarV1ReferenceTermParamType = sourceType
        }
    _ -> failSession "term_param body is not a three-item sequence"

parseOptionalUsing
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError (Maybe GrammarV1ReferenceStaticReferenceSpine)
parseOptionalUsing tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome usingTree -> do
    fields <- expectSequence "using annotation" usingTree
    case fields of
      [usingKeyword, referenceTree] -> do
        expectLiteral "using" usingKeyword
        Just <$> mapStaticReferenceError
          (grammarV1ReferenceStaticReferenceSpine referenceTree)
      _ -> failSession "using annotation is not a two-item sequence"
  _ -> failSession "using annotation slot is not optional"

parseOptionalGuard
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError (Maybe GrammarV1ReferencePropositionCore)
parseOptionalGuard tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome guardTree -> do
    fields <- expectSequence "when annotation" guardTree
    case fields of
      [whenKeyword, propositionTree] -> do
        expectLiteral "when" whenKeyword
        Just <$> mapPropositionError
          (grammarV1ReferencePropositionCore propositionTree)
      _ -> failSession "when annotation is not a two-item sequence"
  _ -> failSession "when annotation slot is not optional"

parseSessionEnd
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionCore
parseSessionEnd tree = do
  fields <- expectSequence "end session" tree
  case fields of
    [endKeyword, labelTree] -> do
      expectLiteral "end" endKeyword
      GrammarV1ReferenceSessionEnd <$> parseIdentifier labelTree
    _ -> failSession "end session is not a two-item sequence"

parseSessionRecursive
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionCore
parseSessionRecursive tree = do
  fields <- expectSequence "recursive session" tree
  case fields of
    [recursiveKeyword, labelTree, equals, bodyTree] -> do
      expectLiteral "recursive" recursiveKeyword
      label <- parseIdentifier labelTree
      expectLiteral "=" equals
      body <- grammarV1ReferenceSessionCore bodyTree
      pure (GrammarV1ReferenceSessionRecursive label body)
    _ -> failSession "recursive session is not a four-item sequence"

parseSessionContinue
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceSessionCore
parseSessionContinue tree = do
  fields <- expectSequence "continue session" tree
  case fields of
    [continueKeyword, labelTree] -> do
      expectLiteral "continue" continueKeyword
      GrammarV1ReferenceSessionContinue <$> parseIdentifier labelTree
    _ -> failSession "continue session is not a two-item sequence"

grammarV1ProductionProtocolSessions
  :: GrammarV1SourceFile
  -> [[GrammarV1ReferenceRoleSessionCore]]
grammarV1ProductionProtocolSessions sourceFile =
  [ map productionRoleSession (grammarV1ProtocolRoles protocol)
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1ProtocolDeclaration protocol <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]
  where
    productionRoleSession locatedRole =
      let role = locatedValue locatedRole
      in GrammarV1ReferenceRoleSessionCore
          { grammarV1ReferenceRoleSessionName =
              locatedValue (grammarV1RoleSessionName role)
          , grammarV1ReferenceRoleSessionValue =
              grammarV1ProductionSessionCore
                (locatedValue (grammarV1RoleSessionExpression role))
          }

grammarV1ReferenceProtocolSessions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError [[GrammarV1ReferenceRoleSessionCore]]
grammarV1ReferenceProtocolSessions tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelProtocolSessions topLevels
      pure [value | Just value <- values]
    _ -> failSession "source_file body is not a three-item sequence"

parseTopLevelProtocolSessions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError (Maybe [GrammarV1ReferenceRoleSessionCore])
parseTopLevelProtocolSessions tree = do
  topLevelBody <- expectNonterminal "top_level_decl" tree
  fields <- expectSequence "top_level_decl" topLevelBody
  case fields of
    [_attributes, declarationTree] -> do
      tag <- mapTopLevelError (grammarV1ReferenceDeclarationTag declarationTree)
      case tag of
        GrammarV1ReferenceProtocolDeclaration -> do
          declarationBody <- expectNonterminal "declaration" declarationTree
          case declarationBody of
            GrammarV1ReferenceAlternative 9 selected ->
              Just <$> parseProtocolSessions selected
            _ -> failSession "protocol declaration does not occupy alternative 9"
        _ -> pure Nothing
    _ -> failSession "top_level_decl body is not a two-item sequence"

parseProtocolSessions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError [GrammarV1ReferenceRoleSessionCore]
parseProtocolSessions tree = do
  body <- expectNonterminal "protocol_decl" tree
  fields <- expectSequence "protocol_decl" body
  case fields of
    [protocolKeyword, _nameTree, _genericTree, _requirementsTree, openBrace, firstRoleTree, secondRoleTree, closeBrace] -> do
      expectLiteral "protocol" protocolKeyword
      expectLiteral "{" openBrace
      first <- parseRoleSession firstRoleTree
      second <- parseRoleSession secondRoleTree
      expectLiteral "}" closeBrace
      pure [first, second]
    _ -> failSession "protocol_decl body is not an eight-item sequence"

parseRoleSession
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceRoleSessionCore
parseRoleSession tree = do
  body <- expectNonterminal "role_session_decl" tree
  fields <- expectSequence "role_session_decl" body
  case fields of
    [roleKeyword, nameTree, equals, sessionTree, terminator] -> do
      expectLiteral "role" roleKeyword
      name <- parseIdentifier nameTree
      expectLiteral "=" equals
      session <- grammarV1ReferenceSessionCore sessionTree
      expectLiteral ";" terminator
      pure GrammarV1ReferenceRoleSessionCore
        { grammarV1ReferenceRoleSessionName = name
        , grammarV1ReferenceRoleSessionValue = session
        }
    _ -> failSession "role_session_decl body is not a five-item sequence"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> pure value
    GrammarV1ReferenceLexical className _ ->
      failSession ("identifier uses lexical class " <> className)
    _ -> failSession "identifier body is not an IDENTIFIER lexical leaf"

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failSession
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failSession ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failSession (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failSession (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceSessionError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failSession
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failSession ("expected literal " <> expected)

mapTypePayloadError
  :: Either GrammarV1ReferenceTypePayloadError a
  -> Either GrammarV1ReferenceSessionError a
mapTypePayloadError = mapLeft
  (GrammarV1ReferenceSessionError . Text.pack . show)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceSessionError a
mapStaticReferenceError = mapLeft
  (GrammarV1ReferenceSessionError . Text.pack . show)

mapPropositionError
  :: Either GrammarV1ReferencePropositionError a
  -> Either GrammarV1ReferenceSessionError a
mapPropositionError = mapLeft
  (GrammarV1ReferenceSessionError . Text.pack . show)

mapTopLevelError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceSessionError a
mapTopLevelError = mapLeft
  (GrammarV1ReferenceSessionError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failSession :: Text -> Either GrammarV1ReferenceSessionError a
failSession = Left . GrammarV1ReferenceSessionError
