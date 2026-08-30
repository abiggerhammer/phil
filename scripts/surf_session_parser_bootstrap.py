from pathlib import Path
import sys

p = Path(sys.argv[1])
text = p.read_text()

def repl(old: str, new: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"expected one replacement target, found {count}: {old[:90]!r}")
    text = text.replace(old, new, 1)

repl(
    "  , GrammarV1BoundaryDecl (..)\n  , GrammarV1SessionExpression (..)\n  , GrammarV1RoleSessionDecl (..)\n",
    "  , GrammarV1BoundaryDecl (..)\n  , GrammarV1SessionExpression (..)\n  , GrammarV1SessionBranch (..)\n  , GrammarV1RoleSessionDecl (..)\n",
)

repl(
    "  | GrammarV1StaticIntegerArgument Text\n  | GrammarV1StaticValueArgument (Located GrammarV1StaticValueExpression)\n  | GrammarV1StaticEffectSetArgument (Located GrammarV1EffectSetExpression)\n  deriving (Eq, Ord, Show)\n",
    "  | GrammarV1StaticIntegerArgument Text\n  | GrammarV1StaticValueArgument (Located GrammarV1StaticValueExpression)\n  | GrammarV1StaticEffectSetArgument (Located GrammarV1EffectSetExpression)\n  | GrammarV1StaticSessionArgument (Located GrammarV1SessionExpression)\n  deriving (Eq, Ord, Show)\n",
)

old_ast = """data GrammarV1SessionExpression
  = GrammarV1SessionReference
      { grammarV1SessionReference :: GrammarV1StaticReference
      }
  | GrammarV1SessionSend
      (Located GrammarV1TermParam)
      (Maybe (Located GrammarV1StaticReference))
      (Maybe (Located GrammarV1Proposition))
      (Located GrammarV1SessionExpression)
  | GrammarV1SessionReceive
      (Located GrammarV1TermParam)
      (Maybe (Located GrammarV1StaticReference))
      (Maybe (Located GrammarV1Proposition))
      (Located GrammarV1SessionExpression)
  | GrammarV1SessionEnd (Located Text)
  deriving (Eq, Ord, Show)
"""
new_ast = """data GrammarV1SessionExpression
  = GrammarV1SessionReference
      { grammarV1SessionReference :: GrammarV1StaticReference
      }
  | GrammarV1SessionSend
      (Located GrammarV1TermParam)
      (Maybe (Located GrammarV1StaticReference))
      (Maybe (Located GrammarV1Proposition))
      (Located GrammarV1SessionExpression)
  | GrammarV1SessionReceive
      (Located GrammarV1TermParam)
      (Maybe (Located GrammarV1StaticReference))
      (Maybe (Located GrammarV1Proposition))
      (Located GrammarV1SessionExpression)
  | GrammarV1SessionSelect [Located GrammarV1SessionBranch]
  | GrammarV1SessionOffer [Located GrammarV1SessionBranch]
  | GrammarV1SessionEnd (Located Text)
  | GrammarV1SessionRecursive
      (Located Text)
      (Located GrammarV1SessionExpression)
  | GrammarV1SessionContinue (Located Text)
  deriving (Eq, Ord, Show)

data GrammarV1SessionBranch = GrammarV1SessionBranch
  { grammarV1SessionBranchLabel :: Located Text
  , grammarV1SessionBranchParams :: Maybe [Located GrammarV1TermParam]
  , grammarV1SessionBranchBoundary :: Maybe (Located GrammarV1StaticReference)
  , grammarV1SessionBranchGuard :: Maybe (Located GrammarV1Proposition)
  , grammarV1SessionBranchContinuation :: Located GrammarV1SessionExpression
  }
  deriving (Eq, Ord, Show)
"""
repl(old_ast, new_ast)

repl(
    '    Just (GrammarKeyword "Validated") -> GrammarV1StaticTypeArgument . locatedValue <$> parseType\n    Just (GrammarSymbol "{") -> do\n',
    '    Just (GrammarKeyword "Validated") -> GrammarV1StaticTypeArgument . locatedValue <$> parseType\n    Just (GrammarKeyword "send") -> GrammarV1StaticSessionArgument <$> parseSessionExpression\n    Just (GrammarKeyword "receive") -> GrammarV1StaticSessionArgument <$> parseSessionExpression\n    Just (GrammarKeyword "select") -> GrammarV1StaticSessionArgument <$> parseSessionExpression\n    Just (GrammarKeyword "offer") -> GrammarV1StaticSessionArgument <$> parseSessionExpression\n    Just (GrammarKeyword "end") -> GrammarV1StaticSessionArgument <$> parseSessionExpression\n    Just (GrammarKeyword "recursive") -> GrammarV1StaticSessionArgument <$> parseSessionExpression\n    Just (GrammarKeyword "continue") -> GrammarV1StaticSessionArgument <$> parseSessionExpression\n    Just (GrammarSymbol "{") -> do\n',
)

start = text.index("parseSessionExpression :: Parser (Located GrammarV1SessionExpression)")
end = text.index("\nparseComponentDeclaration :: Parser (Located GrammarV1Declaration)", start)
replacement = """parseSessionExpression :: Parser (Located GrammarV1SessionExpression)
parseSessionExpression = do
  token <- peekToken
  case fmap locatedValue token of
    Just (GrammarKeyword "send") ->
      parseSessionTransfer "send" GrammarV1SessionSend
    Just (GrammarKeyword "receive") ->
      parseSessionTransfer "receive" GrammarV1SessionReceive
    Just (GrammarKeyword "select") ->
      parseSessionChoice "select" GrammarV1SessionSelect
    Just (GrammarKeyword "offer") ->
      parseSessionChoice "offer" GrammarV1SessionOffer
    Just (GrammarKeyword "end") -> parseSessionEnd
    Just (GrammarKeyword "recursive") -> parseSessionRecursive
    Just (GrammarKeyword "continue") -> parseSessionContinue
    Just (GrammarIdentifier _) -> do
      reference <- parseStaticReference
      pure $ Located
        (locatedSpan reference)
        (GrammarV1SessionReference (locatedValue reference))
    Just other -> failParser $
      "expected session_expression; found " <> renderToken other
    Nothing -> failParser "expected session_expression at end of input"

parseSessionTransfer
  :: Text
  -> ( Located GrammarV1TermParam
       -> Maybe (Located GrammarV1StaticReference)
       -> Maybe (Located GrammarV1Proposition)
       -> Located GrammarV1SessionExpression
       -> GrammarV1SessionExpression
     )
  -> Parser (Located GrammarV1SessionExpression)
parseSessionTransfer keyword constructor = do
  start <- expectKeyword keyword
  _ <- expectSymbol "("
  param <- parseTermParam
  _ <- expectSymbol ")"
  hasUsing <- peekKeyword "using"
  boundary <- if hasUsing
    then expectKeyword "using" >> Just <$> parseStaticReference
    else pure Nothing
  hasGuard <- peekKeyword "when"
  guard <- if hasGuard
    then expectKeyword "when" >> Just <$> parseProposition
    else pure Nothing
  _ <- expectKeyword "then"
  continuation <- parseSessionExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan continuation)))
    (constructor param boundary guard continuation)

parseSessionChoice
  :: Text
  -> ([Located GrammarV1SessionBranch] -> GrammarV1SessionExpression)
  -> Parser (Located GrammarV1SessionExpression)
parseSessionChoice keyword constructor = do
  start <- expectKeyword keyword
  _ <- expectSymbol "{"
  atEnd <- peekSymbol "}"
  if atEnd
    then failParser (keyword <> " session requires at least one session_branch")
    else do
      first <- parseSessionBranch
      rest <- parseMoreSessionBranches
      end <- expectSymbol "}"
      pure $ locatedBetween start end (constructor (first : rest))

parseMoreSessionBranches :: Parser [Located GrammarV1SessionBranch]
parseMoreSessionBranches = do
  hasPipe <- peekSymbol "|"
  if hasPipe
    then do
      _ <- expectSymbol "|"
      atEnd <- peekSymbol "}"
      if atEnd
        then failParser "session branch list does not admit a trailing pipe"
        else do
          branch <- parseSessionBranch
          rest <- parseMoreSessionBranches
          pure (branch : rest)
    else pure []

parseSessionBranch :: Parser (Located GrammarV1SessionBranch)
parseSessionBranch = do
  label <- expectIdentifier
  hasParams <- peekSymbol "("
  params <- if hasParams then Just <$> parseTermParams else pure Nothing
  hasUsing <- peekKeyword "using"
  boundary <- if hasUsing
    then expectKeyword "using" >> Just <$> parseStaticReference
    else pure Nothing
  hasGuard <- peekKeyword "when"
  guard <- if hasGuard
    then expectKeyword "when" >> Just <$> parseProposition
    else pure Nothing
  _ <- expectSymbol "=>"
  continuation <- parseSessionExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan label))
      (sourceSpanEnd (locatedSpan continuation)))
    GrammarV1SessionBranch
      { grammarV1SessionBranchLabel = label
      , grammarV1SessionBranchParams = params
      , grammarV1SessionBranchBoundary = boundary
      , grammarV1SessionBranchGuard = guard
      , grammarV1SessionBranchContinuation = continuation
      }

parseSessionEnd :: Parser (Located GrammarV1SessionExpression)
parseSessionEnd = do
  start <- expectKeyword "end"
  label <- expectIdentifier
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan label)))
    (GrammarV1SessionEnd label)

parseSessionRecursive :: Parser (Located GrammarV1SessionExpression)
parseSessionRecursive = do
  start <- expectKeyword "recursive"
  label <- expectIdentifier
  _ <- expectSymbol "="
  body <- parseSessionExpression
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan body)))
    (GrammarV1SessionRecursive label body)

parseSessionContinue :: Parser (Located GrammarV1SessionExpression)
parseSessionContinue = do
  start <- expectKeyword "continue"
  label <- expectIdentifier
  pure $ Located
    (SourceSpan
      (sourceSpanStart (locatedSpan start))
      (sourceSpanEnd (locatedSpan label)))
    (GrammarV1SessionContinue label)
"""
text = text[:start] + replacement + text[end:]
p.write_text(text)
