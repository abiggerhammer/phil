{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1BinderKey (..)
  , GrammarV1ResolvedBinder (..)
  , GrammarV1LexicalScope
  , GrammarV1BinderScopeError (..)
  , grammarV1RootLexicalScope
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  , grammarV1BindLocal
  , grammarV1ResolveLocal
  , grammarV1BindTermParameters
  , grammarV1FunctionParameterScope
  , grammarV1ComponentParameterScope
  , grammarV1ClosureParameterScope
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax (Name (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Closure (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax
  ( Located (..)
  , SourceSpan
  )

-- | Source-level binder family. This is diagnostic/category metadata, not part of
-- binder identity: the exact identity below is determined only by the enclosing
-- declaration lineage plus a fresh lexical ordinal.
data GrammarV1BinderKind
  = GrammarV1FunctionParameterBinder
  | GrammarV1ComponentParameterBinder
  | GrammarV1ClosureParameterBinder
  | GrammarV1LetPatternBinder
  | GrammarV1MatchArmBinder
  | GrammarV1BorrowViewBinder
  | GrammarV1JoinStateBinder
  | GrammarV1LoopStateBinder
  | GrammarV1ProtocolMessageBinder
  | GrammarV1ProtocolBranchPayloadBinder
  deriving (Eq, Ord, Show)

-- | Semantic identity for one local source binder. Display spelling and source
-- location are deliberately absent. The declaration root is supplied by the
-- persisted lineage authority; the ordinal is allocated monotonically while
-- elaborating that declaration, including across sibling lexical scopes.
data GrammarV1BinderKey = GrammarV1BinderKey
  { grammarV1BinderDeclarationRoot :: DeclarationKey
  , grammarV1BinderOrdinal :: Int
  }
  deriving (Eq, Ord, Show)

-- | One active source binder after lexical identity allocation. The human-facing
-- spelling/span remain attached for diagnostics while all semantic references use
-- the stable-in-this-elaboration key/Core name.
data GrammarV1ResolvedBinder = GrammarV1ResolvedBinder
  { grammarV1ResolvedBinderKey :: GrammarV1BinderKey
  , grammarV1ResolvedBinderCoreName :: Name
  , grammarV1ResolvedBinderKind :: GrammarV1BinderKind
  , grammarV1ResolvedBinderDisplayName :: Text
  , grammarV1ResolvedBinderSourceSpan :: SourceSpan
  }
  deriving (Eq, Show)

-- | Lexical frames are ordered innermost first. The next ordinal is global to the
-- enclosing declaration and is intentionally not rolled back when a child scope
-- closes, so two disjoint binders that reuse one spelling remain distinct semantic
-- occurrences.
data GrammarV1LexicalScope = GrammarV1LexicalScope
  { grammarV1ScopeRootDeclaration :: DeclarationKey
  , grammarV1ScopeFrames :: [Map Text GrammarV1ResolvedBinder]
  , grammarV1ScopeNextOrdinal :: Int
  }
  deriving (Eq, Show)

data GrammarV1BinderScopeError
  = GrammarV1DuplicateBinder
      (Located Text)
      GrammarV1ResolvedBinder
  | GrammarV1ActiveShadowing
      (Located Text)
      GrammarV1ResolvedBinder
  | GrammarV1BinderNotInScope (Located Text)
  | GrammarV1CannotLeaveRootScope
  deriving (Eq, Show)

-- | Begin lexical elaboration for one exact identity-bearing declaration.
grammarV1RootLexicalScope :: DeclarationKey -> GrammarV1LexicalScope
grammarV1RootLexicalScope declarationKey = GrammarV1LexicalScope
  { grammarV1ScopeRootDeclaration = declarationKey
  , grammarV1ScopeFrames = [Map.empty]
  , grammarV1ScopeNextOrdinal = 0
  }

-- | Enter one nested lexical region. No source binder is created merely by
-- entering the region.
grammarV1EnterLexicalScope :: GrammarV1LexicalScope -> GrammarV1LexicalScope
grammarV1EnterLexicalScope scope = scope
  { grammarV1ScopeFrames = Map.empty : grammarV1ScopeFrames scope
  }

-- | Leave one nested lexical region. Its local spellings immediately cease to
-- resolve, but the fresh-identity counter remains advanced.
grammarV1LeaveLexicalScope
  :: GrammarV1LexicalScope
  -> Either GrammarV1BinderScopeError GrammarV1LexicalScope
grammarV1LeaveLexicalScope scope = case grammarV1ScopeFrames scope of
  _current : parent : rest -> Right scope
    { grammarV1ScopeFrames = parent : rest
    }
  _ -> Left GrammarV1CannotLeaveRootScope

-- | Introduce one binder under the Phase 1 no-active-shadowing discipline.
-- Duplicate spelling in the same binding frame and shadowing any still-active
-- enclosing binder are distinct diagnostics. Disjoint sibling scopes may reuse
-- spelling because the prior binder is no longer active.
grammarV1BindLocal
  :: GrammarV1BinderKind
  -> Located Text
  -> GrammarV1LexicalScope
  -> Either
      GrammarV1BinderScopeError
      (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
grammarV1BindLocal binderKind sourceName scope =
  case grammarV1ScopeFrames scope of
    [] -> Left GrammarV1CannotLeaveRootScope
    currentFrame : outerFrames ->
      case Map.lookup displayName currentFrame of
        Just previous -> Left (GrammarV1DuplicateBinder sourceName previous)
        Nothing -> case firstActive displayName outerFrames of
          Just previous -> Left (GrammarV1ActiveShadowing sourceName previous)
          Nothing ->
            let binderKey = GrammarV1BinderKey
                  (grammarV1ScopeRootDeclaration scope)
                  (grammarV1ScopeNextOrdinal scope)
                resolvedBinder = GrammarV1ResolvedBinder
                  { grammarV1ResolvedBinderKey = binderKey
                  , grammarV1ResolvedBinderCoreName = binderCoreName binderKey
                  , grammarV1ResolvedBinderKind = binderKind
                  , grammarV1ResolvedBinderDisplayName = displayName
                  , grammarV1ResolvedBinderSourceSpan = locatedSpan sourceName
                  }
                nextFrame = Map.insert displayName resolvedBinder currentFrame
            in Right
              ( resolvedBinder
              , scope
                  { grammarV1ScopeFrames = nextFrame : outerFrames
                  , grammarV1ScopeNextOrdinal = grammarV1ScopeNextOrdinal scope + 1
                  }
              )
  where
    displayName = locatedValue sourceName

-- | Resolve one active source spelling to its exact semantic binder occurrence.
-- Source spelling locates; the returned BinderKey/Core Name identify.
grammarV1ResolveLocal
  :: Located Text
  -> GrammarV1LexicalScope
  -> Either GrammarV1BinderScopeError GrammarV1ResolvedBinder
grammarV1ResolveLocal sourceName scope =
  case firstActive (locatedValue sourceName) (grammarV1ScopeFrames scope) of
    Just resolvedBinder -> Right resolvedBinder
    Nothing -> Left (GrammarV1BinderNotInScope sourceName)

-- | Allocate identities for a term-parameter telescope in source order. Types are
-- deliberately not checked here: this module owns lexical identity/scope only.
grammarV1BindTermParameters
  :: GrammarV1BinderKind
  -> [Located GrammarV1TermParam]
  -> GrammarV1LexicalScope
  -> Either
      GrammarV1BinderScopeError
      ([GrammarV1ResolvedBinder], GrammarV1LexicalScope)
grammarV1BindTermParameters binderKind = go []
  where
    go reversed [] scope = Right (reverse reversed, scope)
    go reversed (Located _ parameter : rest) scope = do
      (resolvedBinder, nextScope) <- grammarV1BindLocal
        binderKind
        (grammarV1TermParamName parameter)
        scope
      go (resolvedBinder : reversed) rest nextScope

-- | Establish the root term-parameter scope for one named function. Supplying the
-- exact DeclarationKey makes alpha-renaming/source movement presentation-only for
-- binder identity when telescope structure is unchanged.
grammarV1FunctionParameterScope
  :: DeclarationKey
  -> GrammarV1FunctionDecl
  -> Either
      GrammarV1BinderScopeError
      ([GrammarV1ResolvedBinder], GrammarV1LexicalScope)
grammarV1FunctionParameterScope declarationKey functionDecl =
  grammarV1BindTermParameters
    GrammarV1FunctionParameterBinder
    (grammarV1FunctionTermParams functionDecl)
    (grammarV1RootLexicalScope declarationKey)

-- | Establish the root term-parameter scope for one component while preserving
-- the source distinction between an omitted parameter list and explicit `()`.
-- Present parameters receive the same declaration-rooted ordinal/Core-name
-- identity discipline as the other SURF-009 runtime binder families.
grammarV1ComponentParameterScope
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Either
      GrammarV1BinderScopeError
      (Maybe [GrammarV1ResolvedBinder], GrammarV1LexicalScope)
grammarV1ComponentParameterScope declarationKey componentDecl =
  case grammarV1ComponentTermParams componentDecl of
    Nothing -> Right (Nothing, grammarV1RootLexicalScope declarationKey)
    Just parameters -> do
      (binders, scope) <- grammarV1BindTermParameters
        GrammarV1ComponentParameterBinder
        parameters
        (grammarV1RootLexicalScope declarationKey)
      Right (Just binders, scope)

-- | Enter a child region for one closure and allocate its parameters there. An
-- equal spelling still active in the enclosing function/closure is rejected as
-- active shadowing; a spelling from a closed sibling scope is permitted and gets
-- a fresh semantic identity.
grammarV1ClosureParameterScope
  :: GrammarV1LexicalScope
  -> GrammarV1Closure
  -> Either
      GrammarV1BinderScopeError
      ([GrammarV1ResolvedBinder], GrammarV1LexicalScope)
grammarV1ClosureParameterScope outerScope closure =
  grammarV1BindTermParameters
    GrammarV1ClosureParameterBinder
    (grammarV1ClosureTermParams closure)
    (grammarV1EnterLexicalScope outerScope)

firstActive
  :: Text
  -> [Map Text GrammarV1ResolvedBinder]
  -> Maybe GrammarV1ResolvedBinder
firstActive _ [] = Nothing
firstActive displayName (frame : rest) =
  case Map.lookup displayName frame of
    Just resolvedBinder -> Just resolvedBinder
    Nothing -> firstActive displayName rest

-- | Injectively encode declaration-root text plus local ordinal into the existing
-- Core Name carrier. The length prefix prevents delimiter-shaped declaration keys
-- from colliding. This is an internal semantic name, never the user's spelling.
binderCoreName :: GrammarV1BinderKey -> Name
binderCoreName (GrammarV1BinderKey (DeclarationKey rootText) ordinal) =
  Name
    ( "$phil.local:"
      <> Text.pack (show (Text.length rootText))
      <> ":"
      <> rootText
      <> ":"
      <> Text.pack (show ordinal)
    )
