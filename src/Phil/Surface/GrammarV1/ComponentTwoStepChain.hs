{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 NON-NORMATIVE. Bounded production source-component checker for
-- exactly two lexical Send/Receive generations and terminal Close.
-- Source parsing, lexical binder identity and pattern binding reuse the real
-- Grammar-v1 implementation. This is *not* the general component compiler,
-- a protocol/architecture authority grant, or a compiler-correctness theorem.
module Phil.Surface.GrammarV1.ComponentTwoStepChain
  ( ChainError (..)
  , CheckedChain (..)
  , checkSendChain
  , checkReceiveChain
  ) where

import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Name)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..), GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..), grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.PatternBinderScope (grammarV1BindPattern)
import Phil.Surface.Syntax (Located (..))

data ChainError
  = ChainUnsupportedSourceShape
  | ChainUnresolvedOccurrence
  | ChainFirstEndpointNotParameter
  | ChainSecondPayloadNotParameter
  | ChainFirstReceiveAnnotationNotU8
  | ChainSecondReceiveAnnotationNotU8
  | ChainSecondPredecessorMismatch
  | ChainTerminalCloseMismatch
  | ChainPatternShape
  | ChainBinderError String
  deriving (Eq, Show)

data CheckedChain = CheckedChain
  { chainBefore :: Name
  , chainMiddle :: Name
  , chainFinal :: Name
  } deriving (Eq, Show)

-- Production lexical identity is the authority for distinguishing source
-- occurrences. Name spelling is *never* used as a Core endpoint identity.
local :: GrammarV1LexicalScope -> Located GrammarV1Expression
      -> Either ChainError GrammarV1ResolvedBinder
local scope source =
  maybe (Left ChainUnresolvedOccurrence)
    (Right . grammarV1CheckedLocalValueBinder)
    (grammarV1CheckedLocalValueOccurrenceInScope scope source)

bindOne :: Located GrammarV1Pattern -> GrammarV1LexicalScope
        -> Either ChainError (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
bindOne patternSource scope = do
  (binders, after) <- mapLeft (ChainBinderError . show) $
    grammarV1BindPattern GrammarV1LetPatternBinder patternSource scope
  case binders of
    [one] -> Right (one, after)
    _ -> Left ChainPatternShape

bindReceive :: Located GrammarV1Pattern -> GrammarV1LexicalScope
            -> Either ChainError (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
bindReceive patternSource scope =
  case locatedValue patternSource of
    GrammarV1TuplePattern [_, _] -> do
      (binders, after) <- mapLeft (ChainBinderError . show) $
        grammarV1BindPattern GrammarV1LetPatternBinder patternSource scope
      case binders of
        [endpoint, _payload] -> Right (endpoint, after)
        _ -> Left ChainPatternShape
    _ -> Left ChainPatternShape

checkSendChain :: DeclarationKey -> GrammarV1ComponentDecl
               -> Either ChainError CheckedChain
checkSendChain declaration component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement p1 e1)
      , Located _ (GrammarV1LetStatement p2 e2)
      , Located _ (GrammarV1ExpressionStatement eClose)
      ] -> case (locatedValue e1, locatedValue e2, locatedValue eClose) of
        ( GrammarV1SendExpression payload1 endpoint1
          , GrammarV1SendExpression payload2 endpoint2
          , GrammarV1CloseExpression closed
          ) -> do
            (_, scope0) <- mapLeft (ChainBinderError . show) $
              grammarV1ComponentParameterScope declaration component
            p1Binder <- local scope0 payload1
            first <- local scope0 endpoint1
            expectChain (grammarV1ResolvedBinderKind first ==
              GrammarV1ComponentParameterBinder &&
              grammarV1ResolvedBinderKind p1Binder ==
              GrammarV1ComponentParameterBinder)
              ChainFirstEndpointNotParameter
            (middle, scope1) <- bindOne p1 scope0
            -- The second payload is resolved AFTER the first let binding.
            -- A real, newly bound endpoint must not be mistaken for a
            -- component-parameter U8 payload by consulting scope0.
            p2Binder <- local scope1 payload2
            expectChain (grammarV1ResolvedBinderKind p2Binder ==
              GrammarV1ComponentParameterBinder) ChainSecondPayloadNotParameter
            usedMiddle <- local scope1 endpoint2
            expectChain (sameBinder usedMiddle middle) ChainSecondPredecessorMismatch
            (final, scope2) <- bindOne p2 scope1
            closedBinder <- local scope2 closed
            expectChain (sameBinder final closedBinder) ChainTerminalCloseMismatch
            pure $ CheckedChain (core first) (core middle) (core final)
        _ -> Left ChainUnsupportedSourceShape
    _ -> Left ChainUnsupportedSourceShape

checkReceiveChain :: DeclarationKey -> GrammarV1ComponentDecl
                  -> Either ChainError CheckedChain
checkReceiveChain declaration component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement p1 e1)
      , Located _ (GrammarV1LetStatement p2 e2)
      , Located _ (GrammarV1ExpressionStatement eClose)
      ] -> case (locatedValue e1, locatedValue e2, locatedValue eClose) of
        ( GrammarV1ReceiveExpression writtenType1 endpoint1
          , GrammarV1ReceiveExpression writtenType2 endpoint2
          , GrammarV1CloseExpression closed
          ) -> do
            (_, scope0) <- mapLeft (ChainBinderError . show) $
              grammarV1ComponentParameterScope declaration component
            first <- local scope0 endpoint1
            expectChain (grammarV1ResolvedBinderKind first ==
              GrammarV1ComponentParameterBinder)
              ChainFirstEndpointNotParameter
            -- Restricted DoublePing U8/U8 witness envelope only.
            -- Protocol-head authority is supplied externally, not inferred here.
            expectChain (locatedValue writtenType1 == GrammarV1UnsignedType "U8")
              ChainFirstReceiveAnnotationNotU8
            (middle, scope1) <- bindReceive p1 scope0
            usedMiddle <- local scope1 endpoint2
            expectChain (sameBinder usedMiddle middle) ChainSecondPredecessorMismatch
            expectChain (locatedValue writtenType2 == GrammarV1UnsignedType "U8")
              ChainSecondReceiveAnnotationNotU8
            (final, scope2) <- bindReceive p2 scope1
            closedBinder <- local scope2 closed
            expectChain (sameBinder final closedBinder) ChainTerminalCloseMismatch
            pure $ CheckedChain (core first) (core middle) (core final)
        _ -> Left ChainUnsupportedSourceShape
    _ -> Left ChainUnsupportedSourceShape

expectChain :: Bool -> ChainError -> Either ChainError ()
expectChain True _ = Right ()
expectChain False err = Left err

sameBinder :: GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder -> Bool
sameBinder one other =
  grammarV1ResolvedBinderKey one == grammarV1ResolvedBinderKey other

core :: GrammarV1ResolvedBinder -> Name
core = grammarV1ResolvedBinderCoreName

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
