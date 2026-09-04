module Phil.Surface.GrammarV1.ProtocolSpecializedSessionReferences
  ( GrammarV1ResolvedSpecializedSessionRole (..)
  , GrammarV1CheckedSpecializedSessionRole (..)
  , GrammarV1ProtocolSpecializedSessionError (..)
  , grammarV1CheckedSpecializedProtocolSessionReferences
  ) where

import qualified Data.Text as Text
import Data.Text (Text)
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter
  , GenericStaticReferenceCandidate (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  , SemanticForm
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1CheckedSpecializedStaticReference
  , GrammarV1ResolvedDirectStaticArgument
  , GrammarV1SpecializedStaticReferenceError
  , grammarV1CheckedSpecializedStaticReference
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact resolver evidence for one role whose entire session body is a
-- specialized static Session reference. The full located role occurrence is
-- repeated so source correspondence is checked without resolving the target from
-- display spelling. The target candidate supplies the competent resolver's
-- category and semantic form; stable declaration/interface identity and target
-- generic parameter schema are likewise supplied rather than reconstructed.
data GrammarV1ResolvedSpecializedSessionRole =
  GrammarV1ResolvedSpecializedSessionRole
    { resolvedSpecializedSessionSourceRole :: Located GrammarV1RoleSessionDecl
    , resolvedSpecializedSessionTargetCandidate :: GenericStaticReferenceCandidate
    , resolvedSpecializedSessionDeclarationKey :: DeclarationKey
    , resolvedSpecializedSessionInterfaceRevision :: InterfaceRevision
    , resolvedSpecializedSessionParameters :: [GenericStaticParameter]
    , resolvedSpecializedSessionDirectArguments :: [GrammarV1ResolvedDirectStaticArgument]
    , resolvedSpecializedSessionArgumentReferences :: [GenericStaticReferenceCandidate]
    }
  deriving (Eq, Show)

-- | Checked correspondence result. The target semantic form is retained
-- separately from the generic application result so later Session resolution can
-- consume both without deriving target identity from the source name.
data GrammarV1CheckedSpecializedSessionRole =
  GrammarV1CheckedSpecializedSessionRole
    { checkedSpecializedSessionRoleKey :: ProtocolRoleKey
    , checkedSpecializedSessionTargetSemanticForm :: SemanticForm
    , checkedSpecializedSessionReference :: GrammarV1CheckedSpecializedStaticReference
    }
  deriving (Eq, Show)

data GrammarV1ProtocolSpecializedSessionError
  = GrammarV1SpecializedSessionEvidenceCountMismatch Int Int
  | GrammarV1SpecializedSessionRoleSourceMismatch
      Int
      (Located GrammarV1RoleSessionDecl)
      (Located GrammarV1RoleSessionDecl)
  | GrammarV1SpecializedSessionTargetNameMismatch Text Text
  | GrammarV1SpecializedSessionTargetKindMismatch Text GenericStaticKind
  | GrammarV1SpecializedSessionStaticReferenceError
      GrammarV1SpecializedStaticReferenceError
  deriving (Eq, Show)

-- | Check the first Grammar-v1 protocol fragment whose two role bodies are
-- specialized references to already-resolved Session declarations.
--
-- Protocol generics and requirements remain outside this bounded route. Each
-- role must be exactly one specialized static reference. Caller evidence must be
-- present in role order and tied to the exact Located role occurrence. The target
-- candidate's textual name is checked only for source correspondence; its
-- GenericSessionKind and semantic form come from the competent static resolver.
-- Thus a session-shaped source position cannot manufacture Session category.
--
-- Static-argument checking and GenericApplicationIdentity construction are
-- delegated unchanged to 'grammarV1CheckedSpecializedStaticReference'. This layer
-- does not instantiate the resulting Session, check role duality, construct a
-- BinaryProtocolFamily, discharge requirements, or resolve any source binder.
grammarV1CheckedSpecializedProtocolSessionReferences
  :: [GrammarV1ResolvedSpecializedSessionRole]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolSpecializedSessionError
        ( GrammarV1CheckedSpecializedSessionRole
        , GrammarV1CheckedSpecializedSessionRole
        ))
grammarV1CheckedSpecializedProtocolSessionReferences evidence source
  | not (null (grammarV1ProtocolGenericParams source)) = Nothing
  | not (null (grammarV1ProtocolRequirements source)) = Nothing
  | otherwise = case grammarV1ProtocolRoles source of
      [firstRole, secondRole] -> do
        firstReference <- specializedRoleReference firstRole
        secondReference <- specializedRoleReference secondRole
        if length evidence /= 2
          then Just
            (Left
              (GrammarV1SpecializedSessionEvidenceCountMismatch
                2
                (length evidence)))
          else case evidence of
            [firstEvidence, secondEvidence] -> do
              firstChecked <- checkRole 0 firstRole firstReference firstEvidence
              secondChecked <- checkRole 1 secondRole secondReference secondEvidence
              pure $ do
                first <- firstChecked
                second <- secondChecked
                Right (first, second)
            _ -> Nothing
      _ -> Nothing

specializedRoleReference
  :: Located GrammarV1RoleSessionDecl
  -> Maybe GrammarV1StaticReference
specializedRoleReference (Located _ role) =
  case locatedValue (grammarV1RoleSessionExpression role) of
    GrammarV1SessionReference reference
      | not (null (grammarV1StaticReferenceArguments reference)) -> Just reference
    _ -> Nothing

checkRole
  :: Int
  -> Located GrammarV1RoleSessionDecl
  -> GrammarV1StaticReference
  -> GrammarV1ResolvedSpecializedSessionRole
  -> Maybe
      (Either
        GrammarV1ProtocolSpecializedSessionError
        GrammarV1CheckedSpecializedSessionRole)
checkRole index sourceRole sourceReference resolved
  | resolvedSpecializedSessionSourceRole resolved /= sourceRole =
      Just
        (Left
          (GrammarV1SpecializedSessionRoleSourceMismatch
            index
            sourceRole
            (resolvedSpecializedSessionSourceRole resolved)))
  | genericStaticReferenceName target /= sourceName =
      Just
        (Left
          (GrammarV1SpecializedSessionTargetNameMismatch
            sourceName
            (genericStaticReferenceName target)))
  | genericStaticReferenceKind target /= GenericSessionKind =
      Just
        (Left
          (GrammarV1SpecializedSessionTargetKindMismatch
            sourceName
            (genericStaticReferenceKind target)))
  | otherwise = do
      checked <- grammarV1CheckedSpecializedStaticReference
        (resolvedSpecializedSessionDeclarationKey resolved)
        (resolvedSpecializedSessionInterfaceRevision resolved)
        (resolvedSpecializedSessionParameters resolved)
        (resolvedSpecializedSessionDirectArguments resolved)
        (resolvedSpecializedSessionArgumentReferences resolved)
        sourceReference
      pure $ case checked of
        Left err -> Left (GrammarV1SpecializedSessionStaticReferenceError err)
        Right result -> Right GrammarV1CheckedSpecializedSessionRole
          { checkedSpecializedSessionRoleKey =
              ProtocolRoleKey
                (locatedValue
                  (grammarV1RoleSessionName (locatedValue sourceRole)))
          , checkedSpecializedSessionTargetSemanticForm =
              genericStaticReferenceSemanticForm target
          , checkedSpecializedSessionReference = result
          }
  where
    target = resolvedSpecializedSessionTargetCandidate resolved
    sourceName = qualifiedNameText (grammarV1StaticReferenceName sourceReference)

qualifiedNameText :: GrammarV1QualifiedName -> Text
qualifiedNameText source =
  Text.intercalate (Text.singleton '.') (grammarV1QualifiedNameParts source)
