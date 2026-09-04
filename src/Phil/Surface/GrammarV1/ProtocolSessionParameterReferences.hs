module Phil.Surface.GrammarV1.ProtocolSessionParameterReferences
  ( GrammarV1ResolvedProtocolSessionParameter (..)
  , GrammarV1ResolvedProtocolSessionRoleReference (..)
  , GrammarV1ProtocolSessionParameterReferenceError (..)
  , grammarV1ResolvedSessionParameterRoleReferences
  ) where

import qualified Data.Set as Set
import Phil.Core.Generic (GenericStaticParameterKey)
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1GenericKind (..)
  , GrammarV1GenericParam (..)
  , GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact binder-resolution evidence for one source protocol Session parameter.
-- The full located source parameter is retained so this bridge can validate
-- correspondence without deriving a stable key from display spelling.
data GrammarV1ResolvedProtocolSessionParameter =
  GrammarV1ResolvedProtocolSessionParameter
    { resolvedProtocolSessionSourceParameter :: Located GrammarV1GenericParam
    , resolvedProtocolSessionParameter :: GenericStaticParameter
    }
  deriving (Eq, Show)

-- | Exact binder evidence for one whole role whose body is a direct reference to
-- a protocol Session parameter. The located role occurrence, rather than the
-- inner reference spelling, is the source-side identity available from Grammar
-- v1; the competent binder resolver supplies the semantic parameter key.
data GrammarV1ResolvedProtocolSessionRoleReference =
  GrammarV1ResolvedProtocolSessionRoleReference
    { resolvedProtocolSessionSourceRole :: Located GrammarV1RoleSessionDecl
    , resolvedProtocolSessionRoleParameterKey :: GenericStaticParameterKey
    }
  deriving (Eq, Show)

data GrammarV1ProtocolSessionParameterReferenceError
  = GrammarV1ProtocolSessionParameterEvidenceCountMismatch Int Int
  | GrammarV1ProtocolSessionParameterSourceMismatch
      Int
      (Located GrammarV1GenericParam)
      (Located GrammarV1GenericParam)
  | GrammarV1ProtocolSessionParameterKindMismatch
      GenericStaticParameterKey
      GenericStaticKind
  | GrammarV1DuplicateProtocolSessionParameterKey GenericStaticParameterKey
  | GrammarV1ProtocolSessionRoleEvidenceCountMismatch Int Int
  | GrammarV1ProtocolSessionRoleSourceMismatch
      Int
      (Located GrammarV1RoleSessionDecl)
      (Located GrammarV1RoleSessionDecl)
  | GrammarV1ProtocolSessionRoleUndeclaredParameter GenericStaticParameterKey
  deriving (Eq, Show)

-- | Preserve direct protocol Session-parameter role references using exact
-- caller-supplied binder evidence, while leaving binder resolution in SURF-009.
--
-- Every source generic parameter must have Session kind. Parameter evidence must
-- correspond to exact located parameters in declaration order, retain
-- GenericSessionKind, and carry distinct stable keys. Every one of the two role
-- bodies must be a bare unspecialized static session reference, and role evidence
-- must correspond to the exact located role occurrences in source order. The
-- source reference spelling is never consulted to select a semantic key.
--
-- The result remains only a role-to-GenericStaticParameterKey correspondence. It
-- does not instantiate a Session, assert role duality, construct a protocol
-- family, or discharge generic requirements. Requirement-bearing protocols,
-- inline sessions, specialization, and non-Session generic parameters remain
-- structural non-competence.
grammarV1ResolvedSessionParameterRoleReferences
  :: [GrammarV1ResolvedProtocolSessionParameter]
  -> [GrammarV1ResolvedProtocolSessionRoleReference]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolSessionParameterReferenceError
        ( (ProtocolRoleKey, GenericStaticParameterKey)
        , (ProtocolRoleKey, GenericStaticParameterKey)
        ))
grammarV1ResolvedSessionParameterRoleReferences parameterEvidence roleEvidence source
  | null sourceParameters = Nothing
  | not (all sourceParameterIsSession sourceParameters) = Nothing
  | not (null (grammarV1ProtocolRequirements source)) = Nothing
  | otherwise = case grammarV1ProtocolRoles source of
      [firstRole, secondRole]
        | directRoleReference firstRole && directRoleReference secondRole ->
            Just $ do
              parameterKeys <- validateParameterEvidence sourceParameters parameterEvidence
              validateRoleEvidence parameterKeys [firstRole, secondRole] roleEvidence
      _ -> Nothing
  where
    sourceParameters = grammarV1ProtocolGenericParams source

sourceParameterIsSession :: Located GrammarV1GenericParam -> Bool
sourceParameterIsSession (Located _ parameter) =
  locatedValue (grammarV1GenericParamKind parameter) == GrammarV1SessionKind

directRoleReference :: Located GrammarV1RoleSessionDecl -> Bool
directRoleReference (Located _ role) =
  case locatedValue (grammarV1RoleSessionExpression role) of
    GrammarV1SessionReference reference ->
      null (grammarV1StaticReferenceArguments reference)
    _ -> False

validateParameterEvidence
  :: [Located GrammarV1GenericParam]
  -> [GrammarV1ResolvedProtocolSessionParameter]
  -> Either
      GrammarV1ProtocolSessionParameterReferenceError
      (Set.Set GenericStaticParameterKey)
validateParameterEvidence sourceParameters evidence
  | length sourceParameters /= length evidence = Left
      (GrammarV1ProtocolSessionParameterEvidenceCountMismatch
        (length sourceParameters)
        (length evidence))
  | otherwise = go 0 Set.empty sourceParameters evidence
  where
    go _ keys [] [] = Right keys
    go index keys (sourceParameter : sourceRest) (resolved : resolvedRest)
      | sourceParameter /= resolvedProtocolSessionSourceParameter resolved = Left
          (GrammarV1ProtocolSessionParameterSourceMismatch
            index
            sourceParameter
            (resolvedProtocolSessionSourceParameter resolved))
      | genericStaticParameterKind parameter /= GenericSessionKind = Left
          (GrammarV1ProtocolSessionParameterKindMismatch
            key
            (genericStaticParameterKind parameter))
      | Set.member key keys = Left
          (GrammarV1DuplicateProtocolSessionParameterKey key)
      | otherwise = go
          (index + 1)
          (Set.insert key keys)
          sourceRest
          resolvedRest
      where
        parameter = resolvedProtocolSessionParameter resolved
        key = genericStaticParameterKey parameter
    go _ _ _ _ = Left
      (GrammarV1ProtocolSessionParameterEvidenceCountMismatch
        (length sourceParameters)
        (length evidence))

validateRoleEvidence
  :: Set.Set GenericStaticParameterKey
  -> [Located GrammarV1RoleSessionDecl]
  -> [GrammarV1ResolvedProtocolSessionRoleReference]
  -> Either
      GrammarV1ProtocolSessionParameterReferenceError
      ( (ProtocolRoleKey, GenericStaticParameterKey)
      , (ProtocolRoleKey, GenericStaticParameterKey)
      )
validateRoleEvidence parameterKeys sourceRoles evidence
  | length sourceRoles /= length evidence = Left
      (GrammarV1ProtocolSessionRoleEvidenceCountMismatch
        (length sourceRoles)
        (length evidence))
  | otherwise = do
      checked <- sequence
        [ validateOne index sourceRole resolved
        | (index, (sourceRole, resolved)) <- zip [0 ..] (zip sourceRoles evidence)
        ]
      case checked of
        [first, second] -> Right (first, second)
        _ -> Left
          (GrammarV1ProtocolSessionRoleEvidenceCountMismatch
            (length sourceRoles)
            (length evidence))
  where
    validateOne index sourceRole resolved
      | sourceRole /= resolvedProtocolSessionSourceRole resolved = Left
          (GrammarV1ProtocolSessionRoleSourceMismatch
            index
            sourceRole
            (resolvedProtocolSessionSourceRole resolved))
      | not (Set.member key parameterKeys) = Left
          (GrammarV1ProtocolSessionRoleUndeclaredParameter key)
      | otherwise = Right
          ( ProtocolRoleKey
              (locatedValue
                (grammarV1RoleSessionName (locatedValue sourceRole)))
          , key
          )
      where
        key = resolvedProtocolSessionRoleParameterKey resolved
