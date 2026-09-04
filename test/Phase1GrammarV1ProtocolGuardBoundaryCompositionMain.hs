{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  , GenericStaticParameter (..)
  , GenericStaticReferenceCandidate (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , Proposition (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolBoundaryAnnotations
  ( GrammarV1CheckedResolvedProtocolBoundaryAnnotation (..)
  , GrammarV1CheckedSpecializedProtocolBoundaryAnnotation (..)
  , GrammarV1ProtocolBoundaryAnnotation (..)
  , GrammarV1ProtocolBoundaryResolutionError (..)
  , GrammarV1ProtocolBoundarySite (..)
  , GrammarV1ResolvedProtocolBoundaryReference (..)
  , GrammarV1ResolvedSpecializedProtocolBoundary (..)
  )
import Phil.Surface.GrammarV1.ProtocolBoundaryComposition
  ( GrammarV1CheckedMixedProtocolBoundaryAnnotation (..)
  )
import Phil.Surface.GrammarV1.ProtocolGuardAnnotations
  ( GrammarV1CheckedProtocolGuardAnnotation (..)
  , GrammarV1ProtocolGuardError (..)
  , GrammarV1ProtocolGuardSite (..)
  )
import Phil.Surface.GrammarV1.ProtocolGuardBoundaryComposition
  ( GrammarV1CheckedGuardedProtocolBoundaries (..)
  , GrammarV1ClosedGuardBoundarySurface (..)
  , GrammarV1GuardBoundaryError (..)
  , grammarV1CheckedGuardBoundarySurface
  )
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1ResolvedDirectStaticArgument (..)
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 binder-free guards compose with resolved bare protocol boundaries"
        bareGuardBoundariesCompose
    , test "SURF-008 binder-free guards compose with specialized protocol boundaries"
        specializedGuardBoundariesCompose
    , test "SURF-008 binder-free guards compose with mixed boundary-reference shapes"
        mixedGuardBoundariesCompose
    , test "SURF-008 guard/boundary composition preserves competent failure provenance"
        guardBoundaryFailureProvenance
    , test "SURF-008 guard/boundary composition keeps live-binder guards for SURF-009"
        liveBinderGuardRemainsOutsideCompetence
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data BoundaryFlavor = BareBoundary | SpecializedBoundary
  deriving (Eq, Show)

bareGuardBoundariesCompose :: Either String ()
bareGuardBoundariesCompose = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol BareGuarded {"
    , "  role Client = send (outgoing : U8) using wire.Send when true then end Done;"
    , "  role Server = receive (incoming : U8) using wire.Receive when true then end Done;"
    , "}"
    ]
  (bareEvidence, specializedEvidence) <- boundaryEvidence protocol
  surface <- expectRightSurface bareEvidence specializedEvidence protocol
  let expectedTemplates =
        ( ( ProtocolRoleKey "Client"
          , ProtocolTemplateSend
              (Name "outgoing")
              (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateEnd (Outcome "Done"))
          )
        , ( ProtocolRoleKey "Server"
          , ProtocolTemplateReceive
              (Name "incoming")
              (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateEnd (Outcome "Done"))
          )
        )
  assert
    (checkedGuardBoundaryRoleTemplates surface == expectedTemplates)
    "bare guard/boundary composition changed underlying dual role templates"
  assert
    (guardSummary surface ==
      [ (ProtocolRoleKey "Client", GrammarV1SendGuard, Truth)
      , (ProtocolRoleKey "Server", GrammarV1ReceiveGuard, Truth)
      ])
    "bare boundary composition changed guard role/site/proposition order"
  assert
    (boundarySummary surface ==
      [ ( ProtocolRoleKey "Client"
        , GrammarV1SendBoundary
        , BareBoundary
        , SemanticAtom "boundary.wire.Send.resolved"
        )
      , ( ProtocolRoleKey "Server"
        , GrammarV1ReceiveBoundary
        , BareBoundary
        , SemanticAtom "boundary.wire.Receive.resolved"
        )
      ])
    "bare boundary identity or source preorder changed under guard composition"

specializedGuardBoundariesCompose :: Either String ()
specializedGuardBoundariesCompose = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol SpecializedGuarded {"
    , "  role Client = select { Go(x : U8) using wire.Go[U8] when true => end Done };"
    , "  role Server = offer { Go(y : U8) using wire.GoIn[U8] when true => end Done };"
    , "}"
    ]
  (bareEvidence, specializedEvidence) <- boundaryEvidence protocol
  surface <- expectRightSurface bareEvidence specializedEvidence protocol
  assert
    (guardSummary surface ==
      [ (ProtocolRoleKey "Client", GrammarV1SelectBranchGuard "Go", Truth)
      , (ProtocolRoleKey "Server", GrammarV1OfferBranchGuard "Go", Truth)
      ])
    "specialized branch guard semantics changed during composition"
  assert
    (boundarySummary surface ==
      [ ( ProtocolRoleKey "Client"
        , GrammarV1SelectBranchBoundary "Go"
        , SpecializedBoundary
        , SemanticAtom "boundary.wire.Go.checked"
        )
      , ( ProtocolRoleKey "Server"
        , GrammarV1OfferBranchBoundary "Go"
        , SpecializedBoundary
        , SemanticAtom "boundary.wire.GoIn.checked"
        )
      ])
    "specialized branch boundary semantics changed under guard composition"

mixedGuardBoundariesCompose :: Either String ()
mixedGuardBoundariesCompose = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol MixedGuarded {"
    , "  role Client = send (x : U8) using wire.Send when true then"
    , "    select { Go using wire.Go[U8] when true => end Done };"
    , "  role Server = receive (y : U8) using wire.Receive[U8] when true then"
    , "    offer { Go using wire.GoIn when true => end Done };"
    , "}"
    ]
  (bareEvidence, specializedEvidence) <- boundaryEvidence protocol
  surface <- expectRightSurface bareEvidence specializedEvidence protocol
  assert
    (guardSummary surface ==
      [ (ProtocolRoleKey "Client", GrammarV1SendGuard, Truth)
      , (ProtocolRoleKey "Client", GrammarV1SelectBranchGuard "Go", Truth)
      , (ProtocolRoleKey "Server", GrammarV1ReceiveGuard, Truth)
      , (ProtocolRoleKey "Server", GrammarV1OfferBranchGuard "Go", Truth)
      ])
    "mixed boundary composition changed guard source preorder"
  assert
    (boundarySummary surface ==
      [ ( ProtocolRoleKey "Client"
        , GrammarV1SendBoundary
        , BareBoundary
        , SemanticAtom "boundary.wire.Send.resolved"
        )
      , ( ProtocolRoleKey "Client"
        , GrammarV1SelectBranchBoundary "Go"
        , SpecializedBoundary
        , SemanticAtom "boundary.wire.Go.checked"
        )
      , ( ProtocolRoleKey "Server"
        , GrammarV1ReceiveBoundary
        , SpecializedBoundary
        , SemanticAtom "boundary.wire.Receive.checked"
        )
      , ( ProtocolRoleKey "Server"
        , GrammarV1OfferBranchBoundary "Go"
        , BareBoundary
        , SemanticAtom "boundary.wire.GoIn.resolved"
        )
      ])
    "mixed boundary category or source preorder changed under guard composition"

guardBoundaryFailureProvenance :: Either String ()
guardBoundaryFailureProvenance = do
  missingBoundary <- onlyProtocol $ Text.unlines
    [ "protocol MissingBoundaryEvidence {"
    , "  role Client = send (x : U8) using Wire when true then end Done;"
    , "  role Server = receive (y : U8) using Wire when true then end Done;"
    , "}"
    ]
  assert
    ( grammarV1CheckedGuardBoundarySurface
        emptyStaticContext [] [] missingBoundary
        == Just
          (Left
            (GrammarV1GuardBoundaryBareError
              (GrammarV1ResolvedProtocolBoundaryEvidenceCountMismatch 2 0)))
    )
    "missing boundary evidence did not remain a boundary-resolver failure"
  badGuard <- onlyProtocol $ Text.unlines
    [ "protocol BadGuard {"
    , "  role Client = send (x : U8) using Wire when Missing() then end Done;"
    , "  role Server = receive (y : U8) using Wire when true then end Done;"
    , "}"
    ]
  (badBareEvidence, badSpecializedEvidence) <- boundaryEvidence badGuard
  assert
    ( grammarV1CheckedGuardBoundarySurface
        emptyStaticContext badBareEvidence badSpecializedEvidence badGuard
        == Just
          (Left
            (GrammarV1GuardBoundaryGuardError
              (GrammarV1ProtocolGuardFocusingError
                0
                (ProtocolRoleKey "Client")
                GrammarV1SendGuard
                (UnknownClaim "Missing"))))
    )
    "guard focusing failure was hidden by boundary composition"
  bareOnly <- onlyProtocol $ Text.unlines
    [ "protocol Detached {"
    , "  role Client = send (x : U8) using Wire when true then end Done;"
    , "  role Server = receive (y : U8) using Wire when true then end Done;"
    , "}"
    ]
  (bareOnlyEvidence, _) <- boundaryEvidence bareOnly
  let detachedSpecialized = dummySpecializedEvidence
  assert
    ( grammarV1CheckedGuardBoundarySurface
        emptyStaticContext bareOnlyEvidence [detachedSpecialized] bareOnly
        == Just (Left (GrammarV1GuardBoundaryUnexpectedSpecializedEvidence 1))
    )
    "irrelevant specialized evidence was silently ignored on a bare protocol"

liveBinderGuardRemainsOutsideCompetence :: Either String ()
liveBinderGuardRemainsOutsideCompetence = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol BinderDependent {"
    , "  role Client = send (x : U8) using Wire when x == x then end Done;"
    , "  role Server = receive (y : U8) using Wire when y == y then end Done;"
    , "}"
    ]
  (bareEvidence, specializedEvidence) <- boundaryEvidence protocol
  assert
    ( grammarV1CheckedGuardBoundarySurface
        emptyStaticContext bareEvidence specializedEvidence protocol
        == Nothing
    )
    "boundary composition accidentally supplied live binder identity to guard checking"

guardSummary
  :: GrammarV1ClosedGuardBoundarySurface
  -> [(ProtocolRoleKey, GrammarV1ProtocolGuardSite, Proposition)]
guardSummary surface =
  [ ( checkedProtocolGuardRole annotation
    , checkedProtocolGuardSite annotation
    , checkedProtocolGuardProposition annotation
    )
  | annotation <- checkedGuardBoundaryGuards surface
  ]

boundarySummary
  :: GrammarV1ClosedGuardBoundarySurface
  -> [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, BoundaryFlavor, SemanticForm)]
boundarySummary surface = case checkedGuardBoundaryBoundaries surface of
  GrammarV1CheckedGuardedBareProtocolBoundaries annotations ->
    map summarizeBare annotations
  GrammarV1CheckedGuardedSpecializedProtocolBoundaries annotations ->
    map summarizeSpecialized annotations
  GrammarV1CheckedGuardedMixedProtocolBoundaries annotations ->
    map summarizeMixed annotations
  where
    summarizeBare annotation =
      ( checkedResolvedProtocolBoundaryRole annotation
      , checkedResolvedProtocolBoundarySite annotation
      , BareBoundary
      , checkedResolvedProtocolBoundarySemanticForm annotation
      )
    summarizeSpecialized annotation =
      ( checkedSpecializedProtocolBoundaryRole annotation
      , checkedSpecializedProtocolBoundarySite annotation
      , SpecializedBoundary
      , checkedSpecializedProtocolBoundaryTargetSemanticForm annotation
      )
    summarizeMixed checked = case checked of
      GrammarV1CheckedMixedBareProtocolBoundary annotation -> summarizeBare annotation
      GrammarV1CheckedMixedSpecializedProtocolBoundary annotation ->
        summarizeSpecialized annotation

expectRightSurface
  :: [GrammarV1ResolvedProtocolBoundaryReference]
  -> [GrammarV1ResolvedSpecializedProtocolBoundary]
  -> GrammarV1ProtocolDecl
  -> Either String GrammarV1ClosedGuardBoundarySurface
expectRightSurface bareEvidence specializedEvidence protocol =
  case grammarV1CheckedGuardBoundarySurface
      emptyStaticContext bareEvidence specializedEvidence protocol of
    Just (Right surface) -> Right surface
    other -> Left ("expected checked guard/boundary surface, got " <> show other)

boundaryEvidence
  :: GrammarV1ProtocolDecl
  -> Either String
      ( [GrammarV1ResolvedProtocolBoundaryReference]
      , [GrammarV1ResolvedSpecializedProtocolBoundary]
      )
boundaryEvidence protocol = do
  uses <- boundaryUses protocol
  bare <- mapM bareBoundaryEvidence
    [ boundaryUse
    | boundaryUse@(_, _, Located _ reference) <- uses
    , null (grammarV1StaticReferenceArguments reference)
    ]
  specialized <- mapM specializedBoundaryEvidence
    [ boundaryUse
    | boundaryUse@(_, _, Located _ reference) <- uses
    , not (null (grammarV1StaticReferenceArguments reference))
    ]
  pure (bare, specialized)

bareBoundaryEvidence
  :: (ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)
  -> Either String GrammarV1ResolvedProtocolBoundaryReference
bareBoundaryEvidence (roleKey, site, sourceReference@(Located _ reference)) =
  let targetName = qualifiedNameText (grammarV1StaticReferenceName reference)
      annotation = GrammarV1ProtocolBoundaryAnnotation
        { protocolBoundaryRole = roleKey
        , protocolBoundarySite = site
        , protocolBoundarySourceReference = sourceReference
        , protocolBoundaryStaticReference = ReferencedGenericStaticActual targetName
        }
  in Right GrammarV1ResolvedProtocolBoundaryReference
    { resolvedProtocolBoundarySourceAnnotation = annotation
    , resolvedProtocolBoundaryTargetCandidate = GenericStaticReferenceCandidate
        targetName
        GenericBoundaryContractKind
        (SemanticAtom ("boundary." <> targetName <> ".resolved"))
    , resolvedProtocolBoundaryDeclarationKey = DeclarationKey ("decl." <> targetName)
    , resolvedProtocolBoundaryInterfaceRevision =
        InterfaceRevision ("iface." <> targetName <> ".v1")
    }

specializedBoundaryEvidence
  :: (ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)
  -> Either String GrammarV1ResolvedSpecializedProtocolBoundary
specializedBoundaryEvidence (roleKey, site, sourceReference@(Located _ reference)) = do
  argument <- case grammarV1StaticReferenceArguments reference of
    [one] -> Right one
    other -> Left
      ("expected one specialized boundary argument, got " <> show (length other))
  let targetName = qualifiedNameText (grammarV1StaticReferenceName reference)
      typeKey = GenericStaticParameterKey ("protocol.boundary.type." <> targetName)
  Right GrammarV1ResolvedSpecializedProtocolBoundary
    { resolvedSpecializedProtocolBoundaryRole = roleKey
    , resolvedSpecializedProtocolBoundarySite = site
    , resolvedSpecializedProtocolBoundarySourceReference = sourceReference
    , resolvedSpecializedProtocolBoundaryTargetCandidate = GenericStaticReferenceCandidate
        targetName
        GenericBoundaryContractKind
        (SemanticAtom ("boundary." <> targetName <> ".checked"))
    , resolvedSpecializedProtocolBoundaryDeclarationKey = DeclarationKey ("decl." <> targetName)
    , resolvedSpecializedProtocolBoundaryInterfaceRevision =
        InterfaceRevision ("iface." <> targetName <> ".v1")
    , resolvedSpecializedProtocolBoundaryParameters =
        [GenericStaticParameter typeKey GenericTypeKind]
    , resolvedSpecializedProtocolBoundaryDirectArguments =
        [ GrammarV1ResolvedDirectStaticArgument
            argument
            GenericTypeKind
            (SemanticAtom "type.U8.checked")
        ]
    , resolvedSpecializedProtocolBoundaryArgumentReferences = []
    }

dummySpecializedEvidence :: GrammarV1ResolvedSpecializedProtocolBoundary
dummySpecializedEvidence = GrammarV1ResolvedSpecializedProtocolBoundary
  { resolvedSpecializedProtocolBoundaryRole = ProtocolRoleKey "Detached"
  , resolvedSpecializedProtocolBoundarySite = GrammarV1SendBoundary
  , resolvedSpecializedProtocolBoundarySourceReference =
      Located (error "detached evidence source span must not be inspected")
        (error "detached evidence source reference must not be inspected")
  , resolvedSpecializedProtocolBoundaryTargetCandidate = GenericStaticReferenceCandidate
      "Detached"
      GenericBoundaryContractKind
      (SemanticAtom "detached")
  , resolvedSpecializedProtocolBoundaryDeclarationKey = DeclarationKey "detached"
  , resolvedSpecializedProtocolBoundaryInterfaceRevision = InterfaceRevision "detached"
  , resolvedSpecializedProtocolBoundaryParameters = []
  , resolvedSpecializedProtocolBoundaryDirectArguments = []
  , resolvedSpecializedProtocolBoundaryArgumentReferences = []
  }

boundaryUses
  :: GrammarV1ProtocolDecl
  -> Either String
      [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)]
boundaryUses protocol = fmap concat (mapM roleUses (grammarV1ProtocolRoles protocol))

roleUses
  :: Located GrammarV1RoleSessionDecl
  -> Either String
      [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)]
roleUses (Located _ role) = sessionUses
  (ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role)))
  (locatedValue (grammarV1RoleSessionExpression role))

sessionUses
  :: ProtocolRoleKey
  -> GrammarV1SessionExpression
  -> Either String
      [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)]
sessionUses roleKey source = case source of
  GrammarV1SessionReference _ -> Right []
  GrammarV1SessionSend _ boundary _ continuation -> do
    rest <- sessionUses roleKey (locatedValue continuation)
    pure (oneUse roleKey GrammarV1SendBoundary boundary <> rest)
  GrammarV1SessionReceive _ boundary _ continuation -> do
    rest <- sessionUses roleKey (locatedValue continuation)
    pure (oneUse roleKey GrammarV1ReceiveBoundary boundary <> rest)
  GrammarV1SessionSelect branches -> fmap concat (mapM (branchUses True roleKey) branches)
  GrammarV1SessionOffer branches -> fmap concat (mapM (branchUses False roleKey) branches)
  GrammarV1SessionEnd _ -> Right []
  GrammarV1SessionRecursive _ body -> sessionUses roleKey (locatedValue body)
  GrammarV1SessionContinue _ -> Right []

branchUses
  :: Bool
  -> ProtocolRoleKey
  -> Located GrammarV1SessionBranch
  -> Either String
      [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)]
branchUses selecting roleKey (Located _ branch) = do
  let label = locatedValue (grammarV1SessionBranchLabel branch)
      site
        | selecting = GrammarV1SelectBranchBoundary label
        | otherwise = GrammarV1OfferBranchBoundary label
  rest <- sessionUses roleKey (locatedValue (grammarV1SessionBranchContinuation branch))
  pure (oneUse roleKey site (grammarV1SessionBranchBoundary branch) <> rest)

oneUse
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBoundarySite
  -> Maybe (Located GrammarV1StaticReference)
  -> [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)]
oneUse _ _ Nothing = []
oneUse roleKey site (Just sourceReference) = [(roleKey, site, sourceReference)]

qualifiedNameText :: GrammarV1QualifiedName -> Text.Text
qualifiedNameText source = Text.intercalate "." (grammarV1QualifiedNameParts source)

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "protocol-guard-boundary-composition" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left
      ("expected one protocol declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
