{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError (..)
  )
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
  ( GrammarV1ProtocolBoundaryAnnotation (..)
  , GrammarV1ProtocolBoundarySite (..)
  , GrammarV1ResolvedProtocolBoundaryReference (..)
  , GrammarV1ResolvedSpecializedProtocolBoundary (..)
  )
import Phil.Surface.GrammarV1.ProtocolGuardAnnotations
  ( GrammarV1CheckedProtocolGuardAnnotation (..)
  , GrammarV1ClosedProtocolGuardSurface (..)
  , GrammarV1ProtocolGuardError (..)
  , GrammarV1ProtocolGuardSite (..)
  , grammarV1CheckedClosedProtocolGuardSurface
  )
import Phil.Surface.GrammarV1.ProtocolGuardBoundaryComposition
  ( GrammarV1CheckedGuardedProtocolBoundaries (..)
  , GrammarV1ClosedGuardBoundarySurface (..)
  , grammarV1CheckedGuardBoundarySurface
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  )
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1ResolvedDirectStaticArgument (..)
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed message guards preserve exact checked propositions"
        messageGuardsPreserved
    , test "SURF-008 closed branch guards preserve role, site, and source preorder"
        branchGuardsPreserved
    , test "SURF-008 protocol guards cannot bypass checked role duality"
        guardsPreserveDualityFailure
    , test "SURF-008 protocol guard Core focusing failures remain explicit"
        guardFocusingFailure
    , test "SURF-008 protocol guard routing preserves binder and boundary competence walls"
        guardCompetenceBoundaries
    , test "SURF-008 binder-free guards compose with bare specialized and mixed boundaries"
        guardBoundaryComposition
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

messageGuardsPreserved :: Either String ()
messageGuardsPreserved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol P {"
    , "  role Client = send (outgoing : U8) when true then end Done;"
    , "  role Server = receive (incoming : U8) when true then end Done;"
    , "}"
    ]
  surface <- expectRightSurface protocol
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
      expectedGuards =
        [ (ProtocolRoleKey "Client", GrammarV1SendGuard, Truth, [])
        , (ProtocolRoleKey "Server", GrammarV1ReceiveGuard, Truth, [])
        ]
  assert
    (checkedProtocolGuardRoleTemplates surface == expectedTemplates)
    "guard stripping changed the checked underlying protocol templates"
  assert
    (guardSummary surface == expectedGuards)
    "message guard proposition, site, role, or focusing trace changed"

branchGuardsPreserved :: Either String ()
branchGuardsPreserved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Branches {"
    , "  role Client = select {"
    , "    Go(x : U8) when true => end Done"
    , "    | Stop when true => end Done"
    , "  };"
    , "  role Server = offer {"
    , "    Go(y : U8) when true => end Done"
    , "    | Stop when true => end Done"
    , "  };"
    , "}"
    ]
  surface <- expectRightSurface protocol
  let expected =
        [ ( ProtocolRoleKey "Client"
          , GrammarV1SelectBranchGuard "Go"
          , Truth
          , []
          )
        , ( ProtocolRoleKey "Client"
          , GrammarV1SelectBranchGuard "Stop"
          , Truth
          , []
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchGuard "Go"
          , Truth
          , []
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchGuard "Stop"
          , Truth
          , []
          )
        ]
  assert
    (guardSummary surface == expected)
    "branch guard role/site/proposition source preorder changed"

guardsPreserveDualityFailure :: Either String ()
guardsPreserveDualityFailure = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Bad {"
    , "  role Client = send (x : U8) when true then end Left;"
    , "  role Server = receive (y : U8) when true then end Right;"
    , "}"
    ]
  assert
    ( grammarV1CheckedClosedProtocolGuardSurface emptyStaticContext protocol
        == Just
          (Left
            (GrammarV1ProtocolGuardRoleError
              (NonDualProtocolRoles
                (ProtocolRoleKey "Client")
                (ProtocolRoleKey "Server"))))
    )
    "guard stripping made a non-dual protocol acceptable"

guardFocusingFailure :: Either String ()
guardFocusingFailure = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol BadGuard {"
    , "  role Client = send (x : U8) when Missing() then end Done;"
    , "  role Server = receive (y : U8) when true then end Done;"
    , "}"
    ]
  assert
    ( grammarV1CheckedClosedProtocolGuardSurface emptyStaticContext protocol
        == Just
          (Left
            (GrammarV1ProtocolGuardFocusingError
              0
              (ProtocolRoleKey "Client")
              GrammarV1SendGuard
              (UnknownClaim "Missing")))
    )
    "unknown guard claim collapsed into source non-competence"

guardCompetenceBoundaries :: Either String ()
guardCompetenceBoundaries = do
  binderDependent <- onlyProtocol $ Text.unlines
    [ "protocol BinderDependent {"
    , "  role Client = send (x : U8) when x == x then end Done;"
    , "  role Server = receive (y : U8) when y == y then end Done;"
    , "}"
    ]
  branchBinderDependent <- onlyProtocol $ Text.unlines
    [ "protocol BranchBinderDependent {"
    , "  role Client = select { Go(x : U8) when x == x => end Done };"
    , "  role Server = offer { Go(y : U8) when y == y => end Done };"
    , "}"
    ]
  boundaryBearing <- onlyProtocol $ Text.unlines
    [ "protocol BoundaryBearing {"
    , "  role Client = send (x : U8) using Wire when true then end Done;"
    , "  role Server = receive (y : U8) using Wire when true then end Done;"
    , "}"
    ]
  unguarded <- onlyProtocol $ Text.unlines
    [ "protocol Unguarded {"
    , "  role Client = send (x : U8) then end Done;"
    , "  role Server = receive (y : U8) then end Done;"
    , "}"
    ]
  generic <- onlyProtocol $ Text.unlines
    [ "protocol Generic[T : Type] {"
    , "  role Client = send (x : U8) when true then end Done;"
    , "  role Server = receive (y : U8) when true then end Done;"
    , "}"
    ]
  mapM_ (\(label, protocol) ->
    assert
      (grammarV1CheckedClosedProtocolGuardSurface emptyStaticContext protocol == Nothing)
      (label <> " escaped the closed context-free guard competence wall"))
    [ ("message-binder-dependent guards", binderDependent)
    , ("branch-payload-binder-dependent guards", branchBinderDependent)
    , ("boundary-bearing guarded protocol", boundaryBearing)
    , ("protocol without guards", unguarded)
    , ("generic guarded protocol", generic)
    ]

guardBoundaryComposition :: Either String ()
guardBoundaryComposition = do
  bare <- onlyProtocol $ Text.unlines
    [ "protocol GuardedBare {"
    , "  role Client = send (x : U8) using WireOut when true then end Done;"
    , "  role Server = receive (y : U8) using WireIn when true then end Done;"
    , "}"
    ]
  specialized <- onlyProtocol $ Text.unlines
    [ "protocol GuardedSpecialized {"
    , "  role Client = send (x : U8) using WireOut[U8] when true then end Done;"
    , "  role Server = receive (y : U8) using WireIn[U8] when true then end Done;"
    , "}"
    ]
  mixed <- onlyProtocol $ Text.unlines
    [ "protocol GuardedMixed {"
    , "  role Client = send (x : U8) using WireOut when true then end Done;"
    , "  role Server = receive (y : U8) using WireIn[U8] when true then end Done;"
    , "}"
    ]
  bareSurface <- checkedGuardBoundary bare
  specializedSurface <- checkedGuardBoundary specialized
  mixedSurface <- checkedGuardBoundary mixed
  assert
    (boundaryKind bareSurface == "bare")
    "guard composition did not retain the resolved bare-boundary authority"
  assert
    (boundaryKind specializedSurface == "specialized")
    "guard composition did not retain the specialized-boundary authority"
  assert
    (boundaryKind mixedSurface == "mixed")
    "guard composition did not retain both boundary-reference authorities"
  mapM_ (\surface -> do
    assert
      (length (checkedGuardBoundaryGuards surface) == 2)
      "guard composition lost a source guard"
    assert
      (all ((== Truth) . checkedProtocolGuardProposition)
        (checkedGuardBoundaryGuards surface))
      "guard composition changed a checked proposition"
    ) [bareSurface, specializedSurface, mixedSurface]
  binderDependent <- onlyProtocol $ Text.unlines
    [ "protocol GuardedBinderDependent {"
    , "  role Client = send (x : U8) using WireOut when x == x then end Done;"
    , "  role Server = receive (y : U8) using WireIn[U8] when y == y then end Done;"
    , "}"
    ]
  (binderBareEvidence, binderSpecializedEvidence) <- messageBoundaryEvidence binderDependent
  assert
    ( grammarV1CheckedGuardBoundarySurface
        emptyStaticContext
        binderBareEvidence
        binderSpecializedEvidence
        binderDependent
        == Nothing
    )
    "boundary composition accidentally resolved live guard binders before SURF-009"

checkedGuardBoundary
  :: GrammarV1ProtocolDecl
  -> Either String GrammarV1ClosedGuardBoundarySurface
checkedGuardBoundary protocol = do
  (bareEvidence, specializedEvidence) <- messageBoundaryEvidence protocol
  case grammarV1CheckedGuardBoundarySurface
      emptyStaticContext bareEvidence specializedEvidence protocol of
    Just (Right surface) -> Right surface
    other -> Left ("expected checked guard/boundary composition, got " <> show other)

boundaryKind :: GrammarV1ClosedGuardBoundarySurface -> String
boundaryKind surface = case checkedGuardBoundaryBoundaries surface of
  GrammarV1CheckedGuardedBareProtocolBoundaries _ -> "bare"
  GrammarV1CheckedGuardedSpecializedProtocolBoundaries _ -> "specialized"
  GrammarV1CheckedGuardedMixedProtocolBoundaries _ -> "mixed"

messageBoundaryEvidence
  :: GrammarV1ProtocolDecl
  -> Either String
      ( [GrammarV1ResolvedProtocolBoundaryReference]
      , [GrammarV1ResolvedSpecializedProtocolBoundary]
      )
messageBoundaryEvidence protocol = do
  uses <- mapM messageBoundaryUse (grammarV1ProtocolRoles protocol)
  bareEvidence <- mapM bareBoundaryEvidence
    [ use
    | use@(_, _, Located _ reference) <- uses
    , null (grammarV1StaticReferenceArguments reference)
    ]
  specializedEvidence <- mapM specializedBoundaryEvidence
    [ use
    | use@(_, _, Located _ reference) <- uses
    , not (null (grammarV1StaticReferenceArguments reference))
    ]
  pure (bareEvidence, specializedEvidence)

messageBoundaryUse
  :: Located GrammarV1RoleSessionDecl
  -> Either String
      (ProtocolRoleKey, GrammarV1ProtocolBoundarySite, Located GrammarV1StaticReference)
messageBoundaryUse (Located _ role) =
  let roleKey = ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
  in case locatedValue (grammarV1RoleSessionExpression role) of
    GrammarV1SessionSend _ (Just reference) _ _ ->
      Right (roleKey, GrammarV1SendBoundary, reference)
    GrammarV1SessionReceive _ (Just reference) _ _ ->
      Right (roleKey, GrammarV1ReceiveBoundary, reference)
    other -> Left ("expected one boundary-bearing message session, got " <> show other)

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

qualifiedNameText :: GrammarV1QualifiedName -> Text.Text
qualifiedNameText source = Text.intercalate "." (grammarV1QualifiedNameParts source)

guardSummary
  :: GrammarV1ClosedProtocolGuardSurface
  -> [(ProtocolRoleKey, GrammarV1ProtocolGuardSite, Proposition, [FocusStep])]
guardSummary surface =
  [ ( checkedProtocolGuardRole annotation
    , checkedProtocolGuardSite annotation
    , checkedProtocolGuardProposition annotation
    , checkedProtocolGuardFocusTrace annotation
    )
  | annotation <- checkedProtocolGuardAnnotations surface
  ]

expectRightSurface
  :: GrammarV1ProtocolDecl
  -> Either String GrammarV1ClosedProtocolGuardSurface
expectRightSurface protocol =
  case grammarV1CheckedClosedProtocolGuardSurface emptyStaticContext protocol of
    Just (Right surface) -> Right surface
    other -> Left ("expected checked protocol guard surface, got " <> show other)

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "protocol-guard-annotations" source
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
