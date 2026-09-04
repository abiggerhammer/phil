{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
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
  )
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolBoundaryAnnotations
  ( GrammarV1CheckedSpecializedProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedProtocolBoundarySurface (..)
  , GrammarV1ClosedSpecializedProtocolBoundarySurface (..)
  , GrammarV1ProtocolBoundaryAnnotation (..)
  , GrammarV1ProtocolBoundarySite (..)
  , GrammarV1ProtocolSpecializedBoundaryError (..)
  , GrammarV1ResolvedSpecializedProtocolBoundary (..)
  , grammarV1CheckedClosedProtocolBoundarySurface
  , grammarV1CheckedSpecializedProtocolBoundarySurface
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  )
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1ResolvedDirectStaticArgument (..)
  , GrammarV1SpecializedStaticReferenceError (..)
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed protocol boundaries preserve exact unresolved static identity"
        messageBoundariesPreserved
    , test "SURF-008 branch boundary annotations preserve role, branch site, and source order"
        branchBoundariesPreserved
    , test "SURF-008 boundary annotations cannot bypass checked protocol duality"
        boundarySurfacePreservesDualityFailure
    , test "SURF-008 protocol boundary surface remains fail-closed for guards and specialization"
        boundaryCompetenceBoundaries
    , test "SURF-008 specialized protocol boundaries consume checked static-application evidence"
        specializedMessageBoundariesChecked
    , test "SURF-008 specialized branch boundaries preserve exact source site and order"
        specializedBranchBoundariesChecked
    , test "SURF-008 specialized protocol boundaries reject detached or wrong resolver evidence"
        specializedBoundaryEvidenceBoundaries
    , test "SURF-008 specialized protocol boundary routing preserves its competence wall"
        specializedBoundaryCompetenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

messageBoundariesPreserved :: Either String ()
messageBoundariesPreserved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol P {"
    , "  role Client = send (outgoing : U8) using wire.Send then end Done;"
    , "  role Server = receive (incoming : U8) using wire.Receive then end Done;"
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
      expectedAnnotations =
        [ ( ProtocolRoleKey "Client"
          , GrammarV1SendBoundary
          , ReferencedGenericStaticActual "wire.Send"
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1ReceiveBoundary
          , ReferencedGenericStaticActual "wire.Receive"
          )
        ]
  assert
    (checkedProtocolBoundaryRoleTemplates surface == expectedTemplates)
    "boundary stripping changed the checked underlying protocol templates"
  assert
    (annotationSummary surface == expectedAnnotations)
    "message boundary annotation identity or source order changed"

branchBoundariesPreserved :: Either String ()
branchBoundariesPreserved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol P {"
    , "  role Client = select {"
    , "    Go(x : U8) using wire.GoOut => end Done"
    , "    | Stop using wire.StopOut => end Done"
    , "  };"
    , "  role Server = offer {"
    , "    Go(y : U8) using wire.GoIn => end Done"
    , "    | Stop using wire.StopIn => end Done"
    , "  };"
    , "}"
    ]
  surface <- expectRightSurface protocol
  let expected =
        [ ( ProtocolRoleKey "Client"
          , GrammarV1SelectBranchBoundary "Go"
          , ReferencedGenericStaticActual "wire.GoOut"
          )
        , ( ProtocolRoleKey "Client"
          , GrammarV1SelectBranchBoundary "Stop"
          , ReferencedGenericStaticActual "wire.StopOut"
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchBoundary "Go"
          , ReferencedGenericStaticActual "wire.GoIn"
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchBoundary "Stop"
          , ReferencedGenericStaticActual "wire.StopIn"
          )
        ]
  assert
    (annotationSummary surface == expected)
    "branch boundary annotations lost role/site distinction or source preorder"

boundarySurfacePreservesDualityFailure :: Either String ()
boundarySurfacePreservesDualityFailure = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol P {"
    , "  role Client = send (x : U8) using Wire then end Left;"
    , "  role Server = receive (y : U8) using Wire then end Right;"
    , "}"
    ]
  assert
    ( grammarV1CheckedClosedProtocolBoundarySurface protocol
        == Just
          (Left
            (NonDualProtocolRoles
              (ProtocolRoleKey "Client")
              (ProtocolRoleKey "Server")))
    )
    "boundary stripping made a non-dual protocol acceptable"

boundaryCompetenceBoundaries :: Either String ()
boundaryCompetenceBoundaries = do
  guarded <- onlyProtocol $ Text.unlines
    [ "protocol Guarded {"
    , "  role A = send (x : U8) using Wire when true then end Done;"
    , "  role B = receive (y : U8) using Wire when true then end Done;"
    , "}"
    ]
  specialized <- onlyProtocol $ Text.unlines
    [ "protocol Specialized {"
    , "  role A = send (x : U8) using Wire[U8] then end Done;"
    , "  role B = receive (y : U8) using Wire[U8] then end Done;"
    , "}"
    ]
  generic <- onlyProtocol $ Text.unlines
    [ "protocol Generic[T : Type] {"
    , "  role A = send (x : U8) using Wire then end Done;"
    , "  role B = receive (y : U8) using Wire then end Done;"
    , "}"
    ]
  mapM_ (\(label, protocol) ->
    assert
      (grammarV1CheckedClosedProtocolBoundarySurface protocol == Nothing)
      (label <> " escaped the closed boundary-annotation competence wall"))
    [ ("guard-bearing protocol", guarded)
    , ("specialized boundary reference", specialized)
    , ("generic protocol", generic)
    ]

specializedMessageBoundariesChecked :: Either String ()
specializedMessageBoundariesChecked = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Specialized {"
    , "  role Client = send (outgoing : U8) using wire.Send[U8] then end Done;"
    , "  role Server = receive (incoming : U8) using wire.Receive[U8] then end Done;"
    , "}"
    ]
  surface <- expectRightSpecializedSurface protocol
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
      expectedAnnotations =
        [ ( ProtocolRoleKey "Client"
          , GrammarV1SendBoundary
          , SemanticAtom "boundary.wire.Send.checked"
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1ReceiveBoundary
          , SemanticAtom "boundary.wire.Receive.checked"
          )
        ]
  assert
    (checkedSpecializedProtocolBoundaryRoleTemplates surface == expectedTemplates)
    "specialized boundary stripping changed the checked underlying protocol templates"
  assert
    (specializedAnnotationSummary surface == expectedAnnotations)
    "specialized message boundary target/category evidence was not preserved exactly"

specializedBranchBoundariesChecked :: Either String ()
specializedBranchBoundariesChecked = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol SpecializedBranches {"
    , "  role Client = select {"
    , "    Go(x : U8) using wire.GoOut[U8] => end Done"
    , "    | Stop using wire.StopOut[U8] => end Done"
    , "  };"
    , "  role Server = offer {"
    , "    Go(y : U8) using wire.GoIn[U8] => end Done"
    , "    | Stop using wire.StopIn[U8] => end Done"
    , "  };"
    , "}"
    ]
  surface <- expectRightSpecializedSurface protocol
  let expected =
        [ ( ProtocolRoleKey "Client"
          , GrammarV1SelectBranchBoundary "Go"
          , SemanticAtom "boundary.wire.GoOut.checked"
          )
        , ( ProtocolRoleKey "Client"
          , GrammarV1SelectBranchBoundary "Stop"
          , SemanticAtom "boundary.wire.StopOut.checked"
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchBoundary "Go"
          , SemanticAtom "boundary.wire.GoIn.checked"
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchBoundary "Stop"
          , SemanticAtom "boundary.wire.StopIn.checked"
          )
        ]
  assert
    (specializedAnnotationSummary surface == expected)
    "specialized branch boundaries lost exact role/site/source preorder"

specializedBoundaryEvidenceBoundaries :: Either String ()
specializedBoundaryEvidenceBoundaries = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Evidence {"
    , "  role Client = send (x : U8) using Wire[U8] then end Done;"
    , "  role Server = receive (y : U8) using Wire[U8] then end Done;"
    , "}"
    ]
  evidence <- specializedBoundaryEvidence protocol
  case evidence of
    [first, second] -> do
      case grammarV1CheckedSpecializedProtocolBoundarySurface
          [second, first] protocol of
        Just
          (Left
            (GrammarV1SpecializedProtocolBoundaryRoleMismatch
              0
              (ProtocolRoleKey "Client")
              (ProtocolRoleKey "Server"))) -> Right ()
        other -> Left
          ("specialized boundary evidence detached from exact source occurrence: "
            <> show other)
      let wrongName = first
            { resolvedSpecializedProtocolBoundaryTargetCandidate =
                (resolvedSpecializedProtocolBoundaryTargetCandidate first)
                  { genericStaticReferenceName = "Other" }
            }
      assert
        ( grammarV1CheckedSpecializedProtocolBoundarySurface
            [wrongName, second] protocol
            == Just
              (Left
                (GrammarV1SpecializedProtocolBoundaryTargetNameMismatch
                  0 "Wire" "Other"))
        )
        "wrong specialized boundary target name was accepted"
      let wrongKind = first
            { resolvedSpecializedProtocolBoundaryTargetCandidate =
                (resolvedSpecializedProtocolBoundaryTargetCandidate first)
                  { genericStaticReferenceKind = GenericTypeKind }
            }
      assert
        ( grammarV1CheckedSpecializedProtocolBoundarySurface
            [wrongKind, second] protocol
            == Just
              (Left
                (GrammarV1SpecializedProtocolBoundaryTargetKindMismatch
                  0 "Wire" GenericTypeKind))
        )
        "non-Boundary target candidate was accepted at a specialized protocol boundary"
      let missingArgumentEvidence = first
            { resolvedSpecializedProtocolBoundaryDirectArguments = [] }
      case grammarV1CheckedSpecializedProtocolBoundarySurface
          [missingArgumentEvidence, second] protocol of
        Just
          (Left
            (GrammarV1SpecializedProtocolBoundaryStaticReferenceError
              0
              (GrammarV1MissingDirectStaticArgumentEvidence _))) -> Right ()
        other -> Left
          ("missing specialized boundary argument evidence was not preserved: "
            <> show other)
      assert
        ( grammarV1CheckedSpecializedProtocolBoundarySurface [] protocol
            == Just
              (Left
                (GrammarV1SpecializedProtocolBoundaryEvidenceCountMismatch 2 0))
        )
        "missing specialized boundary occurrence evidence did not reject explicitly"
    other -> Left
      ("expected two specialized boundary evidence entries, got "
        <> show (length other))

specializedBoundaryCompetenceBoundaries :: Either String ()
specializedBoundaryCompetenceBoundaries = do
  bare <- onlyProtocol $ Text.unlines
    [ "protocol Bare {"
    , "  role A = send (x : U8) using Wire then end Done;"
    , "  role B = receive (y : U8) using Wire then end Done;"
    , "}"
    ]
  mixed <- onlyProtocol $ Text.unlines
    [ "protocol Mixed {"
    , "  role A = send (x : U8) using Wire[U8] then end Done;"
    , "  role B = receive (y : U8) using Wire then end Done;"
    , "}"
    ]
  guarded <- onlyProtocol $ Text.unlines
    [ "protocol Guarded {"
    , "  role A = send (x : U8) using Wire[U8] when true then end Done;"
    , "  role B = receive (y : U8) using Wire[U8] when true then end Done;"
    , "}"
    ]
  absent <- onlyProtocol $ Text.unlines
    [ "protocol Absent {"
    , "  role A = send (x : U8) then end Done;"
    , "  role B = receive (y : U8) then end Done;"
    , "}"
    ]
  generic <- onlyProtocol $ Text.unlines
    [ "protocol Generic[T : Type] {"
    , "  role A = send (x : U8) using Wire[U8] then end Done;"
    , "  role B = receive (y : U8) using Wire[U8] then end Done;"
    , "}"
    ]
  mapM_ (\(label, protocol) ->
    assert
      (grammarV1CheckedSpecializedProtocolBoundarySurface [] protocol == Nothing)
      (label <> " escaped the specialized boundary competence wall"))
    [ ("bare boundary reference", bare)
    , ("mixed bare/specialized boundary references", mixed)
    , ("guard-bearing specialized boundary protocol", guarded)
    , ("protocol without boundary annotations", absent)
    , ("generic specialized-boundary protocol", generic)
    ]

annotationSummary
  :: GrammarV1ClosedProtocolBoundarySurface
  -> [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, GenericStaticActual)]
annotationSummary surface =
  [ ( protocolBoundaryRole annotation
    , protocolBoundarySite annotation
    , protocolBoundaryStaticReference annotation
    )
  | annotation <- checkedProtocolBoundaryAnnotations surface
  ]

specializedAnnotationSummary
  :: GrammarV1ClosedSpecializedProtocolBoundarySurface
  -> [(ProtocolRoleKey, GrammarV1ProtocolBoundarySite, SemanticForm)]
specializedAnnotationSummary surface =
  [ ( checkedSpecializedProtocolBoundaryRole annotation
    , checkedSpecializedProtocolBoundarySite annotation
    , checkedSpecializedProtocolBoundaryTargetSemanticForm annotation
    )
  | annotation <- checkedSpecializedProtocolBoundaryAnnotations surface
  ]

expectRightSurface
  :: GrammarV1ProtocolDecl
  -> Either String GrammarV1ClosedProtocolBoundarySurface
expectRightSurface protocol =
  case grammarV1CheckedClosedProtocolBoundarySurface protocol of
    Just (Right surface) -> Right surface
    other -> Left ("expected checked boundary surface, got " <> show other)

expectRightSpecializedSurface
  :: GrammarV1ProtocolDecl
  -> Either String GrammarV1ClosedSpecializedProtocolBoundarySurface
expectRightSpecializedSurface protocol = do
  evidence <- specializedBoundaryEvidence protocol
  case grammarV1CheckedSpecializedProtocolBoundarySurface evidence protocol of
    Just (Right surface) -> Right surface
    other -> Left
      ("expected checked specialized boundary surface, got " <> show other)

specializedBoundaryEvidence
  :: GrammarV1ProtocolDecl
  -> Either String [GrammarV1ResolvedSpecializedProtocolBoundary]
specializedBoundaryEvidence protocol = do
  occurrences <- boundaryOccurrences protocol
  mapM specializedBoundaryOccurrenceEvidence occurrences

boundaryOccurrences
  :: GrammarV1ProtocolDecl
  -> Either String
      [ ( ProtocolRoleKey
        , GrammarV1ProtocolBoundarySite
        , Located GrammarV1StaticReference
        )
      ]
boundaryOccurrences protocol =
  fmap concat (mapM roleOccurrences (grammarV1ProtocolRoles protocol))

roleOccurrences
  :: Located GrammarV1RoleSessionDecl
  -> Either String
      [ ( ProtocolRoleKey
        , GrammarV1ProtocolBoundarySite
        , Located GrammarV1StaticReference
        )
      ]
roleOccurrences (Located _ role) =
  sessionOccurrences
    (ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role)))
    (locatedValue (grammarV1RoleSessionExpression role))

sessionOccurrences
  :: ProtocolRoleKey
  -> GrammarV1SessionExpression
  -> Either String
      [ ( ProtocolRoleKey
        , GrammarV1ProtocolBoundarySite
        , Located GrammarV1StaticReference
        )
      ]
sessionOccurrences roleKey source = case source of
  GrammarV1SessionReference _ -> Right []
  GrammarV1SessionSend _ boundary _ continuation -> do
    rest <- sessionOccurrences roleKey (locatedValue continuation)
    pure (occurrence roleKey GrammarV1SendBoundary boundary <> rest)
  GrammarV1SessionReceive _ boundary _ continuation -> do
    rest <- sessionOccurrences roleKey (locatedValue continuation)
    pure (occurrence roleKey GrammarV1ReceiveBoundary boundary <> rest)
  GrammarV1SessionSelect branches ->
    fmap concat (mapM (branchOccurrences True roleKey) branches)
  GrammarV1SessionOffer branches ->
    fmap concat (mapM (branchOccurrences False roleKey) branches)
  GrammarV1SessionEnd _ -> Right []
  GrammarV1SessionRecursive _ body ->
    sessionOccurrences roleKey (locatedValue body)
  GrammarV1SessionContinue _ -> Right []

branchOccurrences
  :: Bool
  -> ProtocolRoleKey
  -> Located GrammarV1SessionBranch
  -> Either String
      [ ( ProtocolRoleKey
        , GrammarV1ProtocolBoundarySite
        , Located GrammarV1StaticReference
        )
      ]
branchOccurrences selecting roleKey (Located _ branch) = do
  let label = locatedValue (grammarV1SessionBranchLabel branch)
      site
        | selecting = GrammarV1SelectBranchBoundary label
        | otherwise = GrammarV1OfferBranchBoundary label
  rest <- sessionOccurrences
    roleKey
    (locatedValue (grammarV1SessionBranchContinuation branch))
  pure (occurrence roleKey site (grammarV1SessionBranchBoundary branch) <> rest)

occurrence
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBoundarySite
  -> Maybe (Located GrammarV1StaticReference)
  -> [ ( ProtocolRoleKey
       , GrammarV1ProtocolBoundarySite
       , Located GrammarV1StaticReference
       )
     ]
occurrence _ _ Nothing = []
occurrence roleKey site (Just sourceReference) =
  [(roleKey, site, sourceReference)]

specializedBoundaryOccurrenceEvidence
  :: ( ProtocolRoleKey
     , GrammarV1ProtocolBoundarySite
     , Located GrammarV1StaticReference
     )
  -> Either String GrammarV1ResolvedSpecializedProtocolBoundary
specializedBoundaryOccurrenceEvidence (roleKey, site, sourceReference@(Located _ reference)) = do
  argument <- case grammarV1StaticReferenceArguments reference of
    [one] -> Right one
    other -> Left
      ("expected one specialized boundary argument, got " <> show (length other))
  let targetName = qualifiedNameText (grammarV1StaticReferenceName reference)
      typeKey = GenericStaticParameterKey
        ("protocol.boundary.type." <> targetName)
  Right GrammarV1ResolvedSpecializedProtocolBoundary
    { resolvedSpecializedProtocolBoundaryRole = roleKey
    , resolvedSpecializedProtocolBoundarySite = site
    , resolvedSpecializedProtocolBoundarySourceReference = sourceReference
    , resolvedSpecializedProtocolBoundaryTargetCandidate =
        GenericStaticReferenceCandidate
          targetName
          GenericBoundaryContractKind
          (SemanticAtom ("boundary." <> targetName <> ".checked"))
    , resolvedSpecializedProtocolBoundaryDeclarationKey =
        DeclarationKey ("decl." <> targetName)
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
qualifiedNameText source =
  Text.intercalate "." (grammarV1QualifiedNameParts source)

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "protocol-boundary-annotations" source
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
