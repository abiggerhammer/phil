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
  ( ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
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
  ( GrammarV1CheckedResolvedProtocolBoundaryAnnotation (..)
  , GrammarV1CheckedSpecializedProtocolBoundaryAnnotation (..)
  , GrammarV1ProtocolBoundaryAnnotation (..)
  , GrammarV1ProtocolBoundaryResolutionError (..)
  , GrammarV1ProtocolBoundarySite (..)
  , GrammarV1ProtocolSpecializedBoundaryError (..)
  , GrammarV1ResolvedProtocolBoundaryReference (..)
  , GrammarV1ResolvedSpecializedProtocolBoundary (..)
  )
import Phil.Surface.GrammarV1.ProtocolBoundaryComposition
  ( GrammarV1CheckedMixedProtocolBoundaryAnnotation (..)
  , GrammarV1ClosedMixedProtocolBoundarySurface (..)
  , GrammarV1MixedProtocolBoundaryError (..)
  , grammarV1CheckedMixedProtocolBoundarySurface
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
    [ test "SURF-008 mixed bare and specialized protocol boundaries compose in exact source order"
        mixedBoundaryFormsCompose
    , test "SURF-008 mixed protocol boundary evidence stays occurrence- and category-exact"
        mixedBoundaryEvidenceIsExact
    , test "SURF-008 mixed protocol boundaries cannot bypass underlying duality"
        mixedBoundaryPreservesDualityFailure
    , test "SURF-008 mixed boundary route does not replace homogeneous sibling routes"
        homogeneousProtocolsStayOutsideMixedRoute
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data BoundaryFlavor = BareBoundary | SpecializedBoundary
  deriving (Eq, Show)

mixedBoundaryFormsCompose :: Either String ()
mixedBoundaryFormsCompose = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Mixed {"
    , "  role Client = send (first : U8) using wire.Send then select {"
    , "    Go(next : U8) using wire.Go[U8] => end Done"
    , "    | Stop using wire.Stop => end Done"
    , "  };"
    , "  role Server = receive (first_in : U8) using wire.Receive[U8] then offer {"
    , "    Go(next_in : U8) using wire.GoIn => end Done"
    , "    | Stop using wire.StopIn[U8] => end Done"
    , "  };"
    , "}"
    ]
  surface <- expectRightMixedSurface protocol
  let endDone = ProtocolTemplateEnd (Outcome "Done")
      expectedTemplates =
        ( ( ProtocolRoleKey "Client"
          , ProtocolTemplateSend
              (Name "first")
              (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateSelect
                [ ProtocolBranchTemplate
                    { protocolTemplateBranchLabel = "Go"
                    , protocolTemplateBranchPayload =
                        Just (Name "next", ProtocolConcreteType (TyUInt 8))
                    , protocolTemplateBranchContinuation = endDone
                    }
                , ProtocolBranchTemplate
                    { protocolTemplateBranchLabel = "Stop"
                    , protocolTemplateBranchPayload = Nothing
                    , protocolTemplateBranchContinuation = endDone
                    }
                ])
          )
        , ( ProtocolRoleKey "Server"
          , ProtocolTemplateReceive
              (Name "first_in")
              (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateOffer
                [ ProtocolBranchTemplate
                    { protocolTemplateBranchLabel = "Go"
                    , protocolTemplateBranchPayload =
                        Just (Name "next_in", ProtocolConcreteType (TyUInt 8))
                    , protocolTemplateBranchContinuation = endDone
                    }
                , ProtocolBranchTemplate
                    { protocolTemplateBranchLabel = "Stop"
                    , protocolTemplateBranchPayload = Nothing
                    , protocolTemplateBranchContinuation = endDone
                    }
                ])
          )
        )
      expectedAnnotations =
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
        , ( ProtocolRoleKey "Client"
          , GrammarV1SelectBranchBoundary "Stop"
          , BareBoundary
          , SemanticAtom "boundary.wire.Stop.resolved"
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
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchBoundary "Stop"
          , SpecializedBoundary
          , SemanticAtom "boundary.wire.StopIn.checked"
          )
        ]
  assert
    (checkedMixedProtocolBoundaryRoleTemplates surface == expectedTemplates)
    "mixed boundary partitioning changed the checked underlying role templates"
  assert
    (mixedAnnotationSummary surface == expectedAnnotations)
    "mixed boundary annotations lost category, role/site identity, or source preorder"

mixedBoundaryEvidenceIsExact :: Either String ()
mixedBoundaryEvidenceIsExact = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Evidence {"
    , "  role Client = send (x : U8) using Wire then end Done;"
    , "  role Server = receive (y : U8) using Wire[U8] then end Done;"
    , "}"
    ]
  (bareEvidence, specializedEvidence) <- mixedBoundaryEvidence protocol
  assert
    ( grammarV1CheckedMixedProtocolBoundarySurface
        [] specializedEvidence protocol
        == Just
          (Left
            (GrammarV1MixedProtocolBoundaryBareError
              (GrammarV1ResolvedProtocolBoundaryEvidenceCountMismatch 1 0)))
    )
    "missing bare evidence in a mixed protocol did not remain a bare-resolver error"
  case specializedEvidence of
    [specialized] -> do
      let detached = specialized
            { resolvedSpecializedProtocolBoundaryRole = ProtocolRoleKey "Client" }
      assert
        ( grammarV1CheckedMixedProtocolBoundarySurface
            bareEvidence [detached] protocol
            == Just
              (Left
                (GrammarV1MixedProtocolBoundarySpecializedError
                  (GrammarV1SpecializedProtocolBoundaryRoleMismatch
                    0
                    (ProtocolRoleKey "Server")
                    (ProtocolRoleKey "Client"))))
        )
        "specialized evidence drifted across the mixed source occurrence"
    other -> Left
      ("expected one specialized evidence entry, got " <> show (length other))

mixedBoundaryPreservesDualityFailure :: Either String ()
mixedBoundaryPreservesDualityFailure = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol NonDual {"
    , "  role Client = send (x : U8) using Wire then end Left;"
    , "  role Server = receive (y : U8) using Wire[U8] then end Right;"
    , "}"
    ]
  (bareEvidence, specializedEvidence) <- mixedBoundaryEvidence protocol
  assert
    ( grammarV1CheckedMixedProtocolBoundarySurface
        bareEvidence specializedEvidence protocol
        == Just
          (Left
            (GrammarV1MixedProtocolBoundaryBareError
              (GrammarV1ResolvedProtocolBoundaryRoleError
                (NonDualProtocolRoles
                  (ProtocolRoleKey "Client")
                  (ProtocolRoleKey "Server")))))
    )
    "mixed annotation routing made a non-dual protocol acceptable"

homogeneousProtocolsStayOutsideMixedRoute :: Either String ()
homogeneousProtocolsStayOutsideMixedRoute = do
  bare <- onlyProtocol $ Text.unlines
    [ "protocol Bare {"
    , "  role Client = send (x : U8) using Wire then end Done;"
    , "  role Server = receive (y : U8) using Wire then end Done;"
    , "}"
    ]
  specialized <- onlyProtocol $ Text.unlines
    [ "protocol Specialized {"
    , "  role Client = send (x : U8) using Wire[U8] then end Done;"
    , "  role Server = receive (y : U8) using Wire[U8] then end Done;"
    , "}"
    ]
  (bareEvidence, _) <- mixedBoundaryEvidence bare
  (_, specializedEvidence) <- mixedBoundaryEvidence specialized
  assert
    (grammarV1CheckedMixedProtocolBoundarySurface bareEvidence [] bare == Nothing)
    "homogeneous bare protocol was silently rerouted through mixed composition"
  assert
    ( grammarV1CheckedMixedProtocolBoundarySurface
        [] specializedEvidence specialized
        == Nothing
    )
    "homogeneous specialized protocol was silently rerouted through mixed composition"

mixedAnnotationSummary
  :: GrammarV1ClosedMixedProtocolBoundarySurface
  -> [ ( ProtocolRoleKey
       , GrammarV1ProtocolBoundarySite
       , BoundaryFlavor
       , SemanticForm
       )
     ]
mixedAnnotationSummary surface = map summarize
  (checkedMixedProtocolBoundaryAnnotations surface)
  where
    summarize checked = case checked of
      GrammarV1CheckedMixedBareProtocolBoundary annotation ->
        ( checkedResolvedProtocolBoundaryRole annotation
        , checkedResolvedProtocolBoundarySite annotation
        , BareBoundary
        , checkedResolvedProtocolBoundarySemanticForm annotation
        )
      GrammarV1CheckedMixedSpecializedProtocolBoundary annotation ->
        ( checkedSpecializedProtocolBoundaryRole annotation
        , checkedSpecializedProtocolBoundarySite annotation
        , SpecializedBoundary
        , checkedSpecializedProtocolBoundaryTargetSemanticForm annotation
        )

expectRightMixedSurface
  :: GrammarV1ProtocolDecl
  -> Either String GrammarV1ClosedMixedProtocolBoundarySurface
expectRightMixedSurface protocol = do
  (bareEvidence, specializedEvidence) <- mixedBoundaryEvidence protocol
  case grammarV1CheckedMixedProtocolBoundarySurface
      bareEvidence specializedEvidence protocol of
    Just (Right surface) -> Right surface
    other -> Left ("expected checked mixed boundary surface, got " <> show other)

mixedBoundaryEvidence
  :: GrammarV1ProtocolDecl
  -> Either String
      ( [GrammarV1ResolvedProtocolBoundaryReference]
      , [GrammarV1ResolvedSpecializedProtocolBoundary]
      )
mixedBoundaryEvidence protocol = do
  occurrences <- boundaryOccurrences protocol
  bare <- mapM bareBoundaryEvidence
    [ occurrence
    | occurrence@(_, _, Located _ reference) <- occurrences
    , null (grammarV1StaticReferenceArguments reference)
    ]
  specialized <- mapM specializedBoundaryEvidence
    [ occurrence
    | occurrence@(_, _, Located _ reference) <- occurrences
    , not (null (grammarV1StaticReferenceArguments reference))
    ]
  pure (bare, specialized)

bareBoundaryEvidence
  :: ( ProtocolRoleKey
     , GrammarV1ProtocolBoundarySite
     , Located GrammarV1StaticReference
     )
  -> Either String GrammarV1ResolvedProtocolBoundaryReference
bareBoundaryEvidence (roleKey, site, sourceReference@(Located _ reference)) = do
  let targetName = qualifiedNameText (grammarV1StaticReferenceName reference)
      annotation = GrammarV1ProtocolBoundaryAnnotation
        { protocolBoundaryRole = roleKey
        , protocolBoundarySite = site
        , protocolBoundarySourceReference = sourceReference
        , protocolBoundaryStaticReference = ReferencedGenericStaticActual targetName
        }
  Right GrammarV1ResolvedProtocolBoundaryReference
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
  :: ( ProtocolRoleKey
     , GrammarV1ProtocolBoundarySite
     , Located GrammarV1StaticReference
     )
  -> Either String GrammarV1ResolvedSpecializedProtocolBoundary
specializedBoundaryEvidence (roleKey, site, sourceReference@(Located _ reference)) = do
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
occurrence roleKey site (Just sourceReference) = [(roleKey, site, sourceReference)]

qualifiedNameText :: GrammarV1QualifiedName -> Text.Text
qualifiedNameText source =
  Text.intercalate "." (grammarV1QualifiedNameParts source)

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "protocol-boundary-composition" source
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
