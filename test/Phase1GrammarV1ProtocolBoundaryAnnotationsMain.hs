{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolBoundaryAnnotations
  ( GrammarV1ClosedProtocolBoundarySurface (..)
  , GrammarV1ProtocolBoundaryAnnotation (..)
  , GrammarV1ProtocolBoundarySite (..)
  , grammarV1CheckedClosedProtocolBoundarySurface
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
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

expectRightSurface
  :: GrammarV1ProtocolDecl
  -> Either String GrammarV1ClosedProtocolBoundarySurface
expectRightSurface protocol =
  case grammarV1CheckedClosedProtocolBoundarySurface protocol of
    Just (Right surface) -> Right surface
    other -> Left ("expected checked boundary surface, got " <> show other)

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
