{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Name (..)
  , Outcome (..)
  , Proposition (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolGuardAnnotations
  ( GrammarV1CheckedProtocolGuardAnnotation (..)
  , GrammarV1ClosedProtocolGuardSurface (..)
  , GrammarV1ProtocolGuardError (..)
  , GrammarV1ProtocolGuardSite (..)
  , grammarV1CheckedClosedProtocolGuardSurface
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
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
    , "    | Stop when false => end Done"
    , "  };"
    , "  role Server = offer {"
    , "    Go(y : U8) when true => end Done"
    , "    | Stop when false => end Done"
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
          , Falsehood
          , []
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchGuard "Go"
          , Truth
          , []
          )
        , ( ProtocolRoleKey "Server"
          , GrammarV1OfferBranchGuard "Stop"
          , Falsehood
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
