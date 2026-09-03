{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
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
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedProtocolRoleTemplates
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed protocol roles preserve exact Core template order and payloads"
        closedRolesPreserved
    , test "SURF-008 protocol role projection does not invent duality"
        nonDualRolesPreserved
    , test "SURF-008 protocol role templates preserve session competence boundaries"
        competenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closedRolesPreserved :: Either String ()
closedRolesPreserved = do
  protocol <- onlyProtocol closedProtocolSource
  let expected =
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
    (grammarV1ClosedProtocolRoleTemplates protocol == Just expected)
    "closed binary protocol did not preserve role order and exact session templates"

nonDualRolesPreserved :: Either String ()
nonDualRolesPreserved = do
  protocol <- onlyProtocol nonDualProtocolSource
  let expected =
        ( (ProtocolRoleKey "First", ProtocolTemplateEnd (Outcome "Left"))
        , (ProtocolRoleKey "Second", ProtocolTemplateEnd (Outcome "Right"))
        )
  assert
    (grammarV1ClosedProtocolRoleTemplates protocol == Just expected)
    "role-template projection incorrectly asserted or repaired protocol duality"

competenceBoundaries :: Either String ()
competenceBoundaries = do
  codec <- onlyProtocol codecProtocolSource
  generic <- onlyProtocol genericProtocolSource
  requirement <- onlyProtocol requirementProtocolSource
  mapM_ expectNothing
    [ ("codec-bearing role", codec)
    , ("generic protocol", generic)
    , ("requirement-bearing protocol", requirement)
    ]
  where
    expectNothing (label, protocol) =
      assert
        (grammarV1ClosedProtocolRoleTemplates protocol == Nothing)
        (label <> " escaped the closed protocol-role competence boundary")

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "protocol-role-templates" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

closedProtocolSource :: Text.Text
closedProtocolSource = Text.unlines
  [ "protocol P {"
  , "  role Client = send (outgoing : U8) then end Done;"
  , "  role Server = receive (incoming : U8) then end Done;"
  , "}"
  ]

nonDualProtocolSource :: Text.Text
nonDualProtocolSource = Text.unlines
  [ "protocol P {"
  , "  role First = end Left;"
  , "  role Second = end Right;"
  , "}"
  ]

codecProtocolSource :: Text.Text
codecProtocolSource = Text.unlines
  [ "protocol P {"
  , "  role A = send (x : U8) using Wire then end Done;"
  , "  role B = end Done;"
  , "}"
  ]

genericProtocolSource :: Text.Text
genericProtocolSource = Text.unlines
  [ "protocol P[S : Session] {"
  , "  role A = end Done;"
  , "  role B = end Done;"
  , "}"
  ]

requirementProtocolSource :: Text.Text
requirementProtocolSource = Text.unlines
  [ "protocol P requires { proposition true; } {"
  , "  role A = end Done;"
  , "  role B = end Done;"
  , "}"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
