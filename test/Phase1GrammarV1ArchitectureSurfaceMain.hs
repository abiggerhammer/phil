{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureItem (..)
  , GrammarV1CheckedArchitectureRoleTarget (..)
  , GrammarV1CheckedArchitectureSurface (..)
  , grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed architecture surfaces preserve checked item order and non-authoritative identities"
        checkedArchitectureSemantics
    , test "SURF-008 architecture proposition failures remain explicit focusing rejection"
        focusingFailurePreserved
    , test "SURF-008 architecture surfaces remain fail-closed outside bounded competence"
        competenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedArchitectureSemantics :: Either String ()
checkedArchitectureSemantics = do
  architecture <- onlyArchitecture $ Text.unlines
    [ "architecture A {"
    , "  instance worker = Worker;"
    , "  ref shared = cluster.worker;"
    , "  process proc = worker;"
    , "  protocol wire = Ping;"
    , "  role wire.Client = proc;"
    , "  role wire.Server = external;"
    , "  bind proc.out = proc.input;"
    , "  boundary proc.edge = codec.inbound;"
    , "  observable proc.metrics;"
    , "  assume true within trust.zone;"
    , "  constraint true;"
    , "  entry ingress : U32;"
    , "  authority token : Proof[true] originates at root.node;"
    , "  grant trust.token = true;"
    , "  export obligation proof.ready to audit.sink;"
    , "}"
    ]
  let declarationKey = DeclarationKey "architecture.stable.lineage"
      definitionRevision = DefinitionRevision "architecture.definition.v1"
  case grammarV1CheckedArchitectureSurface
      emptyStaticContext declarationKey definitionRevision architecture of
    Just (Right checked) -> do
      assert (checkedArchitectureDeclarationKey checked == declarationKey)
        "stable architecture declaration identity was not preserved"
      assert (checkedArchitectureDefinitionRevision checked == definitionRevision)
        "architecture definition revision was not preserved"
      assert (checkedArchitectureDisplayName checked == "A")
        "architecture display name changed"
      case checkedArchitectureItems checked of
        [ GrammarV1CheckedArchitectureInstance "worker" (ReferencedGenericStaticActual "Worker")
          , GrammarV1CheckedArchitectureRef "shared" "cluster.worker"
          , GrammarV1CheckedArchitectureProcess "proc" "worker"
          , GrammarV1CheckedArchitectureProtocol "wire" (ReferencedGenericStaticActual "Ping")
          , GrammarV1CheckedArchitectureRole "wire.Client"
              (GrammarV1CheckedInternalRoleTarget "proc")
          , GrammarV1CheckedArchitectureRole "wire.Server"
              GrammarV1CheckedExternalRoleTarget
          , GrammarV1CheckedArchitectureBind "proc.out" "proc.input"
          , GrammarV1CheckedArchitectureBoundary "proc.edge" "codec.inbound"
          , GrammarV1CheckedArchitectureObservable "proc.metrics"
          , GrammarV1CheckedArchitectureAssume Truth "trust.zone" []
          , GrammarV1CheckedArchitectureConstraint Truth []
          , GrammarV1CheckedArchitectureEntry "ingress" (TyUInt 32) []
          , GrammarV1CheckedArchitectureAuthority "token" (TyProof Truth) "root.node" []
          , GrammarV1CheckedArchitectureGrant "trust.token" (RefBool True)
          , GrammarV1CheckedArchitectureExportObligation "proof.ready" "audit.sink"
          ] -> Right ()
        other -> Left ("unexpected checked architecture items: " <> show other)
    other -> Left ("closed architecture surface did not elaborate: " <> show other)

focusingFailurePreserved :: Either String ()
focusingFailurePreserved = do
  architecture <- onlyArchitecture
    "architecture A { constraint Missing(); }"
  let actual = grammarV1CheckedArchitectureSurface
        emptyStaticContext
        (DeclarationKey "architecture.bad.lineage")
        (DefinitionRevision "architecture.bad.definition")
        architecture
  assert
    (actual == Just (Left (UnknownClaim "Missing")))
    ("unknown architecture claim was not preserved as focusing rejection: " <> show actual)

competenceBoundaries :: Either String ()
competenceBoundaries = do
  generic <- onlyArchitecture
    "architecture A[T : Type] {}"
  constrained <- onlyArchitecture
    "architecture A requires { proposition true; } {}"
  specializedInstance <- onlyArchitecture
    "architecture A { instance worker = Worker[U32]; }"
  specializedProtocol <- onlyArchitecture
    "architecture A { protocol wire = Ping[U32]; }"
  freeGrant <- onlyArchitecture
    "architecture A { grant trust.token = missing; }"
  let declarationKey = DeclarationKey "architecture.boundary.lineage"
      definitionRevision = DefinitionRevision "architecture.boundary.definition"
      check source = grammarV1CheckedArchitectureSurface
        emptyStaticContext declarationKey definitionRevision source
  mapM_ (\(label, source) ->
    assert (check source == Nothing)
      (label <> " escaped the bounded architecture-surface competence boundary"))
    [ ("generic architecture", generic)
    , ("requirement-bearing architecture", constrained)
    , ("specialized instance target", specializedInstance)
    , ("specialized protocol target", specializedProtocol)
    , ("free architecture grant value", freeGrant)
    ]

onlyArchitecture :: Text.Text -> Either String GrammarV1ArchitectureDecl
onlyArchitecture source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "architecture-surface" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ArchitectureDeclaration architecture -> Right architecture
      other -> Left ("expected architecture declaration, got " <> show other)
    declarations -> Left
      ("expected one architecture declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
