{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusingError (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Proposition (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProgramSurface
  ( GrammarV1CheckedProgramItem (..)
  , GrammarV1CheckedProgramSurface (..)
  , grammarV1CheckedProgramSurface
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 checked program roots preserve stable identity and ordered semantic items"
        checkedProgramRoot
    , test "SURF-008 program display spelling cannot manufacture stable identity"
        displayRenameNonsemantic
    , test "SURF-008 program assumption focusing failures remain explicit"
        assumptionFocusingFailure
    , test "SURF-008 program root competence remains fail-closed"
        competenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedProgramRoot :: Either String ()
checkedProgramRoot = do
  source <- onlyProgram $ Text.unlines
    [ "program main = instantiate pkg.Arch {"
    , "  entry ingress : U32;"
    , "  assume true within trust.zone;"
    , "  export obligation proof.ready to audit.sink;"
    , "  observable metrics.bytes;"
    , "};"
    ]
  let declarationKey = DeclarationKey "program.stable.lineage"
      definitionRevision = DefinitionRevision "program.definition.v1"
      expected = GrammarV1CheckedProgramSurface
        { checkedProgramDeclarationKey = declarationKey
        , checkedProgramDefinitionRevision = definitionRevision
        , checkedProgramDisplayName = "main"
        , checkedProgramTargetKind = GenericArchitectureDependencyKind
        , checkedProgramTargetReference =
            ReferencedGenericStaticActual "pkg.Arch"
        , checkedProgramItems =
            [ GrammarV1CheckedProgramEntry "ingress" (TyUInt 32) []
            , GrammarV1CheckedProgramAssume Truth "trust.zone" []
            , GrammarV1CheckedProgramExportObligation "proof.ready" "audit.sink"
            , GrammarV1CheckedProgramObservable "metrics.bytes"
            ]
        }
  assert
    ( grammarV1CheckedProgramSurface
        emptyStaticContext declarationKey definitionRevision source
        == Just (Right expected)
    )
    "program root lost stable identity, architecture-category target, or ordered item meaning"

displayRenameNonsemantic :: Either String ()
displayRenameNonsemantic = do
  first <- onlyProgram "program first = instantiate Arch;"
  renamed <- onlyProgram "program renamed = instantiate Arch;"
  let declarationKey = DeclarationKey "program.stable.lineage"
      definitionRevision = DefinitionRevision "program.definition.v1"
      route = grammarV1CheckedProgramSurface
        emptyStaticContext declarationKey definitionRevision
  case (route first, route renamed) of
    (Just (Right left), Just (Right right)) -> do
      assert
        (checkedProgramDeclarationKey left == checkedProgramDeclarationKey right)
        "display rename changed stable program declaration identity"
      assert
        (checkedProgramDefinitionRevision left == checkedProgramDefinitionRevision right)
        "display rename changed stable program definition revision"
      assert
        (checkedProgramTargetReference left == checkedProgramTargetReference right)
        "display rename changed exact unresolved architecture target"
      assert
        (checkedProgramDisplayName left /= checkedProgramDisplayName right)
        "test did not preserve distinct source display names"
    other -> Left ("renamed program roots did not elaborate: " <> show other)

assumptionFocusingFailure :: Either String ()
assumptionFocusingFailure = do
  source <- onlyProgram $ Text.unlines
    [ "program main = instantiate Arch {"
    , "  entry ingress : U32;"
    , "  assume Missing() within trust.zone;"
    , "};"
    ]
  let actual = grammarV1CheckedProgramSurface
        emptyStaticContext
        (DeclarationKey "program.bad.lineage")
        (DefinitionRevision "program.bad.definition")
        source
  assert
    (actual == Just (Left (UnknownClaim "Missing")))
    ("unknown program assumption claim did not remain a focusing rejection: " <> show actual)

competenceBoundaries :: Either String ()
competenceBoundaries = do
  specializedTarget <- onlyProgram
    "program main = instantiate Arch[U32];"
  freeEntry <- onlyProgram $ Text.unlines
    [ "program main = instantiate Arch {"
    , "  entry packet : Bytes[n];"
    , "};"
    ]
  let declarationKey = DeclarationKey "program.boundary.lineage"
      definitionRevision = DefinitionRevision "program.boundary.definition"
      route = grammarV1CheckedProgramSurface
        emptyStaticContext declarationKey definitionRevision
  assert
    (route specializedTarget == Nothing)
    "specialized architecture target bypassed generic static-argument competence"
  assert
    (route freeEntry == Nothing)
    "program entry inherited a nonexistent top-level term binding"

onlyProgram :: Text.Text -> Either String GrammarV1ProgramDecl
onlyProgram source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "program-surface" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProgramDeclaration program -> Right program
      other -> Left ("expected program declaration, got " <> show other)
    declarations -> Left
      ("expected one program declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
