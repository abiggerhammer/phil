{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.GrammarV1WholeSource
  ( GrammarV1WholeSourceVerificationSpec (..)
  , GrammarV1WholeSourceVerificationError (..)
  , grammarV1ClosedArchitectureInterfaceRevision
  , grammarV1WholeSourceVerificationBundle
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( Digest (..)
  , digestText
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InterfaceRevision (..)
  , deriveArchitectureInstanceIdentity
  , emptyStaticContext
  )
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureSurface (..)
  , grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ArchitectureDecl
  , GrammarV1Declaration (..)
  , GrammarV1ParseDiagnostic
  , GrammarV1ProgramDecl
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.ProgramSurface
  ( GrammarV1CheckedProgramSurface (..)
  , grammarV1CheckedProgramSurface
  )
import Phil.Surface.Lineage
  ( GrammarRevision (..)
  , canonicalGrammarRevisionV1
  )
import Phil.Surface.Syntax (Located (..))
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision
  , buildVerificationRevisionGraph
  )
import Phil.Verification.Bundle
  ( VerificationBundle
  , buildVerificationBundle
  )

data GrammarV1WholeSourceVerificationSpec =
  GrammarV1WholeSourceVerificationSpec
    { wholeSourcePrimaryLabel :: Text
    , wholeSourcePrimaryText :: Text
    , wholeSourceSupplementalUnits :: [(Text, Text)]
    , wholeSourceArchitectureKey :: DeclarationKey
    , wholeSourceArchitectureRevision :: DefinitionRevision
    , wholeSourceProgramKey :: DeclarationKey
    , wholeSourceProgramRevision :: DefinitionRevision
    , wholeSourcePolicyRevision :: AssurancePolicyRevision
    }
  deriving (Eq, Show)

data GrammarV1WholeSourceVerificationError
  = WholeSourcePrimaryParseError GrammarV1ParseDiagnostic
  | WholeSourceSupplementalParseError Text GrammarV1ParseDiagnostic
  | WholeSourceSupplementalEmpty Text
  | WholeSourceArchitectureCountMismatch Int
  | WholeSourceProgramCountMismatch Int
  | WholeSourceArchitectureNotCompetent
  | WholeSourceArchitectureRejected Text
  | WholeSourceProgramNotCompetent
  | WholeSourceProgramRejected Text
  | WholeSourceProgramTargetKindMismatch GenericStaticKind
  | WholeSourceProgramTargetMismatch Text Text
  | WholeSourceVerificationGraphError Text
  | WholeSourceVerificationBundleError Text
  deriving (Eq, Show)

-- | Closed, non-generic Grammar-v1 architectures have no public static
-- parameter/requirement interface in the currently competent whole-source
-- fragment. Their exact body revision remains caller-supplied stable identity.
grammarV1ClosedArchitectureInterfaceRevision :: InterfaceRevision
grammarV1ClosedArchitectureInterfaceRevision =
  InterfaceRevision "phil.grammar-v1.architecture.closed.v1"

grammarV1WholeSourceVerificationBundle
  :: GrammarV1WholeSourceVerificationSpec
  -> Either GrammarV1WholeSourceVerificationError VerificationBundle
grammarV1WholeSourceVerificationBundle spec = do
  sourceFile <- mapLeft WholeSourcePrimaryParseError $
    parseGrammarV1StructuralSource
      (wholeSourcePrimaryLabel spec)
      (wholeSourcePrimaryText spec)
  mapM_ checkSupplemental (wholeSourceSupplementalUnits spec)
  architectureDecl <- exactlyOneArchitecture sourceFile
  programDecl <- exactlyOneProgram sourceFile
  architecture <- checkedArchitecture architectureDecl
  program <- checkedProgram programDecl
  validateProgramTarget architecture program
  graph <- mapLeft (WholeSourceVerificationGraphError . showText) $
    buildVerificationRevisionGraph [] Set.empty
  let declarationIdentity = DeclarationIdentity
        { identityDeclarationKey = wholeSourceArchitectureKey spec
        , identityInterfaceRevision = grammarV1ClosedArchitectureInterfaceRevision
        , identityDefinitionRevision = wholeSourceArchitectureRevision spec
        }
      instanceIdentity = deriveArchitectureInstanceIdentity
        ArchitectureInstanceDescriptor
          { architectureInstanceKey = programInstanceKey spec
          , architectureParentInstanceKey = Nothing
          , architectureDeclarationIdentity = declarationIdentity
          , architectureStaticBindings = Map.empty
          }
      policy = ApplicationAssurancePolicy
        { applicationAssurancePolicyRevision = wholeSourcePolicyRevision spec
        , applicationAssurancePolicyPermittedDispositions = Set.empty
        }
  mapLeft (WholeSourceVerificationBundleError . showText) $
    buildVerificationBundle
      (wholeSourceRevision spec)
      [declarationIdentity]
      [instanceIdentity]
      []
      graph
      policy
      []
  where
    checkSupplemental (label, source)
      | Text.null source = Left (WholeSourceSupplementalEmpty label)
      | otherwise =
          mapLeft (WholeSourceSupplementalParseError label) $
            parseGrammarV1StructuralSource label source

    checkedArchitecture source =
      case grammarV1CheckedArchitectureSurface
          emptyStaticContext
          (wholeSourceArchitectureKey spec)
          (wholeSourceArchitectureRevision spec)
          source of
        Nothing -> Left WholeSourceArchitectureNotCompetent
        Just (Left errorValue) ->
          Left (WholeSourceArchitectureRejected (showText errorValue))
        Just (Right value) -> Right value

    checkedProgram source =
      case grammarV1CheckedProgramSurface
          emptyStaticContext
          (wholeSourceProgramKey spec)
          (wholeSourceProgramRevision spec)
          source of
        Nothing -> Left WholeSourceProgramNotCompetent
        Just (Left errorValue) ->
          Left (WholeSourceProgramRejected (showText errorValue))
        Just (Right value) -> Right value

exactlyOneArchitecture
  :: GrammarV1SourceFile
  -> Either GrammarV1WholeSourceVerificationError GrammarV1ArchitectureDecl
exactlyOneArchitecture source =
  case
    [ architecture
    | Located _ top <- grammarV1TopLevelDecls source
    , GrammarV1ArchitectureDeclaration architecture <-
        [locatedValue (grammarV1Declaration top)]
    ] of
    [architecture] -> Right architecture
    architectures ->
      Left (WholeSourceArchitectureCountMismatch (length architectures))

exactlyOneProgram
  :: GrammarV1SourceFile
  -> Either GrammarV1WholeSourceVerificationError GrammarV1ProgramDecl
exactlyOneProgram source =
  case
    [ program
    | Located _ top <- grammarV1TopLevelDecls source
    , GrammarV1ProgramDeclaration program <-
        [locatedValue (grammarV1Declaration top)]
    ] of
    [program] -> Right program
    programs -> Left (WholeSourceProgramCountMismatch (length programs))

validateProgramTarget
  :: GrammarV1CheckedArchitectureSurface
  -> GrammarV1CheckedProgramSurface
  -> Either GrammarV1WholeSourceVerificationError ()
validateProgramTarget architecture program = do
  if checkedProgramTargetKind program == GenericArchitectureDependencyKind
    then Right ()
    else Left
      (WholeSourceProgramTargetKindMismatch
        (checkedProgramTargetKind program))
  case checkedProgramTargetReference program of
    ReferencedGenericStaticActual target
      | target == checkedArchitectureDisplayName architecture -> Right ()
      | otherwise -> Left
          (WholeSourceProgramTargetMismatch
            (checkedArchitectureDisplayName architecture)
            target)
    DirectGenericStaticActual actualKind _ ->
      Left (WholeSourceProgramTargetKindMismatch actualKind)

wholeSourceRevision :: GrammarV1WholeSourceVerificationSpec -> Digest
wholeSourceRevision spec = digestText (Text.intercalate "\n"
  ( [ "phil.grammar-v1.whole-source.verification.v1"
    , "grammar=" <> unGrammarRevision canonicalGrammarRevisionV1
    , "primary.label=" <> wholeSourcePrimaryLabel spec
    , "primary.sha256=" <> digestValue (digestText (wholeSourcePrimaryText spec))
    ]
    <> [ "supplemental." <> label <> ".sha256=" <> digestValue (digestText source)
       | (label, source) <- wholeSourceSupplementalUnits spec
       ]
    <> [ "architecture.key=" <> unDeclarationKey
          (wholeSourceArchitectureKey spec)
       , "architecture.definition=" <> unDefinitionRevision
          (wholeSourceArchitectureRevision spec)
       , "program.key=" <> unDeclarationKey (wholeSourceProgramKey spec)
       , "program.definition=" <> unDefinitionRevision
          (wholeSourceProgramRevision spec)
       ]
  ))
  where
    digestValue (Digest value) = value

programInstanceKey :: GrammarV1WholeSourceVerificationSpec -> InstanceKey
programInstanceKey spec =
  InstanceKey
    ("phil.grammar-v1.program-instance.v1:"
      <> unDeclarationKey (wholeSourceProgramKey spec))

showText :: Show a => a -> Text
showText = Text.pack . show

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
