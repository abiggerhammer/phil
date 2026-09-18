{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1CheckedArchitecture
  ( HandoffCheckedDeclaration (..)
  , Phase1CheckedArchitectureSummary (..)
  , Phase1CheckedArchitectureSummaryError (..)
  , phase1CheckedArchitectureFormatV1
  , derivePhase1CheckedArchitectureSummary
  , renderPhase1CheckedArchitectureSummary
  , decodePhase1CheckedArchitectureSummary
  ) where

import Data.Char (isDigit)
import Data.List (sortOn)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest (..), digestText)
import Phil.Compiler.SourceArchitecture
  ( CheckedSourceArchitecture (..)
  , sourceComponentDefinitionSemantics
  , sourceComponentInterfaceSemantics
  )
import Phil.Compiler.SourceBundle
  ( CheckedSourceBundle (..)
  , CheckedSourceUnit (..)
  )
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , CheckedArchitectureInstance (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , InterfaceRevision (..)
  , canonicalSemanticForm
  , deriveDeclarationIdentity
  )
import Phil.Surface.Syntax (Located (..))

data HandoffCheckedDeclaration = HandoffCheckedDeclaration
  { handoffCheckedDeclarationKey :: DeclarationKey
  , handoffCheckedInterfaceSemanticsSha256 :: Text
  , handoffCheckedDefinitionSemanticsSha256 :: Text
  , handoffCheckedInterfaceRevisionSha256 :: Text
  , handoffCheckedDefinitionRevisionSha256 :: Text
  }
  deriving (Eq, Ord, Show)

data Phase1CheckedArchitectureSummary = Phase1CheckedArchitectureSummary
  { handoffCheckedSelectedRoot :: Text
  , handoffCheckedSelectedDeclaration :: DeclarationKey
  , handoffCheckedDeclarations :: [HandoffCheckedDeclaration]
  , handoffCheckedInstanceKey :: InstanceKey
  , handoffCheckedInstanceRevisionSha256 :: Text
  }
  deriving (Eq, Show)

data Phase1CheckedArchitectureSummaryError
  = CheckedArchitectureSummaryEmpty
  | CheckedArchitectureSummaryHeaderMismatch Text
  | CheckedArchitectureSummaryMalformedRecord Int Text
  | CheckedArchitectureSummaryMalformedDigest Int Text
  | CheckedArchitectureSummaryDuplicateRoot
  | CheckedArchitectureSummaryDuplicateInstance
  | CheckedArchitectureSummaryDuplicateDeclaration DeclarationKey
  | CheckedArchitectureSummaryMissingRoot
  | CheckedArchitectureSummaryMissingInstance
  | CheckedArchitectureSummaryRootDeclarationMissing DeclarationKey
  deriving (Eq, Show)

phase1CheckedArchitectureFormatV1 :: Text
phase1CheckedArchitectureFormatV1 = "PHIL-PHASE1-CHECKED-ARCHITECTURE-V1"

derivePhase1CheckedArchitectureSummary
  :: CheckedSourceArchitecture
  -> Phase1CheckedArchitectureSummary
derivePhase1CheckedArchitectureSummary architecture =
  Phase1CheckedArchitectureSummary
    { handoffCheckedSelectedRoot = checkedSourceSelectedRoot bundle
    , handoffCheckedSelectedDeclaration = checkedSourceSelectedRootKey bundle
    , handoffCheckedDeclarations =
        sortOn handoffCheckedDeclarationKey
          (map declarationSummary (checkedSourceUnits bundle))
    , handoffCheckedInstanceKey = identityInstanceKey instanceIdentity
    , handoffCheckedInstanceRevisionSha256 =
        sha256Text (unInstanceRevision (identityInstanceRevision instanceIdentity))
    }
  where
    bundle = checkedSourceArchitectureBundle architecture
    instanceIdentity =
      checkedArchitectureIdentity (checkedSourceArchitectureRoot architecture)

declarationSummary :: CheckedSourceUnit -> HandoffCheckedDeclaration
declarationSummary unit =
  HandoffCheckedDeclaration
    { handoffCheckedDeclarationKey = identityDeclarationKey identity
    , handoffCheckedInterfaceSemanticsSha256 =
        sha256Text (canonicalSemanticForm interfaceSemantics)
    , handoffCheckedDefinitionSemanticsSha256 =
        sha256Text (canonicalSemanticForm definitionSemantics)
    , handoffCheckedInterfaceRevisionSha256 =
        sha256Text (unInterfaceRevision (identityInterfaceRevision identity))
    , handoffCheckedDefinitionRevisionSha256 =
        sha256Text (unDefinitionRevision (identityDefinitionRevision identity))
    }
  where
    component = locatedValue (checkedSourceComponent unit)
    interfaceSemantics = sourceComponentInterfaceSemantics component
    definitionSemantics = sourceComponentDefinitionSemantics component
    identity = deriveDeclarationIdentity DeclarationDescriptor
      { declarationPresentation = DeclarationPresentation "handoff" []
      , declarationKey = checkedSourceDeclarationKey unit
      , declarationInterfaceSemantics = interfaceSemantics
      , declarationDefinitionSemantics = definitionSemantics
      }

sha256Text :: Text -> Text
sha256Text = ("sha256:" <>) . unDigest . digestText

renderPhase1CheckedArchitectureSummary
  :: Phase1CheckedArchitectureSummary
  -> Text
renderPhase1CheckedArchitectureSummary summary = Text.unlines
  ( [ phase1CheckedArchitectureFormatV1
    , Text.intercalate "\t"
        [ "root"
        , handoffCheckedSelectedRoot summary
        , unDeclarationKey (handoffCheckedSelectedDeclaration summary)
        ]
    ]
    <> map renderDeclaration
        (sortOn handoffCheckedDeclarationKey (handoffCheckedDeclarations summary))
    <> [ Text.intercalate "\t"
          [ "instance"
          , unInstanceKey (handoffCheckedInstanceKey summary)
          , handoffCheckedInstanceRevisionSha256 summary
          ]
       ]
  )
  where
    renderDeclaration declaration = Text.intercalate "\t"
      [ "declaration"
      , unDeclarationKey (handoffCheckedDeclarationKey declaration)
      , handoffCheckedInterfaceSemanticsSha256 declaration
      , handoffCheckedDefinitionSemanticsSha256 declaration
      , handoffCheckedInterfaceRevisionSha256 declaration
      , handoffCheckedDefinitionRevisionSha256 declaration
      ]

data DecodeState = DecodeState
  { decodeRoot :: Maybe (Text, DeclarationKey)
  , decodeDeclarations :: [HandoffCheckedDeclaration]
  , decodeInstance :: Maybe (InstanceKey, Text)
  }

emptyDecodeState :: DecodeState
emptyDecodeState = DecodeState Nothing [] Nothing

decodePhase1CheckedArchitectureSummary
  :: Text
  -> Either Phase1CheckedArchitectureSummaryError Phase1CheckedArchitectureSummary
decodePhase1CheckedArchitectureSummary input =
  case Text.lines input of
    [] -> Left CheckedArchitectureSummaryEmpty
    header : rows
      | Text.strip header /= phase1CheckedArchitectureFormatV1 ->
          Left (CheckedArchitectureSummaryHeaderMismatch (Text.strip header))
      | otherwise -> do
          state <- foldl step (Right emptyDecodeState) (zip [2 ..] rows)
          (rootName, rootDeclaration) <- maybe
            (Left CheckedArchitectureSummaryMissingRoot)
            Right
            (decodeRoot state)
          (instanceKey, instanceRevisionDigest) <- maybe
            (Left CheckedArchitectureSummaryMissingInstance)
            Right
            (decodeInstance state)
          let declarations = sortOn handoffCheckedDeclarationKey
                (decodeDeclarations state)
              declarationKeys = Set.fromList
                (map handoffCheckedDeclarationKey declarations)
          if Set.member rootDeclaration declarationKeys
            then Right ()
            else Left
              (CheckedArchitectureSummaryRootDeclarationMissing rootDeclaration)
          Right Phase1CheckedArchitectureSummary
            { handoffCheckedSelectedRoot = rootName
            , handoffCheckedSelectedDeclaration = rootDeclaration
            , handoffCheckedDeclarations = declarations
            , handoffCheckedInstanceKey = instanceKey
            , handoffCheckedInstanceRevisionSha256 = instanceRevisionDigest
            }
  where
    step accumulated row = accumulated >>= \state -> decodeRow state row

decodeRow
  :: DecodeState
  -> (Int, Text)
  -> Either Phase1CheckedArchitectureSummaryError DecodeState
decodeRow state (lineNumber, rawLine)
  | Text.null stripped = Right state
  | "#" `Text.isPrefixOf` stripped = Right state
  | otherwise =
      case Text.splitOn "\t" rawLine of
        ["root", rawRoot, rawDeclaration]
          | allNonempty [rawRoot, rawDeclaration] ->
              case decodeRoot state of
                Nothing -> Right state
                  { decodeRoot = Just
                      (Text.strip rawRoot, DeclarationKey (Text.strip rawDeclaration))
                  }
                Just _ -> Left CheckedArchitectureSummaryDuplicateRoot
          | otherwise -> malformed
        [ "declaration"
          , rawKey
          , interfaceSemanticsDigest
          , definitionSemanticsDigest
          , interfaceRevisionDigest
          , definitionRevisionDigest
          ]
          | not (Text.null (Text.strip rawKey)) -> do
              mapM_ (validateDigest lineNumber)
                [ interfaceSemanticsDigest
                , definitionSemanticsDigest
                , interfaceRevisionDigest
                , definitionRevisionDigest
                ]
              let declaration = HandoffCheckedDeclaration
                    { handoffCheckedDeclarationKey = DeclarationKey (Text.strip rawKey)
                    , handoffCheckedInterfaceSemanticsSha256 = interfaceSemanticsDigest
                    , handoffCheckedDefinitionSemanticsSha256 = definitionSemanticsDigest
                    , handoffCheckedInterfaceRevisionSha256 = interfaceRevisionDigest
                    , handoffCheckedDefinitionRevisionSha256 = definitionRevisionDigest
                    }
              if any
                  ((== handoffCheckedDeclarationKey declaration)
                    . handoffCheckedDeclarationKey)
                  (decodeDeclarations state)
                then Left
                  (CheckedArchitectureSummaryDuplicateDeclaration
                    (handoffCheckedDeclarationKey declaration))
                else Right state
                  { decodeDeclarations = declaration : decodeDeclarations state }
          | otherwise -> malformed
        ["instance", rawKey, revisionDigest]
          | not (Text.null (Text.strip rawKey)) -> do
              validateDigest lineNumber revisionDigest
              case decodeInstance state of
                Nothing -> Right state
                  { decodeInstance =
                      Just (InstanceKey (Text.strip rawKey), revisionDigest)
                  }
                Just _ -> Left CheckedArchitectureSummaryDuplicateInstance
          | otherwise -> malformed
        _ -> malformed
  where
    stripped = Text.strip rawLine
    malformed = Left (CheckedArchitectureSummaryMalformedRecord lineNumber rawLine)
    allNonempty = all (not . Text.null . Text.strip)

validateDigest
  :: Int
  -> Text
  -> Either Phase1CheckedArchitectureSummaryError ()
validateDigest lineNumber raw =
  case Text.stripPrefix "sha256:" raw of
    Just digest
      | Text.length digest == 64
      , Text.all lowerHex digest -> Right ()
    _ -> Left (CheckedArchitectureSummaryMalformedDigest lineNumber raw)
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')
