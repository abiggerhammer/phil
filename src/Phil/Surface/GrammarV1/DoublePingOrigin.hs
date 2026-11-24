{-# LANGUAGE OverloadedStrings #-}

-- Gate 1 correspondence only. Both selections and all keys are external
-- premises. The result has no authority to issue keys or activate processes.
module Phil.Surface.GrammarV1.DoublePingOrigin
  ( SourceAnchor (..), CandidateLineage (..), CandidateError (..)
  , Candidate, candidateDeclarations, candidateNetwork, candidateGraph
  , candidateSites, candidateActivation, candidateManifest
  , prepareCandidate, checkSelectedCandidate, sourceDigest
  ) where

import Control.Monad (unless)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as Bytes
import Data.List (nub, zipWith4)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as UTF8
import Numeric (showHex)
import Phil.Core.Focusing (FocusingError)
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual (GenericStaticActual (..), GenericStaticKind (..))
import Phil.Core.Process
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax (Outcome (..), Ty (..))
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
import Phil.Surface.GrammarV1.BinderScope
import Phil.Surface.GrammarV1.ComponentTwoStepChain
import Phil.Surface.GrammarV1.ParameterBodyScope
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.PatternBinderScope (grammarV1BindPattern)
import Phil.Surface.GrammarV1.ProgramSurface
import Phil.Surface.GrammarV1.ProtocolEndpointType
import Phil.Surface.GrammarV1.ProtocolRoles
import Phil.Surface.GrammarV1.SemanticComponentHeader
import Phil.Surface.Lineage (GrammarRevision (..), canonicalGrammarRevisionV1)
import Phil.Surface.Syntax (Located (..), SourcePoint (..), SourceSpan (..))

data SourceAnchor = SourceAnchor
  { anchorCommit :: Text
  , anchorBlob :: Text
  , anchorPath :: Text
  , anchorSHA256 :: Text
  }
  deriving (Eq, Show)

-- Ordered lists correspond to the fixed declaration, child, and process rows.
-- Text site IDs, stable keys, and occurrence keys are all proposed externally.
data CandidateLineage = CandidateLineage
  [(Text, DeclarationKey)] [OccurrenceSlotKey] [ProcessSiteKey]
  deriving (Eq, Show)

data CandidateError
  = SelectedOriginMismatch
  | InvalidSidecar
  | OriginHeaderMismatch
  | InvalidSourceEncoding
  | SourceParseFailure GrammarV1ParseDiagnostic
  | DeclarationInventory
  | DeclarationSiteMismatch Text
  | OccurrenceSiteMismatch Text
  | InvalidLineage
  | RevisionMismatch Text
  | ProgramSurfaceFailure FocusingError
  | ArchitectureSurfaceFailure FocusingError
  | SelectedTargetMismatch
  | ProgramInventory
  | ArchitectureInventory
  | ProtocolProfile
  | ProtocolRolesFailure GrammarV1ProtocolRoleError
  | ProtocolFamilyFailure ProtocolFamilyError
  | ComponentProfile Text
  | ComponentPattern Text Int
  | ComponentBodyFailure Text ChainError
  | ComponentHeaderFailure GrammarV1SemanticComponentHeaderError
  | GraphFailure ArchitectureInstantiationError
  | ProcessFailure ProcessNetworkError
  | ProcessTargetMismatch
  | ProvisioningFailure GrammarV1ArchitectureComponentProvisioningError
  | ActivationContractFailure GrammarV1ArchitectureComponentActivationError
  deriving (Eq, Show)

data Candidate = Candidate
  [DeclarationIdentity] ArchitectureInstanceGraph [ProcessDeclarationSite]
  ProcessNetwork [GrammarV1ResolvedComponentActivation] Bytes.ByteString
  deriving (Eq, Show)

candidateDeclarations :: Candidate -> [DeclarationIdentity]
candidateDeclarations (Candidate declarations _ _ _ _ _) = declarations

candidateGraph :: Candidate -> ArchitectureInstanceGraph
candidateGraph (Candidate _ graph _ _ _ _) = graph

candidateSites :: Candidate -> [ProcessDeclarationSite]
candidateSites (Candidate _ _ sites _ _ _) = sites

candidateNetwork :: Candidate -> ProcessNetwork
candidateNetwork (Candidate _ _ _ network _ _) = network

candidateActivation :: Candidate -> [GrammarV1ResolvedComponentActivation]
candidateActivation (Candidate _ _ _ _ activation _) = activation

candidateManifest :: Candidate -> Bytes.ByteString
candidateManifest (Candidate _ _ _ _ _ manifest) = manifest

-- The pinned commit/blob/path are supplied by the independent selection.
-- This comparison proves equality with that selection. There is no issuer
-- lookup here. Offline callers can exercise this with a separate test oracle.
checkSelectedCandidate
  :: SourceAnchor -> (Bytes.ByteString, Bytes.ByteString)
  -> (Bytes.ByteString, Bytes.ByteString) -> Either CandidateError Candidate
checkSelectedCandidate anchor selected actual@(source, manifest) = do
  require SelectedOriginMismatch (actual == selected)
  rows <- either (const (Left InvalidSidecar)) (Right . map (Text.splitOn "\t") . Text.lines)
    (UTF8.decodeUtf8' manifest)
  let (header, body) = splitAt 5 rows
  require OriginHeaderMismatch $
    header == originHeader anchor && sourceDigest source == anchorSHA256 anchor
  (declRows, occurrenceRows, lineage) <- decodeRows body
  (expected, candidate) <- prepareRows anchor source lineage
  let (expectedDeclarations, expectedOccurrences) = splitAt 5 expected
  mapM_ checkDeclaration (zip declRows expectedDeclarations)
  mapM_ checkOccurrence (zip occurrenceRows expectedOccurrences)
  require InvalidSidecar (manifest == encodeRows (header ++ expected))
  pure candidate
  where
    checkDeclaration (actualRow, expectedRow) = case expectedRow of
      _ : label : _ -> do
        require (DeclarationSiteMismatch label) (take 7 actualRow == take 7 expectedRow)
        require (RevisionMismatch label) (drop 7 actualRow == drop 7 expectedRow)
      _ -> Left InvalidSidecar
    checkOccurrence (actualRow, expectedRow) = case expectedRow of
      _ : label : _ -> require (OccurrenceSiteMismatch label) (actualRow == expectedRow)
      _ -> Left InvalidSidecar

-- Candidate authoring tool. Its output confers no selection or issuance.
prepareCandidate
  :: SourceAnchor -> Bytes.ByteString -> CandidateLineage
  -> Either CandidateError (Bytes.ByteString, Candidate)
prepareCandidate anchor source lineage = do
  (rows, candidate) <- prepareRows anchor source lineage
  pure (encodeRows (originHeader anchor ++ rows), candidate)

originHeader :: SourceAnchor -> [[Text]]
originHeader (SourceAnchor commit blob path digest) =
  [ ["FSEM03-DOUBLEPING-ORIGIN-V1"]
  , ["origin", "abiggerhammer/phil", commit, blob, path]
  , ["source-sha256", digest]
  , ["grammar", unGrammarRevision canonicalGrammarRevisionV1]
  , ["offsets", "unicode-code-points", "zero-based", "exclusive-end"]
  ]

sourceDigest :: Bytes.ByteString -> Text
sourceDigest = Text.pack . concatMap hex . Bytes.unpack . SHA256.hash
  where
    hex byte = case showHex byte "" of
      [digit] -> ['0', digit]
      digits -> digits

encodeRows :: [[Text]] -> Bytes.ByteString
encodeRows = UTF8.encodeUtf8 . Text.unlines . map (Text.intercalate "\t")

decodeRows :: [[Text]] -> Either CandidateError ([[Text]], [[Text]], CandidateLineage)
decodeRows rows = case splitAt 5 rows of
  (decls, [root@["root", _, _, _],
           client@["child", _, clientSlot, _, _, _, _],
           server@["child", _, serverSlot, _, _, _, _],
           clientProcess@["process", _, clientSite, _, _, _, _],
           serverProcess@["process", _, serverSite, _, _, _, _]])
    | length decls == 5 -> do
        keys <- mapM declarationKeyRow decls
        pure (decls, [root, client, server, clientProcess, serverProcess],
          CandidateLineage keys (map OccurrenceSlotKey [clientSlot, serverSlot])
            (map ProcessSiteKey [clientSite, serverSite]))
  _ -> Left InvalidSidecar
  where
    declarationKeyRow ["decl", _, _, site, key, _, _, _, _] =
      Right (site, DeclarationKey key)
    declarationKeyRow _ = Left InvalidSidecar

require :: e -> Bool -> Either e ()
require err = flip unless (Left err)

checked :: e -> (a -> e) -> Maybe (Either a b) -> Either e b
checked fallback wrap = maybe (Left fallback) (mapError wrap)

mapError :: (a -> b) -> Either a c -> Either b c
mapError wrap = either (Left . wrap) Right

tag :: Text -> [SemanticForm] -> SemanticForm
tag label fields = SemanticOrdered (SemanticAtom label : fields)

u8 :: SemanticForm
u8 = tag "uint" [SemanticAtom "8"]

number :: Int -> SemanticForm
number = SemanticAtom . Text.pack . show

identityForm :: DeclarationIdentity -> SemanticForm
identityForm ident = tag "identity" (map SemanticAtom
  [ unDeclarationKey (identityDeclarationKey ident)
  , unInterfaceRevision (identityInterfaceRevision ident)
  , unDefinitionRevision (identityDefinitionRevision ident)
  ])

derive :: Text -> DeclarationKey -> SemanticForm -> SemanticForm -> DeclarationIdentity
derive name key interface definition = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation name []
  , declarationKey = key
  , declarationInterfaceSemantics = interface
  , declarationDefinitionSemantics = definition
  }

prepareRows
  :: SourceAnchor -> Bytes.ByteString -> CandidateLineage
  -> Either CandidateError ([[Text]], Candidate)
prepareRows anchor source
    (CandidateLineage lineage@[pLine, cLine, sLine, aLine, mLine] [cSlot, sSlot] [cSite, sSite]) = do
  require OriginHeaderMismatch (sourceDigest source == anchorSHA256 anchor)
  let pKey = snd pLine
      cKey = snd cLine
      sKey = snd sLine
      aKey = snd aLine
      mKey = snd mLine
      valid prefix input = case Text.stripPrefix prefix input of
        Just token -> not (Text.null token) && Text.all tokenChar token
        Nothing -> False
      tokenChar c = c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c == '-'
      distinct inputs = nub inputs == inputs
  require InvalidLineage $
    all (valid "site:" . fst) lineage && all (valid "decl:" . unDeclarationKey . snd) lineage
    && distinct (map fst lineage) && distinct (map snd lineage)
    && all (valid "slot:" . unOccurrenceSlotKey) [cSlot, sSlot] && cSlot /= sSlot
    && all (valid "process:" . unProcessSiteKey) [cSite, sSite] && cSite /= sSite
  text <- either (const (Left InvalidSourceEncoding)) Right (UTF8.decodeUtf8' source)
  parsed <- mapError SourceParseFailure (parseGrammarV1StructuralSource (anchorPath anchor) text)
  let tops = grammarV1TopLevelDecls parsed
      declarations = map (grammarV1Declaration . locatedValue) tops
  require DeclarationInventory $
    grammarV1ModuleDecl parsed == Nothing && null (grammarV1ImportDecls parsed)
    && all (null . grammarV1Attributes . locatedValue) tops
  (protocol, client, server, architecture, program) <- case map locatedValue declarations of
    [GrammarV1ProtocolDeclaration p, GrammarV1ComponentDeclaration c,
     GrammarV1ComponentDeclaration s, GrammarV1ArchitectureDeclaration a,
     GrammarV1ProgramDeclaration m]
      | locatedValue (grammarV1ProtocolName p) == "DoublePing"
      , locatedValue (grammarV1ComponentName c) == "ClientWorker"
      , locatedValue (grammarV1ComponentName s) == "ServerWorker"
      , locatedValue (grammarV1ArchitectureName a) == "LocalDoublePing"
      , locatedValue (grammarV1ProgramName m) == "main" -> Right (p, c, s, a, m)
    _ -> Left DeclarationInventory
  -- The surface checkers copy this metadata through. They do not consult it
  -- when checking their semantic fields. The record is replaced below once D
  -- has been computed from the checked facts.
  let pending = DefinitionRevision ""
  programSurface <- checked ProgramInventory ProgramSurfaceFailure $
    grammarV1CheckedProgramSurface emptyStaticContext mKey pending program
  require SelectedTargetMismatch $
    checkedProgramTargetKind programSurface == GenericArchitectureDependencyKind
    && checkedProgramTargetReference programSurface ==
      ReferencedGenericStaticActual (locatedValue (grammarV1ArchitectureName architecture))
  require ProgramInventory (null (checkedProgramItems programSurface))
  surface <- checked ArchitectureInventory ArchitectureSurfaceFailure $
    grammarV1CheckedArchitectureSurface emptyStaticContext aKey pending architecture
  checkInventory (checkedArchitectureItems surface)
  (cChildItem, sChildItem, cProcessItem, sProcessItem) <- case grammarV1ArchitectureItems architecture of
    first : second : third : fourth : _ -> Right (first, second, third, fourth)
    _ -> Left ArchitectureInventory
  pIdentity <- protocolIdentity pKey protocol
  let ref = ReferencedGenericStaticActual "DoublePing"
  family <- checked ProtocolProfile ProtocolRolesFailure $
    grammarV1ClosedBinaryProtocolFamily pKey (identityInterfaceRevision pIdentity) protocol
  instanceValue <- mapError ProtocolFamilyFailure $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  cProjection <- mapError ProtocolFamilyFailure $ projectProtocolRole instanceValue (ProtocolRoleKey "Client")
  sProjection <- mapError ProtocolFamilyFailure $ projectProtocolRole instanceValue (ProtocolRoleKey "Server")
  let resolutions = [GrammarV1ProtocolEndpointResolution ref instanceValue]
  (cIdentity, cHeader) <- componentIdentity True resolutions pIdentity cProjection cKey client
  (sIdentity, sHeader) <- componentIdentity False resolutions pIdentity sProjection sKey server
  let root = InstanceKey ("phil.grammar-v1.program-instance.v1:" <> unDeclarationKey mKey)
      aIdentity = architectureIdentity aKey pIdentity cIdentity sIdentity cSlot sSlot cSite sSite
      programInterface = tag "phil.program.doubleping-interface.v1"
        (map (flip tag []) ["entries", "exports", "observables", "assumptions"])
      mIdentity = derive "main" mKey programInterface
        (tag "phil.program.doubleping-definition.v1"
          [programInterface, tag "instantiate" [identityForm aIdentity, atomKey root]])
      identities = [pIdentity, cIdentity, sIdentity, aIdentity, mIdentity]
      node ident children = ArchitectureNodeSpec ident Map.empty [] children []
  graph <- mapError GraphFailure $ instantiateArchitecture root (node aIdentity
    [ArchitectureChildSpec cSlot (node cIdentity []), ArchitectureChildSpec sSlot (node sIdentity [])])
  owner <- maybe (Left ProcessTargetMismatch) Right (Map.lookup root (architectureGraphInstances graph))
  let child slot = maybe (Left ProcessTargetMismatch) Right (Map.lookup slot (checkedArchitectureChildren owner))
  cTarget <- child cSlot
  sTarget <- child sSlot
  let sites = [ScopedProcessDeclarationSite root cSite cTarget, ScopedProcessDeclarationSite root sSite sTarget]
  network <- mapError ProcessFailure (elaborateProcessNetwork graph sites)
  let provision occurrence site target component header = do
        key <- case [processOccurrenceKey process
                    | process <- Map.elems (processNetworkPopulation network)
                    , processOccurrenceOwner process == architectureGraphRoot graph
                    , identityInstanceKey (processOccurrenceTarget process) == target] of
          [one] -> Right one
          _ -> Left ProcessTargetMismatch
        result <- mapError ProvisioningFailure $
          grammarV1ResolveArchitectureComponentProvisioning
            surface {checkedArchitectureDefinitionRevision = identityDefinitionRevision aIdentity}
            occurrence site key component header
            [GrammarV1ArchitectureProtocolOccurrence "ping" ref instanceValue]
        mapError ActivationContractFailure (grammarV1ResolvedComponentActivation result)
  cActivation <- provision "client" "client_run" cTarget client cHeader
  sActivation <- provision "server" "server_run" sTarget server sHeader
  let declMeta = [("DoublePing", "protocol"), ("ClientWorker", "component"), ("ServerWorker", "component"),
                  ("LocalDoublePing", "architecture"), ("main", "program")]
      declRow (name, kind) (site, key) declaration ident =
        ["decl", name, kind, site, unDeclarationKey key] ++ offsets declaration ++
          [unInterfaceRevision (identityInterfaceRevision ident), unDefinitionRevision (identityDefinitionRevision ident)]
      occurrenceRows =
        [ ["root", "main", unInstanceKey root, "LocalDoublePing"]
        , ["child", "client", unOccurrenceSlotKey cSlot, "LocalDoublePing", "ClientWorker"] ++ offsets cChildItem
        , ["child", "server", unOccurrenceSlotKey sSlot, "LocalDoublePing", "ServerWorker"] ++ offsets sChildItem
        , ["process", "client_run", unProcessSiteKey cSite, unInstanceKey root, unOccurrenceSlotKey cSlot] ++ offsets cProcessItem
        , ["process", "server_run", unProcessSiteKey sSite, unInstanceKey root, unOccurrenceSlotKey sSlot] ++ offsets sProcessItem
        ]
      rows = zipWith4 declRow declMeta lineage declarations identities ++ occurrenceRows
  pure (rows, Candidate identities graph sites network [cActivation, sActivation]
    (encodeRows (originHeader anchor ++ rows)))
  where
    atomKey = SemanticAtom . unInstanceKey
prepareRows _ _ _ = Left InvalidLineage

offsets :: Located a -> [Text]
offsets (Located spanValue _) = map (Text.pack . show . sourcePointOffset)
  [sourceSpanStart spanValue, sourceSpanEnd spanValue]

protocolIdentity :: DeclarationKey -> GrammarV1ProtocolDecl -> Either CandidateError DeclarationIdentity
protocolIdentity key source = do
  ((client, send), (server, receive)) <- checked ProtocolProfile ProtocolRolesFailure
    (grammarV1CheckedClosedProtocolRoleTemplates source)
  let done = ProtocolTemplateEnd (Outcome "Done")
  require ProtocolProfile $
    client == ProtocolRoleKey "Client" && server == ProtocolRoleKey "Server"
    && case (send, receive) of
      (ProtocolTemplateSend _ (ProtocolConcreteType (TyUInt 8))
        (ProtocolTemplateSend _ (ProtocolConcreteType (TyUInt 8)) endSend),
       ProtocolTemplateReceive _ (ProtocolConcreteType (TyUInt 8))
        (ProtocolTemplateReceive _ (ProtocolConcreteType (TyUInt 8)) endReceive)) ->
          endSend == done && endReceive == done
      _ -> False
  sendForm <- templateForm send
  receiveForm <- templateForm receive
  let interface = tag "phil.protocol.closed-binary-interface.v1"
        [tag "generic-parameters" [], tag "requirements" [],
         tag "roles" [roleForm client sendForm, roleForm server receiveForm]]
  pure (derive "DoublePing" key interface (tag "phil.protocol.closed-binary-definition.v1" [interface]))
  where
    roleForm role session = tag "role" [SemanticAtom (unProtocolRoleKey role), session]

templateForm :: ProtocolSessionTemplate -> Either CandidateError SemanticForm
templateForm template = case template of
  ProtocolTemplateSend _ (ProtocolConcreteType (TyUInt 8)) next ->
    fmap (\rest -> tag "send" [u8, rest]) (templateForm next)
  ProtocolTemplateReceive _ (ProtocolConcreteType (TyUInt 8)) next ->
    fmap (\rest -> tag "receive" [u8, rest]) (templateForm next)
  ProtocolTemplateEnd (Outcome outcome) -> Right (tag "end" [SemanticAtom outcome])
  _ -> Left ProtocolProfile

componentIdentity
  :: Bool -> [GrammarV1ProtocolEndpointResolution] -> DeclarationIdentity
  -> ProtocolProjectionEvidence -> DeclarationKey -> GrammarV1ComponentDecl
  -> Either CandidateError (DeclarationIdentity, GrammarV1CheckedSemanticComponentHeader)
componentIdentity isClient resolutions protocol projection key source = do
  let name = locatedValue (grammarV1ComponentName source)
      profileError = ComponentProfile name
      shape = if isClient then bare else pair
  (firstPattern, firstAction, secondPattern, secondAction) <-
    case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody source)) of
      [Located _ (GrammarV1LetStatement p1 e1), Located _ (GrammarV1LetStatement p2 e2), _] ->
        Right (p1, e1, p2, e2)
      _ -> Left (ComponentBodyFailure name ChainUnsupportedSourceShape)
  require (ComponentPattern name 1) (shape firstPattern)
  require (ComponentPattern name 2) (shape secondPattern)
  chain <- mapError (ComponentBodyFailure name) $
    (if isClient then checkSendChain else checkReceiveChain) resolutions projection key source
  (header, _) <- checked profileError ComponentHeaderFailure $
    grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
      emptyStaticContext resolutions key (DefinitionRevision "") source
  params <- maybe (Left profileError) Right (checkedSemanticComponentParameters header)
  require profileError $
    map (grammarV1ResolvedBinderDisplayName . fst) params ==
      (if isClient then ["endpoint", "first", "second"] else ["endpoint"])
    && map snd params == (TyEndpoint (protocolProjectionSession projection) :
      if isClient then [TyUInt 8, TyUInt 8] else [])
    && checkedSemanticComponentProvidesType header == Nothing
  let session = tag (if isClient then "send" else "receive")
        [u8, tag (if isClient then "send" else "receive") [u8, tag "end" [SemanticAtom "Done"]]]
      endpoint = tag "endpoint"
        [ SemanticAtom (unDeclarationKey (identityDeclarationKey protocol))
        , SemanticAtom (unInterfaceRevision (identityInterfaceRevision protocol))
        , SemanticAtom (unProtocolRoleKey (protocolProjectionRole projection))
        , session
        ]
      parameter binder ty = tag "parameter" (SemanticAtom (grammarV1ResolvedBinderDisplayName binder) :
        case ty of
          TyEndpoint _ -> [SemanticAtom "linear", endpoint]
          _ -> [SemanticAtom "unrestricted", u8])
      interface = tag "phil.component.doubleping-interface.v1"
        [tag "parameters" (map (uncurry parameter) params), tag "provides" []]
      ordinal core = maybe (Left profileError) (Right . grammarV1BinderOrdinal)
        (grammarV1DecodeBinderCoreName core)
      payloadOrdinal scope expression = case locatedValue expression of
        GrammarV1SendExpression payload _ ->
          maybe (Left profileError)
            (Right . grammarV1BinderOrdinal . grammarV1ResolvedBinderKey . grammarV1CheckedLocalValueBinder)
            (grammarV1CheckedLocalValueOccurrenceInScope scope payload)
        _ -> Left profileError
  before <- ordinal (chainBefore chain)
  middle <- ordinal (chainMiddle chain)
  final <- ordinal (chainFinal chain)
  require profileError (before == 0)
  let step action input output role = tag action [u8, number input, number output, number role]
      initial = checkedSemanticComponentLexicalScope header
      bindResult patternSource = mapError (const profileError) . grammarV1BindPattern GrammarV1LetPatternBinder patternSource
  (firstBinders, afterFirst) <- bindResult firstPattern initial
  (secondBinders, _) <- bindResult secondPattern afterFirst
  actions <- if isClient
    then do
      first <- payloadOrdinal initial firstAction
      second <- payloadOrdinal afterFirst secondAction
      pure [step "send" before middle first, step "send" middle final second]
    else case (firstBinders, secondBinders) of
      ([_, value1], [_, value2]) ->
        let valueOrdinal = grammarV1BinderOrdinal . grammarV1ResolvedBinderKey
        in pure [step "receive" before middle (valueOrdinal value1),
                 step "receive" middle final (valueOrdinal value2)]
      _ -> Left profileError
  let definition = tag "phil.component.doubleping-definition.v1"
        [interface, tag "body" (actions ++ [tag "close" [number final]])]
      ident = derive name key interface definition
  pure (ident, header {checkedSemanticComponentDefinitionRevision = identityDefinitionRevision ident})
  where
    bare (Located _ (GrammarV1IdentifierPattern _)) = True
    bare _ = False
    pair (Located _ (GrammarV1TuplePattern [a, b])) = bare a && bare b
    pair _ = False

checkInventory :: [GrammarV1CheckedArchitectureItem] -> Either CandidateError ()
checkInventory items = require ArchitectureInventory $
  map inventoryItem items ==
    map Just
      [ ["instance", "client", "ClientWorker"], ["instance", "server", "ServerWorker"]
      , ["process", "client_run", "client"], ["process", "server_run", "server"]
      , ["protocol", "ping", "DoublePing"]
      , ["internal", "ping.Client", "client"], ["internal", "ping.Server", "server"]
      , ["entry-u8", "first"], ["entry-u8", "second"]
      , ["bind", "client.endpoint", "ping.Client"], ["bind", "client.first", "first"]
      , ["bind", "client.second", "second"], ["bind", "server.endpoint", "ping.Server"]
      ]
  where
    inventoryItem item = case item of
      GrammarV1CheckedArchitectureInstance name (ReferencedGenericStaticActual target) -> Just ["instance", name, target]
      GrammarV1CheckedArchitectureProcess name target -> Just ["process", name, target]
      GrammarV1CheckedArchitectureProtocol name (ReferencedGenericStaticActual target) -> Just ["protocol", name, target]
      GrammarV1CheckedArchitectureRole name (GrammarV1CheckedInternalRoleTarget target) -> Just ["internal", name, target]
      GrammarV1CheckedArchitectureEntry name (TyUInt 8) _ -> Just ["entry-u8", name]
      GrammarV1CheckedArchitectureBind name target -> Just ["bind", name, target]
      _ -> Nothing

architectureIdentity
  :: DeclarationKey -> DeclarationIdentity -> DeclarationIdentity -> DeclarationIdentity
  -> OccurrenceSlotKey -> OccurrenceSlotKey -> ProcessSiteKey -> ProcessSiteKey -> DeclarationIdentity
architectureIdentity key protocol client server cSlot sSlot cSite sSite =
  derive "LocalDoublePing" key interface definition
  where
    entry label = tag "entry" [SemanticAtom label, SemanticAtom "unrestricted", u8]
    interface = tag "phil.architecture.doubleping-interface.v1"
      [tag "entries" [entry "first", entry "second"], tag "external-contracts" []]
    child slot ident = tag "child" [SemanticAtom (unOccurrenceSlotKey slot), identityForm ident]
    process site slot = tag "root-owned-process"
      [SemanticAtom (unProcessSiteKey site), SemanticAtom (unOccurrenceSlotKey slot)]
    role name slot = tag "internal-role" [SemanticAtom name, SemanticAtom (unOccurrenceSlotKey slot)]
    bind slot label rhs = tag "bind" [SemanticAtom (unOccurrenceSlotKey slot), SemanticAtom label, rhs]
    entryRef name = tag "entry-ref" [SemanticAtom name]
    endpoint name = tag "protocol-role-ref" [SemanticAtom "ping", SemanticAtom name]
    definition = tag "phil.architecture.doubleping-definition.v1"
      [ interface
      , tag "children" [child cSlot client, child sSlot server]
      , tag "processes" [process cSite cSlot, process sSite sSlot]
      , tag "protocol-occurrence" [SemanticAtom "ping", identityForm protocol]
      , tag "roles" [role "Client" cSlot, role "Server" sSlot]
      , tag "bindings"
        [ bind cSlot "endpoint" (endpoint "Client")
        , bind cSlot "first" (entryRef "first")
        , bind cSlot "second" (entryRef "second")
        , bind sSlot "endpoint" (endpoint "Server")
        ]
      ]
