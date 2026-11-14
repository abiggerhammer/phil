{-# LANGUAGE OverloadedStrings #-}

-- P8 PR1: empirical *native* accepted-domain discrimination.
-- This is not a native-to-Rocq codec, acceptance oracle, or release certificate.
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest (..))
import Phil.Core.Generic
  ( GenericApplicationIdentity (..)
  , GenericApplicationIdentityError (..)
  , GenericStaticParameterKey (..)
  , deriveGenericApplicationIdentity
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Verification.NativeFinalInstanceCorrespondence
  ( NativeRawSystemsDigest (..)
  , NativeLoweringRootDigest (..)
  , encodeNativeRawSystemsDigestWire
  , encodeNativeLoweringRootWire
  , decodeNativeRawSystemsDigestWire
  , decodeNativeLoweringRootWire
  , encodeNativeSemanticAtomWire
  , decodeNativeSemanticAtomWire
  , encodeNativeSemanticOrderedAtomWires
  , encodeNativeSemanticUnorderedAtomWires
  , decodeNativeSemanticUnorderedAtomWires
  , encodeNativeSemanticRecordAtomFieldWires
  , decodeNativeSemanticRecordAtomFieldWires
  , encodeNativeGenericAtomApplicationWires
  , encodeNativeGenericActualsKeyDomainWires
  , decodeNativeGenericActualsKeyDomainWires
  , decodeNativeGenericStaticParameterKeyWire
  )

check :: String -> Bool -> IO ()
check name ok = do
  unless ok (error ("P8 boundary regression: " <> name))
  putStrLn ("P8 native: " <> name)

main :: IO ()
main = do
  let eAcute = Text.singleton '\x00E9'
      smile = Text.singleton '\x1F642'
      nul = Text.pack ['x', '\0', 'y']
      composed = eAcute
      decomposed = Text.pack ['e', '\x0301']
      atom x = SemanticAtom x
      nested = SemanticRecord (Map.fromList
        [ ("name", SemanticOrdered
            [atom eAcute, SemanticUnordered (Set.fromList [atom smile, atom nul])])
        , ("nul", atom nul)
        ])
      ka = GenericStaticParameterKey "alpha"
      kz = GenericStaticParameterKey "zeta"
      decl = DeclarationKey "example"
      iface = InterfaceRevision "rev"
      derived = deriveGenericApplicationIdentity decl iface
        [(kz, nested), (ka, atom smile)]

  -- Real native Text has legal values beyond the seven-bit diagnostic subset.
  -- The Text length below counts Unicode scalar values, not UTF-8 octets.
  check "U+00E9 and U+1F642 are distinct single Text characters"
    (Text.length eAcute == 1 && Text.length smile == 1 && eAcute /= smile)
  check "embedded NUL is preserved in Text and canonical SemanticForm"
    (Text.length nul == 3
      && Text.isInfixOf nul (canonicalSemanticForm (atom nul)))
  check "canonical SemanticForm distinguishes composed and decomposed Unicode"
    (Text.length composed == 1 && Text.length decomposed == 2
      && canonicalSemanticForm (atom composed)
           /= canonicalSemanticForm (atom decomposed))
  check "structured nested Unicode and NUL are representable native values"
    (Text.isInfixOf eAcute (canonicalSemanticForm nested)
      && Text.isInfixOf smile (canonicalSemanticForm nested)
      && Text.isInfixOf nul (canonicalSemanticForm nested))

  -- The existing generic identity constructor checks duplicate key input but
  -- does not narrow all SemanticForm values to SemanticAtom.
  case derived of
    Left _ -> error "P8 boundary regression: nested generic actual was rejected"
    Right application -> do
      check "native identity derivation retains complete recursive actuals"
        (genericApplicationSemanticArguments application
          == Map.fromList [(ka, atom smile), (kz, nested)])
      check "native key-domain wire is sorted and has exactly two keys"
        (encodeNativeGenericActualsKeyDomainWires application
          == ["Qalpha", "Qzeta"])
      check "atom-only application diagnostic refuses nested accepted-domain input"
        (encodeNativeGenericAtomApplicationWires application == Nothing)

  check "native duplicate generic argument is detected before Map insertion"
    (case deriveGenericApplicationIdentity decl iface
       [(ka, atom "first"), (ka, atom "second")] of
       Left (DuplicateGenericSemanticArgument key) -> key == ka
       _ -> False)
  check "native Map field order is canonical across construction orders"
    (canonicalSemanticForm (SemanticRecord (Map.fromList
       [("z", atom "last"), ("a", nested)]))
       == canonicalSemanticForm (SemanticRecord (Map.fromList
       [("a", nested), ("z", atom "last")])))
  check "native Set deduplicates and canonicalizes across input order"
    (SemanticUnordered (Set.fromList [atom "b", atom "a", atom "b"])
       == SemanticUnordered (Set.fromList [atom "a", atom "b"]))

  -- These existing partial wire decoders reconstruct UNACCEPTED native DATA,
  -- never the independently checked source, manifest or release.
  check "atom-only vector rejects recursive child"
    (encodeNativeSemanticOrderedAtomWires
       (SemanticOrdered [atom "ok", nested]) == Nothing)
  check "atom-only set rejects nested child"
    (encodeNativeSemanticUnorderedAtomWires
       (SemanticUnordered (Set.singleton nested)) == Nothing)
  check "atom-only record rejects nested field"
    (encodeNativeSemanticRecordAtomFieldWires nested == Nothing)
  check "native atom tag retains full Unicode payload"
    (encodeNativeSemanticAtomWire (atom smile)
       == Just (Text.cons 'M' smile))
  check "native role Q cannot be decoded as an M value"
    (decodeNativeSemanticAtomWire "Qalpha" == Nothing)
  check "native role M cannot be decoded as a Q key"
    (decodeNativeGenericStaticParameterKeyWire "Malpha" == Nothing)
  check "native set diagnostic rejects reversed wire order"
    (decodeNativeSemanticUnorderedAtomWires ["Mb", "Ma"] == Nothing)
  check "native set diagnostic rejects repeated member"
    (decodeNativeSemanticUnorderedAtomWires ["Ma", "Ma"] == Nothing)
  check "native record diagnostic rejects repeated field"
    (decodeNativeSemanticRecordAtomFieldWires
       [("Ha", "Mx"), ("Ha", "My")] == Nothing)
  check "native record diagnostic rejects reversed fields"
    (decodeNativeSemanticRecordAtomFieldWires
       [("Hb", "Mx"), ("Ha", "My")] == Nothing)
  check "native generic key-domain decoder rejects repeated key"
    (decodeNativeGenericActualsKeyDomainWires ["Qalpha", "Qalpha"] == Nothing)
  check "native generic key-domain decoder rejects reversed keys"
    (decodeNativeGenericActualsKeyDomainWires ["Qzeta", "Qalpha"] == Nothing)

  -- Identical textual payloads under distinct native digest roles are
  -- different data. A syntactically valid role wire is NOT accepted provenance.
  let raw = NativeRawSystemsDigest (Digest "same-text")
      lowering = NativeLoweringRootDigest (Digest "same-text")
  check "R and L remain different despite equal Text payloads"
    (encodeNativeRawSystemsDigestWire raw /= encodeNativeLoweringRootWire lowering)
  check "R role cannot be decoded as L"
    (decodeNativeLoweringRootWire (encodeNativeRawSystemsDigestWire raw)
       == Nothing)
  check "L role cannot be decoded as R"
    (decodeNativeRawSystemsDigestWire (encodeNativeLoweringRootWire lowering)
       == Nothing)

  putStrLn "P8 PR1: all native discriminating data probes passed; P8 remains OPEN."
