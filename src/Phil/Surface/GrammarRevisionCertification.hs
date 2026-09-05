module Phil.Surface.GrammarRevisionCertification
  ( CertifiedGrammarRevisionBundle
  , certifiedGrammarRevisionBundle
  , GrammarRevisionKernelFacts (..)
  , GrammarRevisionCertificationError (..)
  , certifyPortableSourceBundleGrammar
  , verifyGrammarRevisionKernelFacts
  ) where

import qualified GrammarRevisionKernel as Kernel
import Data.Text (Text)
import Phil.Surface.Lineage
  ( GrammarRevision
  , LineageError
  , PortableSourceBundle
  , decodePortableSourceBundleForGrammar
  , portableGrammarRevision
  )

newtype CertifiedGrammarRevisionBundle = CertifiedGrammarRevisionBundle
  { certifiedGrammarRevisionBundle :: PortableSourceBundle
  }
  deriving (Eq, Show)

data GrammarRevisionKernelFacts = GrammarRevisionKernelFacts
  { grammarRevisionCompetentPresent :: Bool
  , grammarRevisionExactSelected :: Bool
  , grammarRevisionPayloadIndependent :: Bool
  }
  deriving (Eq, Show)

data GrammarRevisionCertificationError
  = GrammarRevisionNativeError LineageError
  | GrammarRevisionKernelDisagreement GrammarRevisionKernelFacts
  deriving (Eq, Show)

certifyPortableSourceBundleGrammar
  :: GrammarRevision
  -> Text
  -> Either GrammarRevisionCertificationError CertifiedGrammarRevisionBundle
certifyPortableSourceBundleGrammar expected source = do
  bundle <- mapLeft GrammarRevisionNativeError
    (decodePortableSourceBundleForGrammar expected source)
  let facts = GrammarRevisionKernelFacts
        { grammarRevisionCompetentPresent = True
        , grammarRevisionExactSelected = portableGrammarRevision bundle == expected
        , grammarRevisionPayloadIndependent = True
        }
  verifyGrammarRevisionKernelFacts facts
  pure (CertifiedGrammarRevisionBundle bundle)

verifyGrammarRevisionKernelFacts
  :: GrammarRevisionKernelFacts
  -> Either GrammarRevisionCertificationError ()
verifyGrammarRevisionKernelFacts facts
  | Kernel.decideGrammarRevisionBindingByFacts
      (grammarRevisionCompetentPresent facts)
      (grammarRevisionExactSelected facts)
      (grammarRevisionPayloadIndependent facts) = Right ()
  | otherwise = Left (GrammarRevisionKernelDisagreement facts)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
