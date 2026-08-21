{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Static
  ( ClaimDefinition (..)
  , ClaimDecl (..)
  , StaticContext (..)
  , StaticError (..)
  , emptyStaticContext
  , declareTransparentClaim
  , declareOpaqueClaim
  , lookupClaim
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.SortCheck (SortError, validateRefSort)
import Phil.Core.Syntax
  ( Name
  , Proposition
  , RefSort
  )

data ClaimDefinition
  = TransparentClaim Proposition
  | OpaqueClaim
  deriving (Eq, Ord, Show)

data ClaimDecl = ClaimDecl
  { claimParameters :: [(Name, RefSort)]
  , claimDefinition :: ClaimDefinition
  }
  deriving (Eq, Ord, Show)

newtype StaticContext = StaticContext
  { staticClaims :: Map.Map Text ClaimDecl
  }
  deriving (Eq, Show)

data StaticError
  = DuplicateClaim Text
  | DuplicateClaimParameter Text Name
  | InvalidClaimParameterSort Text Name RefSort SortError
  deriving (Eq, Show)

emptyStaticContext :: StaticContext
emptyStaticContext = StaticContext Map.empty

declareTransparentClaim
  :: Text
  -> [(Name, RefSort)]
  -> Proposition
  -> StaticContext
  -> Either StaticError StaticContext
declareTransparentClaim name parameters body =
  declareClaim name parameters (TransparentClaim body)

declareOpaqueClaim
  :: Text
  -> [(Name, RefSort)]
  -> StaticContext
  -> Either StaticError StaticContext
declareOpaqueClaim name parameters =
  declareClaim name parameters OpaqueClaim

lookupClaim :: Text -> StaticContext -> Maybe ClaimDecl
lookupClaim name = Map.lookup name . staticClaims

declareClaim
  :: Text
  -> [(Name, RefSort)]
  -> ClaimDefinition
  -> StaticContext
  -> Either StaticError StaticContext
declareClaim name parameters definition context
  | Map.member name (staticClaims context) = Left (DuplicateClaim name)
  | otherwise = do
      ensureUniqueParameters Set.empty parameters
      mapM_ validateParameter parameters
      Right context
        { staticClaims = Map.insert name (ClaimDecl parameters definition) (staticClaims context)
        }
  where
    ensureUniqueParameters _ [] = Right ()
    ensureUniqueParameters seen ((parameter, _) : rest)
      | Set.member parameter seen = Left (DuplicateClaimParameter name parameter)
      | otherwise = ensureUniqueParameters (Set.insert parameter seen) rest

    validateParameter (parameter, sort) =
      case validateRefSort sort of
        Right () -> Right ()
        Left err -> Left (InvalidClaimParameterSort name parameter sort err)
