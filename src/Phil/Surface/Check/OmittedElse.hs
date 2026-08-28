{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check.OmittedElse
  ( checkOmittedElseIdentity
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( ResourceContext (..)
  , joinContinuing
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
import Phil.Surface.Syntax (SourceSpan)

-- | EXEC-015: elaborate an omitted `else` as one exact continuing identity
-- predecessor. The false predecessor reuses the incoming SurfaceState verbatim
-- and contributes Unit. Continuing true predecessors must also be Unit-valued,
-- retain the same residual-obligation set, and pass the ordinary Core resource
-- join against that incoming state. Terminal/fatal/return true outcomes do not
-- participate in the continuing join.
checkOmittedElseIdentity
  :: SourceSpan
  -> SurfaceState
  -> [SurfacePath]
  -> Either SurfaceCheckError [SurfacePath]
checkOmittedElseIdentity span' incoming truePaths = do
  mapM_ (requireUnitTrueContinuation span') truePaths
  mapM_ requireIncomingObligations trueContinuing
  joinedContext <- mapLeft joinError $
    joinContinuing (map (resourceContext . stateCore . pathState) continuing)
  joinedState <- joinMetadata span' continuing joinedContext
  Right (stopped ++ [SurfacePath PathContinue joinedState (Just RuntimeUnit)])
  where
    falseIdentity = SurfacePath PathContinue incoming (Just RuntimeUnit)
    trueContinuing = filter ((== PathContinue) . pathControl) truePaths
    continuing = falseIdentity : trueContinuing
    stopped = filter ((/= PathContinue) . pathControl) truePaths

    requireIncomingObligations path
      | residualObligations (stateCore (pathState path))
          == residualObligations (stateCore incoming) = Right ()
      | otherwise = Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = IncompatibleBranchResidue
          , surfaceErrorDetail =
              "omitted else identity predecessor preserves incoming residual obligations exactly"
          }

    joinError errorValue = SurfaceCheckError
      { surfaceErrorSpan = span'
      , surfaceErrorClass = IncompatibleBranchResidue
      , surfaceErrorDetail = Text.pack (show errorValue)
      }

requireUnitTrueContinuation
  :: SourceSpan
  -> SurfacePath
  -> Either SurfaceCheckError ()
requireUnitTrueContinuation span' path
  | pathControl path /= PathContinue = Right ()
  | otherwise = case pathValue path of
      Just RuntimeUnit -> Right ()
      Just (RuntimeScalar scalar)
        | scalarType scalar == TyUnit -> Right ()
      _ -> Left SurfaceCheckError
        { surfaceErrorSpan = span'
        , surfaceErrorClass = TypeMismatch
        , surfaceErrorDetail =
            "continuing true arm of omitted-else if must produce Unit; explicit else is required for a non-Unit conditional value"
        }

joinMetadata
  :: SourceSpan
  -> [SurfacePath]
  -> ResourceContext
  -> Either SurfaceCheckError SurfaceState
joinMetadata span' paths joined = do
  let states = map pathState paths
      firstState = head states
      surviving = Map.filterWithKey
        (bindingSurvives joined)
        (stateBindings firstState)
  mapM_ (ensureAgrees surviving) (tail states)
  Right firstState
    { stateCore = (stateCore firstState) { resourceContext = joined }
    , stateBindings = surviving
    , stateFresh = maximum (map stateFresh states)
    , stateFrame = maximum (map stateFrame states)
    , stateActiveEndpoint = commonActiveEndpoint states surviving
    }
  where
    ensureAgrees surviving state = mapM_
      (\(name, meta) -> case Map.lookup name (stateBindings state) of
        Just other | other == meta -> Right ()
        _ -> Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = IncompatibleBranchResidue
          , surfaceErrorDetail =
              "continuing omitted-else predecessors disagree on metadata for " <> name
          })
      (Map.toList surviving)

bindingSurvives :: ResourceContext -> Text -> BindingMeta -> Bool
bindingSurvives context name meta = case bindingMode meta of
  Unrestricted -> Map.member (Name name) (unrestrictedBindings context)
  Affine -> Map.member (Name name) (affineBindings context)
  Linear -> Map.member (Name name) (linearBindings context)

commonActiveEndpoint :: [SurfaceState] -> Map.Map Text BindingMeta -> Maybe Text
commonActiveEndpoint states surviving = case map stateActiveEndpoint states of
  first : rest | all (== first) rest -> first
  _ -> case
    [ name
    | (name, meta) <- Map.toList surviving
    , TyEndpoint _ <- [bindingType meta]
    ] of
      [name] -> Just name
      _ -> Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
