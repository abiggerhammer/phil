module Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , FieldInfo (..)
  , SurfaceShape (..)
  , InitialBinding (..)
  , PrimitiveSemantics (..)
  , SurfaceEnvironment (..)
  , SurfaceCheckResult (..)
  , emptySurfaceEnvironment
  , checkSurfaceComponent
  ) where

import qualified Phil.Surface.Check.Engine as Engine
import Phil.Surface.Check.Preflight (preflightComponent)
import Phil.Surface.Check.Types
import Phil.Surface.Syntax (Component, Located)

checkSurfaceComponent
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceCheckResult
checkSurfaceComponent environment component = do
  preflightComponent environment component
  Engine.checkSurfaceComponent environment component
