module Phil.Surface.GrammarV1.TypeAlias
  ( grammarV1CheckedTypeAlias
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Route the first complete Grammar-v1 type-alias declaration fragment through
-- the uniform checked type dispatcher. This bounded bridge is intentionally
-- closed: aliases with generic parameters or requirements remain outside current
-- declaration competence, and the target is checked under an empty term scope so
-- a top-level alias cannot accidentally inherit caller-local bindings. Refinement
-- binders still establish their own lexical scope inside grammarV1CheckedType.
-- Core focusing rejection remains a distinct Left, while structurally unsupported
-- target types remain Nothing. No alias expansion, recursive alias environment,
-- structural-mode rule, generic instantiation, or fallback interpretation is
-- invented here.
grammarV1CheckedTypeAlias
  :: StaticContext
  -> GrammarV1TypeAliasDecl
  -> Maybe (Either FocusingError ((Text, Ty), [FocusStep]))
grammarV1CheckedTypeAlias staticContext source
  | not (null (grammarV1TypeAliasGenericParams source)) = Nothing
  | not (null (grammarV1TypeAliasRequirements source)) = Nothing
  | otherwise = do
      checked <- grammarV1CheckedType
        staticContext
        emptySurfaceState
        (locatedValue (grammarV1TypeAliasTarget source))
      pure $ fmap
        (\(ty, steps) ->
          ( (locatedValue (grammarV1TypeAliasName source), ty)
          , steps
          ))
        checked
