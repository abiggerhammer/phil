module Main (main) where

import Phil.Surface.GrammarV1.DoublePingExecution (runInternalControls)

main :: IO ()
main = either fail (mapM_ putStrLn) runInternalControls
