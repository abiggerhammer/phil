{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Ty (..))
import Phil.Surface.Check
  ( InitialBinding (..)
  , PrimitiveSemantics (..)
  , RejectionClass (..)
  , SurfaceCallableSignature (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (Component, Located, SurfaceFile (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 invoke accepts exact checked signature" validLinearInvoke
    , test "CALL-019 invoke transfers a restricted argument" invokeConsumesLinear
    , test "CALL-019 unknown callable rejects at callable competence" unknownCallableRejects
    , test "CALL-019 provider primitive cannot rescue invoke lookup" primitiveCannotRescueInvoke
    , test "CALL-019 ordinary call remains provider primitive lookup" ordinaryCallRemainsPrimitive
    , test "CALL-019 callable result carries declared restricted mode" restrictedResultReturns
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

blobType :: Ty
blobType = TyOpaque "Blob"

candidateBinding :: InitialBinding
candidateBinding = InitialBinding Linear blobType PlainShape

callable :: Text -> [(Mode, Ty)] -> Maybe (Mode, Ty) -> SurfaceCallableSignature
callable key parameters result = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = DeclarationKey key
  , surfaceCallableParameters = parameters
  , surfaceCallableResult = result
  }

takeSignature :: SurfaceCallableSignature
takeSignature = callable "decl.take" [(Linear, blobType)] Nothing

baseWithCandidate :: SurfaceEnvironment
baseWithCandidate = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "candidate" candidateBinding
  , surfaceCallables = Map.singleton "Take" takeSignature
  }

validLinearInvoke :: Either String ()
validLinearInvoke = expectAccept baseWithCandidate
  "component Caller(candidate) { invoke Take(candidate) return unit }"

invokeConsumesLinear :: Either String ()
invokeConsumesLinear = expectReject StructuralUse baseWithCandidate
  "component Caller(candidate) { invoke Take(candidate) return candidate }"

unknownCallableRejects :: Either String ()
unknownCallableRejects = expectReject UnknownCallable
  (emptySurfaceEnvironment emptyStaticContext)
  "component Caller { invoke Missing() return unit }"

namespaceEnvironment :: SurfaceEnvironment
namespaceEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "candidate" candidateBinding
  , surfacePrimitives = Map.singleton "Worker" PrimitiveUse
  , surfaceCallables = Map.singleton "Worker"
      (callable "decl.worker" [] Nothing)
  }

primitiveCannotRescueInvoke :: Either String ()
primitiveCannotRescueInvoke = expectReject TypeMismatch namespaceEnvironment
  "component Caller(candidate) { invoke Worker(candidate) return unit }"

ordinaryCallRemainsPrimitive :: Either String ()
ordinaryCallRemainsPrimitive = expectAccept namespaceEnvironment
  "component Caller(candidate) { Worker(candidate) return unit }"

restrictedResultReturns :: Either String ()
restrictedResultReturns = expectAccept
  ((emptySurfaceEnvironment emptyStaticContext)
    { surfaceCallables = Map.singleton "Maker"
        (callable "decl.maker" [] (Just (Linear, blobType)))
    })
  "component Caller { let result = invoke Maker() return result }"

expectAccept :: SurfaceEnvironment -> Text -> Either String ()
expectAccept environment source = do
  component <- parseOne source
  _ <- mapLeft show (checkSurfaceComponent environment component)
  Right ()

expectReject :: RejectionClass -> SurfaceEnvironment -> Text -> Either String ()
expectReject expected environment source = do
  component <- parseOne source
  case checkSurfaceComponent environment component of
    Left err
      | surfaceErrorClass err == expected -> Right ()
      | otherwise -> Left ("expected " <> show expected <> ", got " <> show err)
    Right result -> Left ("expected rejection, got acceptance: " <> show result)

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-surface" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
