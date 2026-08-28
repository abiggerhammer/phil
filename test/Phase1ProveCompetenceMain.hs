{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( DecisionCertificate (..)
  , checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Static
  ( declareOpaqueClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( InitialBinding (..)
  , PrimitiveSemantics (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax
  ( Component
  , Located
  , SurfaceFile (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "VER-013 definitional prove introduces exact evidence" definitionalProofAccepts
    , test "VER-013 exact in-scope evidence discharges opaque claim" evidenceProofAccepts
    , test "VER-013 checked decision certificate proves transparent arithmetic" decisionProofAccepts
    , test "VER-013 opaque claim without evidence rejects" opaqueProofRejects
    , test "VER-013 invalid certificate is rejected by the checked decision boundary" invalidCertificateRejects
    , test "VER-013 unchecked machine arithmetic cannot manufacture proof" uncheckedArithmeticRejects
    , test "VER-013 failed prove has no implicit runtime/assumption disposition" failedProveRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

definitionalProofAccepts :: Either String ()
definitionalProofAccepts =
  expectAccept baseEnvironment "component Definitional { prove true }"

evidenceProofAccepts :: Either String ()
evidenceProofAccepts = do
  staticContext <- mapLeft show $
    declareOpaqueClaim "OpaqueClaim" [] emptyStaticContext
  let proposition = Atom "OpaqueClaim" []
      environment = (emptySurfaceEnvironment staticContext)
        { surfaceInitialBindings = Map.singleton "evidence"
            (InitialBinding Unrestricted (TyProof proposition) PlainShape)
        }
  expectAccept environment "component Evidence { prove OpaqueClaim() }"

decisionProofAccepts :: Either String ()
decisionProofAccepts = do
  let proposition = LessThan (RefNat 1) (RefNat 2)
  certificate <- maybe
    (Left "builtin decision proposer failed to produce certificate for 1 < 2")
    Right
    (proposeDecisionCertificate emptyCheckState [] proposition)
  mapLeft show $ checkDecisionCertificate emptyCheckState [] proposition certificate
  expectAccept baseEnvironment "component Decision { prove 1 < 2 }"

opaqueProofRejects :: Either String ()
opaqueProofRejects = do
  staticContext <- mapLeft show $
    declareOpaqueClaim "OpaqueClaim" [] emptyStaticContext
  expectReject
    OpaqueProof
    (emptySurfaceEnvironment staticContext)
    "component Opaque { prove OpaqueClaim() }"

invalidCertificateRejects :: Either String ()
invalidCertificateRejects =
  let proposition = LessThan (RefNat 1) (RefNat 2)
  in case checkDecisionCertificate
      emptyCheckState
      []
      proposition
      CertificateTruth of
      Left _ -> Right ()
      Right () -> Left "invalid certificate shape was accepted"

uncheckedArithmeticRejects :: Either String ()
uncheckedArithmeticRejects =
  let uint = InitialBinding Unrestricted (TyUInt 32) PlainShape
      environment = baseEnvironment
        { surfaceInitialBindings = Map.fromList [("a", uint), ("b", uint)]
        , surfacePrimitives = Map.singleton
            "unchecked_u32_add"
            PrimitiveUncheckedU32Add
        }
      source =
        "component Unchecked(a, b) { "
          <> "let r = unchecked_u32_add(a, b) "
          <> "prove toNat(r) == toNat(a) + toNat(b) "
          <> "}"
  in expectReject UncheckedArithmetic environment source

failedProveRejects :: Either String ()
failedProveRejects =
  expectReject
    MissingEvidence
    baseEnvironment
    "component Failed { prove false }"

baseEnvironment :: SurfaceEnvironment
baseEnvironment = emptySurfaceEnvironment emptyStaticContext

expectAccept :: SurfaceEnvironment -> Text -> Either String ()
expectAccept environment source = do
  component <- parseOne source
  mapLeft show $ checkSurfaceComponent environment component
  Right ()

expectReject :: RejectionClass -> SurfaceEnvironment -> Text -> Either String ()
expectReject expected environment source = do
  component <- parseOne source
  case checkSurfaceComponent environment component of
    Left errorValue ->
      assert (surfaceErrorClass errorValue == expected)
        ("expected " <> show expected <> ", got " <> show errorValue)
    Right result -> Left ("expected rejection, got acceptance: " <> show result)

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show $ parseSurfaceFile "ver013" source
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
