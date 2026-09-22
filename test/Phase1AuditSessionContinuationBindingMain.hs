{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Phil.Core.Context as Context
import Phil.Core.Session
  ( MessageSpec (..), SessionError (..), SessionStep (..), sendEndpoint )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Branch (..), Control (..), Mode (..), Name (..), Outcome (..)
  , RefTerm (..), Session (..), Ty (..) )
import Phil.Surface.Check
  ( InitialBinding (..), PrimitiveSemantics (..), RejectionClass (..)
  , SurfaceCheckError (..), SurfaceCheckResult (..), SurfaceEnvironment (..)
  , SurfaceShape (..), checkSurfaceComponent, emptySurfaceEnvironment )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.IO (hPutStrLn, stderr)

-- Permanent replay for PHIL-AUD-SESSION-CONTINUATION-BINDING-001.
-- These cases execute the public parser/checker.  The lower-level controls at
-- the end deliberately confirm that ordinary session step helpers remain
-- descriptor/resource transitions; Surface performs occurrence substitution
-- only after the concrete message has been checked.
data Observed = Accepted | Rejected RejectionClass | HelperOK | Unexpected String
  deriving (Eq, Show)
data AuditCase = AuditCase String Observed Observed (Either String Observed)

success :: Outcome
success = Outcome "success"

end :: Session
end = End success

len :: Text -> RefTerm
len n = RefToNat (RefVar (Name n))

bytes :: Text -> Ty
bytes = TyBytes . len

scalarBinding :: (Text, InitialBinding)
scalarBinding = ("m", InitialBinding Unrestricted (TyUInt 16) PlainShape)

ambient :: (Text, InitialBinding)
ambient = ("n", InitialBinding Unrestricted (TyUInt 16) PlainShape)

owned :: Text -> Ty -> (Text, InitialBinding)
owned n ty = (n, InitialBinding Linear ty (case ty of
  TyBytes i -> OwnedBytesShape i Nothing
  _ -> PlainShape))

env :: Session -> [(Text, InitialBinding)] -> SurfaceEnvironment
env session bindings = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.fromList
      (("ep", InitialBinding Linear (TyEndpoint session) PlainShape) : bindings)
  , surfacePrimitives = Map.singleton "use" PrimitiveUse
  }

source :: [Text] -> Text
source body = Text.unlines ("component Audit {" : map ("  " <>) body ++ ["}"])

runSource :: SurfaceEnvironment -> [Text] -> Either String Observed
runSource environment body = do
  parsed <- case parseSurfaceFile "session-continuation-audit.phil" (source body) of
    Left err -> Left ("unexpected parser failure: " ++ show err)
    Right value -> Right value
  component <- case parsed of
    SurfaceFile [value] -> Right value
    _ -> Left "fixture did not parse to exactly one component"
  case checkSurfaceComponent environment component of
    Left err -> Right (Rejected (surfaceErrorClass err))
    Right result
      | checkedComponentName result == "Audit"
        && checkedTerminalControls result == [Closed success] -> Right Accepted
      | otherwise -> Right (Unexpected ("unexpected accepted control: " ++ show result))

sendSession :: Text -> Ty -> Session
sendSession formal payloadTy = Send (Name formal) (TyUInt 16)
  (Send (Name "body") payloadTy end)

recvSendSession :: Text -> Session
recvSendSession formal = Receive (Name formal) (TyUInt 16)
  (Send (Name "body") (bytes formal) end)

recvRecvSession :: Text -> Ty -> Session
recvRecvSession formal payloadTy = Receive (Name formal) (TyUInt 16)
  (Receive (Name "body") payloadTy end)

selectSession :: Text -> Ty -> Session
selectSession formal payloadTy = Select
  [Branch "length" (Just (Name formal, TyUInt 16))
    (Send (Name "body") payloadTy end)]

offerSession :: Text -> Bool -> Ty -> Session
offerSession formal receiveNext payloadTy = Offer
  [Branch "length" (Just (Name formal, TyUInt 16))
    ((if receiveNext then Receive else Send) (Name "body") payloadTy end)]

sendBody :: Text -> [Text]
sendBody value =
  [ "let ep1 = send " <> value <> " on ep"
  , "let ep2 = send payload on ep1"
  , "close ep2"
  ]

recvSendBody :: [Text]
recvSendBody =
  [ "let (ep1, got) = receive U16 on ep"
  , "let ep2 = send payload on ep1"
  , "close ep2"
  ]

recvRecvBody :: Text -> Text -> [Text]
recvRecvBody binder payloadType =
  [ "let (ep1, " <> binder <> ") = receive U16 on ep"
  , "let (ep2, payload) = receive " <> payloadType <> " on ep1"
  , "use(payload)"
  , "close ep2"
  ]

selectBody :: Text -> [Text]
selectBody value =
  [ "let ep1 = select length(" <> value <> ") on ep"
  , "let ep2 = send payload on ep1"
  , "close ep2"
  ]

offerSendBody :: [Text]
offerSendBody =
  [ "offer ep {"
  , "  length(got) => {"
  , "    let ep1 = send payload on ep"
  , "    close ep1"
  , "  }"
  , "}"
  ]

offerRecvBody :: Text -> [Text]
offerRecvBody binder =
  [ "offer ep {"
  , "  length(" <> binder <> ") => {"
  , "    let (ep1, payload) = receive OwnedBytes[" <> binder <> "] on ep"
  , "    use(payload)"
  , "    close ep1"
  , "  }"
  , "}"
  ]

cases :: [AuditCase]
cases =
  [ AuditCase "S01" (Rejected ExplicitTransport) Accepted $
      runSource (env (sendSession "n" (bytes "n"))
        [scalarBinding, ambient, owned "payload" (bytes "n")]) (sendBody "m")
  , AuditCase "S02" (Rejected ExplicitTransport) (Rejected ExplicitTransport) $
      runSource (env (sendSession "k" (bytes "k"))
        [scalarBinding, ambient, owned "payload" (bytes "n")]) (sendBody "m")
  , AuditCase "S03" Accepted (Rejected ExplicitTransport) $
      runSource (env (sendSession "n" (bytes "n"))
        [scalarBinding, owned "payload" (bytes "m")]) (sendBody "m")
  , AuditCase "S04" Accepted Accepted $
      runSource (env (sendSession "n" (bytes "n"))
        [ambient, owned "payload" (bytes "n")]) (sendBody "n")
  , AuditCase "S05" Accepted Accepted $
      runSource (env (sendSession "n" (TyBytes (RefNat 7)))
        [scalarBinding, owned "payload" (TyBytes (RefNat 7))]) (sendBody "m")
  , AuditCase "S06" (Rejected TypeMismatch) (Rejected TypeMismatch) $
      runSource (env (sendSession "n" (TyBytes (RefNat 7)))
        [scalarBinding, ("payload", InitialBinding Unrestricted (TyUInt 16) PlainShape)])
        (sendBody "m")
  , AuditCase "S07" (Rejected LinearCompletion) (Rejected LinearCompletion) $
      runSource (env (sendSession "n" (bytes "n"))
        [ambient, owned "payload" (bytes "n"), owned "extra" (TyBytes (RefNat 1))])
        (sendBody "n")
  , AuditCase "S08" (Rejected TypeMismatch) (Rejected TypeMismatch) $
      runSource (env (sendSession "n" (TyBytes (RefNat 7)))
        [("m", InitialBinding Unrestricted TyBool PlainShape), owned "payload" (TyBytes (RefNat 7))])
        (sendBody "m")
  , AuditCase "R01" (Rejected ExplicitTransport) Accepted $
      runSource (env (recvSendSession "n") [ambient, owned "payload" (bytes "n")]) recvSendBody
  , AuditCase "R02" (Rejected ExplicitTransport) (Rejected ExplicitTransport) $
      runSource (env (recvSendSession "k") [ambient, owned "payload" (bytes "n")]) recvSendBody
  , AuditCase "R03" Accepted (Rejected TypeMismatch) $
      runSource (env (recvRecvSession "n" (bytes "n")) []) (recvRecvBody "got" "OwnedBytes[got]")
  , AuditCase "R04" Accepted Accepted $
      runSource (env (recvRecvSession "n" (bytes "n")) []) (recvRecvBody "n" "OwnedBytes[n]")
  , AuditCase "R05" Accepted Accepted $
      runSource (env (recvRecvSession "n" (TyBytes (RefNat 7))) []) (recvRecvBody "got" "OwnedBytes[7]")
  , AuditCase "R06" (Rejected TypeMismatch) (Rejected TypeMismatch) $
      runSource (env (Receive (Name "n") (TyUInt 16) end) [])
        ["let (ep1, got) = receive U8 on ep", "close ep1"]
  , AuditCase "B01" (Rejected ExplicitTransport) Accepted $
      runSource (env (selectSession "n" (bytes "n"))
        [scalarBinding, ambient, owned "payload" (bytes "n")]) (selectBody "m")
  , AuditCase "B02" Accepted (Rejected ExplicitTransport) $
      runSource (env (selectSession "n" (bytes "n"))
        [scalarBinding, owned "payload" (bytes "m")]) (selectBody "m")
  , AuditCase "B03" Accepted Accepted $
      runSource (env (selectSession "n" (bytes "n"))
        [ambient, owned "payload" (bytes "n")]) (selectBody "n")
  , AuditCase "B04" (Rejected TypeMismatch) (Rejected TypeMismatch) $
      runSource (env (Select [Branch "length" Nothing end]) [scalarBinding])
        ["let ep1 = select length(m) on ep", "close ep1"]
  , AuditCase "O01" (Rejected ExplicitTransport) Accepted $
      runSource (env (offerSession "n" False (bytes "n"))
        [ambient, owned "payload" (bytes "n")]) offerSendBody
  , AuditCase "O02" Accepted (Rejected TypeMismatch) $
      runSource (env (offerSession "n" True (bytes "n")) []) (offerRecvBody "got")
  , AuditCase "O03" Accepted Accepted $
      runSource (env (offerSession "n" True (bytes "n")) []) (offerRecvBody "n")
  , AuditCase "O04" (Rejected BranchExhaustiveness) (Rejected BranchExhaustiveness) $
      runSource (env (offerSession "n" True (bytes "n")) []) ["offer ep {}"]
  , AuditCase "C01" HelperOK HelperOK helperContext
  , AuditCase "C02" HelperOK HelperOK helperReuse
  , AuditCase "C03" HelperOK HelperOK helperCollision
  , AuditCase "C04" HelperOK HelperOK helperLoan
  ]

baseContext :: Either String Context.ResourceContext
baseContext = do
  first <- either (Left . show) Right $
    Context.insertBinding Linear (Name "ep")
      (TyEndpoint (sendSession "n" (bytes "n"))) Context.emptyContext
  either (Left . show) Right $
    Context.insertBinding Unrestricted (Name "keep") TyBool first

helperContext :: Either String Observed
helperContext = do
  before <- baseContext
  step <- either (Left . show) Right $ sendEndpoint (Name "ep") (Name "ep1") before
  let continuation = Send (Name "body") (bytes "n") end
      expected = before
        { Context.linearBindings = Map.singleton (Name "ep1") (TyEndpoint continuation) }
  Right $ if stepMessage step == Just (MessageSpec (Name "n") (TyUInt 16))
       && stepSuccessor step == Just (Name "ep1", continuation)
       && stepContext step == expected
    then HelperOK else Unexpected (show step)

helperReuse :: Either String Observed
helperReuse = do
  before <- baseContext
  first <- either (Left . show) Right $ sendEndpoint (Name "ep") (Name "ep1") before
  Right $ case sendEndpoint (Name "ep") (Name "ep2") (stepContext first) of
    Left (SessionResourceError (Context.UnknownBinding (Name "ep"))) -> HelperOK
    other -> Unexpected (show other)

helperCollision :: Either String Observed
helperCollision = do
  before <- baseContext
  occupied <- either (Left . show) Right $
    Context.insertBinding Unrestricted (Name "ep1") TyBool before
  Right $ case sendEndpoint (Name "ep") (Name "ep1") occupied of
    Left (SessionResourceError (Context.DuplicateBinding (Name "ep1"))) -> HelperOK
    other -> Unexpected (show other)

helperLoan :: Either String Observed
helperLoan = do
  before <- baseContext
  loaned <- either (Left . show) Right $ Context.startSharedLoan (Name "ep") before
  Right $ case sendEndpoint (Name "ep") (Name "ep1") loaned of
    Left (SessionResourceError (Context.OwnerBorrowed (Name "ep"))) -> HelperOK
    other -> Unexpected (show other)

runCase :: Bool -> AuditCase -> IO String
runCase characterize (AuditCase ident intended frozen action) =
  case action of
    Left detail -> do
      putStrLn ("CASE\t" ++ ident ++ "\tINFRA")
      hPutStrLn stderr (ident ++ ": " ++ detail)
      pure "INFRA"
    Right actual -> do
      let expected = if characterize then frozen else intended
          good = actual == expected
          status = if characterize then (if good then "MATCH" else "MISMATCH")
                    else (if good then "PASS" else "FAIL")
      putStrLn ("CASE\t" ++ ident ++ "\t" ++ status)
      if good then pure () else hPutStrLn stderr
        (ident ++ ": expected " ++ show expected ++ "; actual " ++ show actual)
      pure status

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> run False
    ["--characterize"] -> run True
    _ -> hPutStrLn stderr "usage: Phase1AuditSessionContinuationBindingMain [--characterize]"
      >> exitWith (ExitFailure 2)
  where
    run characterize = do
      statuses <- mapM (runCase characterize) cases
      let code | "INFRA" `elem` statuses = 2
               | any (`elem` ["FAIL", "MISMATCH"]) statuses = 1
               | otherwise = 0
      putStrLn ("SUMMARY\t" ++ show (length cases) ++ "\t" ++ show code)
      exitWith (if code == 0 then ExitSuccess else ExitFailure code)
