{-# LANGUAGE ScopedTypeVariables, TemplateHaskell,GADTs,ConstraintKinds,
DeriveDataTypeable,StandaloneDeriving #-}

module ProcessUtil where

import Control.Distributed.Process.Closure
import Control.Distributed.Process.Node
import Network.Transport.TCP
import Control.Distributed.Process
import Data.Binary
import Data.Typeable
import Network (withSocketsDo)
import Control.Concurrent (threadDelay,forkIO)
import Control.Concurrent.MVar
import Unsafe.Coerce
import qualified Data.Rank1Typeable as R1
--import qualified Data.ByteString as BS (writeFile,readFile)
--import qualified Data.ByteString.Lazy as L (toStrict)

--(+++) = Just 3 :: Maybe Integer
-- $(remotable ['(+++),'not])
--remoteTable = __remoteTable initRemoteTable

data Dict c where Dict :: c => Dict c deriving Typeable
instance Typeable c => Show (Dict c) where
    show (Dict :: Dict c) = ("Dict__"++) $ drop 5 $
                            show $ typeOf (undefined :: Dict c)
deriving instance Typeable Num
{-
newtype Tree a = Tree UT
data UT = Apply UT UT
        | Stat (Static Any) --bah
apply ::
-}
-- Serializable (= Binary + Typeable)
{-
data Ping = Ping deriving (Typeable)
instance Binary Ping where
    put Ping = putWord8 0
    get      = do { getWord8; return Ping }
server :: ReceivePort Ping -> Process ()
server rPing = do
    Ping <- receiveChan rPing
    liftIO $ putStrLn "Got a ping!"
client :: SendPort Ping -> Process ()
client sPing =
    sendChan sPing Ping
-}
{-ignition :: Process ()
ignition = do
  --liftIO $ threadDelay 1000000
  m <- unStatic $(mkStatic '(+++))
  say $ show m
    -- start the server
    --sPing <- spawnChannelLocal server
    -- start the client
    --spawnLocal $ client sPing

    --liftIO $ threadDelay 100000 -- wait a while-}

{-main :: IO ()
main = withSocketsDo $ do
         Right transport <- createTransport "127.0.0.1" "8080"
                            defaultTCPParameters
         node <- newLocalNode transport remoteTable
         runProcess node ignition-}
type KillSignal = ()
setupt :: RemoteTable -> IO (MVar (Either KillSignal (Process ())))
setupt remoteTable =
    withSocketsDo $ do
      t <- createTransport "127.0.0.1" "8080"
                        defaultTCPParameters
      case t of
        Left x ->
          error $ "Unable to connect: " ++ show x
        Right transport -> do
          node <- newLocalNode transport remoteTable
          mvar <- newEmptyMVar
          forkIO $ handler mvar node
          return mvar
            where
              handler mvar node =
                    do either <- takeMVar mvar
                       case either of
                         Right p -> forkIO (runProcess node p)
                                    >> handler mvar node
                         Left _ -> return ()
--BS.writeFile "localCloudHaskellNode.txt"
-- $ L.toStrict $ encode $ localNodeId node
--threadDelay $ 10 * 1000000run :: Process () -> IO ()
killNode killMVar = putMVar killMVar $ Left ()
run mvar p = putMVar mvar $ Right p
callproc mvar p = do result <- newEmptyMVar
                     run mvar (p >>= liftIO . putMVar result)
                     takeMVar result



