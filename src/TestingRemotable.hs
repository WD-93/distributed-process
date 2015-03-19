{-# LANGUAGE TemplateHaskell, StandaloneDeriving, DeriveDataTypeable,
RankNTypes, PolyKinds #-}
import Remotable
import ProcessUtil
import Tree
import RTD
import Control.Distributed.Process.Node (initRemoteTable)
import Data.Rank1Typeable
import Data.Rank1Dynamic
import Unsafe.Coerce
import qualified Data.Map as M

--newtype SRT = SRT (Map String Dynamic)
--That was the culprit! newtype /= data at runtime

--Unexpected complication: return has type 
--forall (m :: * -> *) . a -> m a,
--and ANY can't mimic that type.
--My ANY needs to be poly-kinded.

$(remotable ['(+),'True,'show,'return,'(>>=),'(>>),'getLine,'putStrLn,
            'nil,'(:),'if_then_else,'unit,'map, '(==)] 
                [[t| Num Int |],[t| Show Integer |]
                               ,[t| Monad IO |], [t| Eq Integer |],
                [t| Eq ([] Char) |]])

deriving instance Typeable Show

remoteTable = __RemoteTable initRemoteTable

ma :: M.Map String Dynamic
ma = unsafeCoerce remoteTable

setup = setupt remoteTable 

pluspoly :: Typeable a => Tree ((D Num (Num a)) -> a -> a -> a)
pluspoly = stat "GHC.Num.+:poly"
intdict = stat "D:AppT (ConT GHC.Num.Num) (ConT GHC.Types.Int)" 
          :: Tree (D Num (Num Int))

example :: Tree (IO String) 
example = $(mkTree [| return "OK!" |])