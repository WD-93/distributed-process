{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, 
DeriveDataTypeable, GADTs,GeneralizedNewtypeDeriving, FlexibleInstances,
UndecidableInstances, StandaloneDeriving #-}
module Var (Var(),newVar,readVar,writeVar,killVar,readVarUntyped) where
import Data.Rank1Typeable
import Data.Binary
import Data.List
import Control.Distributed.Process
import qualified Data.ByteString.Lazy as L
import Data.Typeable.Internal (TyCon(..))
import GHC.Int (Int64)
import Control.Applicative ((<$>),(<*>))

deriving instance Typeable TypeRep

--Needs to be rewritten to conform to VarOrd anyway
--(Num a,Ord a) => VarOrd a --special: increment?
--[a] --special: concatenate, slices
--VarOrd a => VarOrd (BoundedSize a) --allows use  of a's methods
newtype Var a = Var {getSendPort :: SendPort (Interaction a)} 
    deriving (Eq,Typeable,Ord,Binary)
instance Show (Var a) where
    show _ = "<Var>"
data Interaction a = IRead (SendPort a) 
                   | IWrite (SendPort ()) a 
                   | IKill (SendPort ())
                   | IReadUntyped (SendPort (TypeRep,L.ByteString)) 
                     deriving Typeable
instance (Binary a,Typeable a) => Binary (Interaction a) where
    put (IRead sp) = putWord8 0 >> put sp
    put (IWrite sp a) = putWord8 1 >> put sp >> put a
    put (IKill sp) = putWord8 2 >> put sp --creepy constructor name lol
    put (IReadUntyped sp) = putWord8 3 >> put sp
    get = do w <- getWord8
             case w of
               0 -> get >>= return . IRead
               1 -> do sp <- get
                       a <- get
                       return $ IWrite sp a
               2 -> get >>= return . IKill
               3 -> get >>= return . IReadUntyped

class (Binary a, Typeable a) => VarOrd a where
    varGreater :: a -> a -> Bool
class (Num a,Ord a, Binary a, Typeable a) => VarOrdNumber a where
instance VarOrdNumber Rational
instance VarOrdNumber Integer
instance VarOrdNumber Double
instance VarOrdNumber Int
instance VarOrdNumber a => VarOrd a where 
    varGreater = (<) --number types individually vetted
instance (Eq a,Binary a,Typeable a) => VarOrd [a] where 
    varGreater = isPrefixOf 
instance (Binary a,VarOrd a) => VarOrd (BoundedSize a) where
    varGreater b1@(BoundedSize bound bsOld) b2@(BoundedSize bound' bsNew)
               = bound == bound' && 
                 varGreater (decodeBounded b1) (decodeBounded b2) &&
                 L.length bsNew < bound
data BoundedSize a = BoundedSize Int64 L.ByteString deriving Typeable
decodeBounded :: Binary a => BoundedSize a -> a
decodeBounded (BoundedSize _ bs) = decode bs
encodeBounded :: Binary a => Int64 -> a -> BoundedSize a
encodeBounded i = BoundedSize i . encode
instance Binary (BoundedSize a) where
    put (BoundedSize i bs) = put i >> put bs
    get = BoundedSize <$> get <*> get

newVar :: VarOrd a => a -> Process (Var a)
newVar x = do sp <- spawnChannelLocal (varProc x)
              return $ Var sp
                  where varProc x rp = 
                            do i <- receiveChan rp
                               case i of
                                 IRead sp ->
                                     sendChan sp x >> varProc x rp
                                 IWrite sp y -> 
                                     sendChan sp () >> 
                                              varProc (if varGreater x y
                                                       then y
                                                       else x) rp
                                 IKill sp -> sendChan sp ()
                                 IReadUntyped sp -> 
                                     sendChan sp (typeOf x,encode x) >>
                                     varProc x rp
                                           
readVar :: VarOrd a => Var a -> Process a
readVar (Var sendp) = do (sp,rp) <- newChan
                         sendChan sendp (IRead sp)
                         receiveChan rp 
writeVar :: VarOrd a => Var a -> a -> Process ()
writeVar (Var sendp) x = do (sp,rp) <- newChan
                            sendChan sendp (IWrite sp x)
                            receiveChan rp
killVar :: VarOrd a => Var a -> Process ()
killVar (Var sendp) = do (sp,rp) <- newChan
                         sendChan sendp (IKill sp)
                         receiveChan rp
readVarUntyped :: (Binary a,Typeable a) => Var a -> 
                  Process (TypeRep,L.ByteString)
readVarUntyped (Var sendp) = do (sp,rp) <- newChan
                                sendChan sendp (IReadUntyped sp)
                                receiveChan rp