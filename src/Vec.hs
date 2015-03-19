{-# LANGUAGE ExistentialQuantification, GADTs,DeriveDataTypeable, FlexibleContexts, UndecidableInstances #-}
module Vec where
import Data.Typeable
import Data.Binary
data Vec r a where
    Vec :: [(r,a)]->Vec r a
    Scalar :: r -> Vec r a deriving Typeable
unVec (Vec xs) = xs
instance Binary (r,a) => Binary (Vec r a) where
    put (Vec xs) = put xs
    get = do xs <- get 
             return (Vec xs)
instance (Show r,Show a) => Show (Vec r a) where
    show (Vec []) = "0"
    show (Vec xs) = 
                (map (\(r,a) -> show r ++ "*" ++ show a) ==>
                (foldr1 (\s string -> s ++ " + " ++ string))) xs
instance (Num r,Ord a,Eq a) => Num (Vec r a) where
    (+) = vecWise (+) 
    (*) (Vec []) _ = Vec []
    (*) (Scalar r) (Vec xs) = Vec $ mapFst (*r) xs
    (*) (Scalar r) (Scalar r2) = Scalar $ r*r2
    (*) (Vec _) (Vec _) = error "Only multiply vectors with scalars"
    (*) a b = b * a
    (-) = vecWise (-)
    abs = undefined
    signum = undefined
    fromInteger 0 = Vec []
    fromInteger n = Scalar $ fromInteger n
instance (Ord r,Num r,Ord a,Eq a) => Ord (Vec r a) where
    compare v w = checkLTGT $ map fst (unVec $ vecWise compare v w) 
                  where
                        checkLTGT [] = EQ
                        checkLTGT (x:xs) = checkLTGT' x xs
                        checkLTGT' lge [] = lge
                        checkLTGT' EQ (x:xs) = checkLTGT' x xs
                        checkLTGT' lg (EQ:xs) = checkLTGT' lg xs
                        checkLTGT' lg (x:xs) | lg == x = checkLTGT' lg xs
                                             | otherwise = EQ
instance (Eq r,Eq a) => Eq (Vec r a) where
    (Vec xs) == (Vec ys) = xs == ys
--all ((==True).fst) $ unVec $ vecWise (==) a b
vec x = Vec [(1,x)]
(==>) f g = g . f

--assume x op 0 = x? 
vecWise :: (Num r,Ord a,Eq a) => (r -> r -> q) -> Vec r a -> Vec r a -> Vec q a
vecWise op (Vec xs) (Vec ys) = Vec $ vecWise' op xs ys
vecWise' op [] xs = mapFst (op 0) xs
vecWise' op xs [] = mapFst (`op` 0) xs
vecWise' op ((r,a):xs) ((r2,b):ys)
    | a == b = (op r r2,a):vecWise' op xs ys
    | a > b = (op 0 r2,b):vecWise' op ((r,a):xs) ys
    | a < b = (op r 0,a):vecWise' op xs ((r2,b):ys) 
mapFst f = map (\(a,b) -> (f a,b))

