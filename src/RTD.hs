{-# LANGUAGE PolyKinds, GADTs, ConstraintKinds,
ScopedTypeVariables, DeriveDataTypeable,StandaloneDeriving,
TemplateHaskell, GeneralizedNewtypeDeriving,
TypeOperators, TypeFamilies, UndecidableInstances,
MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
--It is a well known fact that having many language extensions
--at the head of your file is a sign of intelligence
module RTD where
import Data.Rank1Typeable
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad (mplus, guard)
import Data.Maybe (fromJust)
import Unsafe.Coerce
--A new module for run-time fetching of typeclass dicts
--from a list of TypeReps

data D typeclass c where D :: c => D typeclass c deriving Typeable
data T k where T :: T k deriving Typeable
instance (Typeable tc,Typeable c) => Show (D tc c) where
    show d@D = show (typeOf d)
instance Typeable k => Show (T k) where
    show t@T = show (typeOf t)
--D2 stores a class dict and includes a proxy
--type variable indicating what class (Num,Binary etc.)
--it is

class RuntimeLookup tc where
    runtimeLookup :: TypeRep -> Maybe (D tc ANY)
class Conversion tc f where
    conversion :: f -> TypeRep -> Maybe (D tc ANY)
instance (Typeable tc',Typeable c,Typeable tc) => Conversion tc (D tc' c) where
    conversion (d::D tc' c) tr = do 
      matchT (typeOf d) tr (typeOf ()) 
    -- ^identical to guard $ Right() ==isInstanceOf (typeOf d) tr 
      guard $ typeOf (T::T tc') == typeOf (T::T tc) 
      return $ unsafeCoerce d 

instance (Typeable tc',Typeable c,RuntimeLookup tc',
          Conversion tc f, LastType f, Typeable f) => 
    Conversion tc ((D tc' c) -> f) where
        conversion (f :: (D tc' c) -> conversion) tr = 
            let tr' = lastType f 
                typeOfDict = typeOf (undefined :: D tc' c)
{-i.e. let tr' = tr in typeOfDict-}
            in
            do lookupType <- matchT tr' tr typeOfDict
               dict <- runtimeLookup lookupType :: Maybe (D tc' ANY)
               conversion (f $ unsafeCoerce dict) tr 
               

matchT :: TypeRep -> TypeRep -> TypeRep -> Maybe TypeRep
matchT trPat trVal res = do mp <- (execStateT (unify trPat trVal) M.empty)
                            return $ subst mp res
    where 
      subst :: (M.Map Int TypeRep) -> TypeRep -> TypeRep
      subst mp tr = 
          case splitTyConApp tr of
            (con,trs) | isAnAny con ->
                        fromJust$ M.lookup (anyId trs) mp
                      | otherwise ->
                        mkTyConApp con $ map (subst mp) trs
unify :: TypeRep -> TypeRep -> StateT (M.Map Int TypeRep) Maybe ()
unify trp trv = case splitTyConApp trp of
                  (con,trs) | isAnAny con -> 
                                insertV (anyId trs) trv
                            | otherwise -> 
                                       case splitTyConApp trv of
                                         (conv,trsv) ->
                                             do lift $ guard (conv == con)
                                                sequence_ $ 
                                                          zipWith unify trs trsv
                            where insertV k ty = 
                                      do m <- get
                                         case M.lookup k m of
                                           Nothing -> put (M.insert k ty m)
                                           Just ty' | ty == ty' ->
                                                        return ()
                                                    | otherwise ->
                                                        lift $ Nothing
                  
--known: trv does not contain ANY<n>

isAnAny = (== tyConOf (typeOf (undefined :: ANY)))
--anyId ANY = 0;anyId ANY1 = 1 etc.
anyId :: [TypeRep] -> Int
anyId [_,tr] = typeHeight tr
               where typeHeight = typeHeight' 0 
                     typeHeight' n tr = 
                         case splitTyConApp tr of
                           (_,[]) -> n
                           (_,[tr]) -> typeHeight' (n+1) tr
                                
tyConOf = fst . splitTyConApp  
                
class LastType t where
    lastType :: t -> TypeRep
instance (Typeable tc,Typeable c) => LastType (D tc c) where
    lastType = typeOf
instance LastType t => LastType (a -> t) where
    lastType f = lastType $ f undefined
    
--heterogenous list:
data a * b = a :* b
infixr 0 :*
data One = One
--hlookup :: HetList conversion -> TypeRep -> Maybe Dict tc ANY
class HLookup tc hetlist where
    hlookup :: hetlist -> TypeRep -> Maybe (D tc ANY)
instance HLookup tc One where
    hlookup One _ = Nothing
instance (Conversion tc a, HLookup tc xs) => HLookup tc (a * xs) where
    hlookup (a :* xs) tr = mplus (conversion a tr) (hlookup xs tr)

--TODO heterogenous search tree instead of list
--for O(log n) lookup of dict
--maybe caching when evaluating? 

-- Test code:
{-instance RuntimeLookup Show where
    runtimeLookup = hlookup $
                    (D::D Show (Show Int)) :*
                    (D::D Show (Show Bool)) :* 
                    ((\D->D) :: D Show (Show ANY) -> 
                                D Show (Show [ANY])) :* 
                    ((\D->D) :: D Show (Show ANY) -> 
                                D Show (Show ((Maybe ANY)))) :*
                    One
deriving instance Typeable Show
runtimeShow :: TypeRep -> Maybe (a -> String)
runtimeShow tr = do dict :: D Show ANY <- runtimeLookup tr
                    return $ unsafeCoerce withDictShow dict 
withDictShow :: D Show (Show a) -> a -> String
withDictShow D = show

testShow :: Typeable a => a -> Maybe String
testShow (x :: a) = do s <- runtimeShow (typeOf (undefined::D Show (Show a)))
                       return $ s x-}
