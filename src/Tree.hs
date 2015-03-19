{-# LANGUAGE ScopedTypeVariables,StandaloneDeriving, DeriveDataTypeable,
GeneralizedNewtypeDeriving, TypeOperators,GADTs,ConstraintKinds, 
MultiParamTypeClasses, PolyKinds, KindSignatures,TemplateHaskell #-}
module Tree where
import Data.Rank1Typeable
import Data.Binary
import Data.Binary.Put
import Data.ByteString.Lazy
--import Control.Distributed.Static
import Var
import Unsafe.Coerce

import Control.Applicative
import Control.Monad (msum,mplus)
import Data.Maybe
import Language.Haskell.TH
import System.IO.Unsafe


newtype Tree a = Tree {unTree :: UntypedTree} deriving (Eq, Show, Typeable)
constant :: (Typeable a, Binary a) => a -> Tree a
constant a = Tree $ Constant (typeOf a) (encode a)
apply :: Tree (a->b) -> Tree a -> Tree b
apply (Tree t1) (Tree t2) = Tree $ Apply t1 t2
($$) = apply
stat :: Typeable a => String -> Tree a
stat s = tree 
         where typerep = typeOf (typegetter tree)
               typegetter :: Tree a -> a
               typegetter = undefined
               tree = (Tree $ Stat typerep s) :: Tree a
var (v :: Var a) = Tree $ V (typeOf (undefined :: a)) (unsafeCoerce v)
tvar (v :: Var (Tree a)) = 
    Tree $ TV (typeOf (undefined :: a)) (unsafeCoerce v) :: Tree a
lam :: Tree a -> Tree b -> Tree (a->b)
lam (Tree p) (Tree (Lam ps body)) = Tree $ Lam (p:ps) body
lam (Tree p) (Tree body) = Tree $ Lam [p] body
--lambdaBody :: Tree a -> Tree a
--lambdaBody (Tree uttbody) = Tree $ LambdaBody uttbody
data UntypedTree = Constant {trep :: TypeRep,bs :: ByteString}
                 | Apply UntypedTree UntypedTree                  
                 | Stat {trep :: TypeRep,str :: String}
                 | V {trep :: TypeRep,getVar :: (Var UnknownType)}
                 | TV {trep :: TypeRep,getTreeVar :: (Var (Tree UnknownType))}
                 --The newest constructors! These are required to 
                 --implement lambdas.
                 | Lam [UntypedTree] UntypedTree
                 -- | LambdaBody UntypedTree --signals end of lambda:
                 -- \x y -> z ===> Lam x (Lam y (LambdaBody z))
                 --The wildcard pattern becomes: stat "_"
                 --Any other string than "_" is treated as a variable.
                 --Literal patterns become: constant lit
                   deriving (Eq, Ord,Show, Typeable)
data UnknownType = UnknownType 
                   --Compiler needs at least one constructor
                   --to derive Eq
                   deriving (Eq, Typeable)
instance Binary UnknownType where put = undefined;get = undefined
deriving instance Binary (Tree a)
instance Binary UntypedTree where
    put (Constant tr b) = putWord8 0 >> put tr >> put b
    put (Apply utf utx) = putWord8 1 >> put utf >> put utx
    put (Stat tr s) = putWord8 2 >> put tr >> put s
    put (V tr v) = putWord8 3 >> put tr >> put v
    put (TV tr v) = putWord8 4 >> put tr >> put v
    put (Lam ps body) = putWord8 5 >> put ps >> put body
    --put (LambdaBody utt) = putWord8 6 >> put utt
    get = do w <- getWord8
             case w of
               0 -> do tr <- get
                       b <- get 
                       return $ Constant tr b
               1 -> do utf <- get
                       utx <- get
                       return $ Apply utf utx
               2 -> do tr <- get 
                       s <- get
                       return $ Stat tr s
               3 -> do tr <- get
                       v <- get
                       return $ V tr v
               4 -> do tr <- get 
                       v <- get 
                       return $ TV tr v
               5 -> Lam <$> get <*> get
               --6 -> LambdaBody <$> get


getTypeOfUT :: UntypedTree -> TypeRep
getTypeOfUT (Apply f _) = rhs where
    (_,[_,rhs]) = splitTyConApp $ getTypeOfUT f
getTypeOfUT t = trep t
    --exploits rule '(_ -> a) _ ~ a' given a well-typed expression 

--the class of representations of trees.
--to be used for extracting typed subtrees
--from a tree '(Tree t)' via pattern matching
--on 'analyze t'
analyze :: Analyze b => Tree a -> Maybe b
analyze = analyze' . unTree
class Analyze a where 
    analyze' :: UntypedTree -> Maybe a
instance Typeable a => Analyze (Tree a) where
    analyze' t = maybeTree 
                where typeOft = getTypeOfUT t
                      maybeTree = if typeOfMaybeTree == typeOft
                                  then Just (Tree t)
                                  else Nothing
                      typeOfMaybeTree = typeOf ((undefined :: 
                                                 Maybe (Tree a) -> a) maybeTree)
data a :$ b = a :$ b --typed Apply
instance (Analyze f,Analyze x) => Analyze (f :$ x) where
    analyze' (Apply utf utx) = do f <- analyze' utf
                                  x <- analyze' utx
                                  return $ f :$ x
instance Applicative Tree where
    (<*>) (Tree t1) (Tree t2) = Tree $ Apply t1 t2 
    pure = undefined --can't get Typeable constraint
instance Functor Tree where
    fmap = undefined --Again, can't get typeable

instance Ord TypeRep where
    compare t1 t2 = compare (encode t1) (encode t2)