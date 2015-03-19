{-# LANGUAGE StandaloneDeriving, ScopedTypeVariables, DeriveDataTypeable,
TemplateHaskell, PolyKinds, KindSignatures #-}
module Remotable where

import Tree
import RTD
import Var

import ProcessUtil --just for debugging

import Data.Binary
import Data.Rank1Typeable
import qualified Data.ByteString.Lazy as L
import Unsafe.Coerce
import Control.Distributed.Process
import Control.Distributed.Static
import qualified Control.Distributed.Process.Closure as C
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (showName)
import Data.Maybe (fromJust)
import Control.Applicative ((<$>),(<*>))
import Control.Monad (mapM)
import Data.Char (isUpper)
import Data.Generics (everywhereM, mkM, gmapM) --used in functions from Closure
import qualified Data.Map --for use only in TH Exps
import qualified Data.Rank1Dynamic --for use only in TH
import Data.Typeable.Internal (tyConModule,tyConName)
import qualified Data.Set as S
import Data.List (union,isPrefixOf)
--import qualified Data.Typeable (splitTyConApp)
--Just using mkTyCon to convert Type (known at compile time) to TypeRep
--(known at runtime) and then showing it. This gives each dict
--a unique string. Problem: show does not differentiate between A.T
--and B.T. Need to use my own showTypeRep, showType.
--underlyingTypeRep
--Data.Typeable.Internal.TypeRep.tyConModule


--TODO: Remove all instances of shout, unsafePerformIO


import System.IO.Unsafe --for debugging
--move this to another module later, it's for testing
deriving instance Typeable Monad
deriving instance Typeable Eq

instance RuntimeLookup Eq where
    runtimeLookup = hlookup $
                    (D::E ()) :*
                    (D::E Bool) :*
                    (D::E Char) :*
                    (D::E Int) :*
                    (D::E Integer) :*
                    (D::E (Tree ANY)) :*

                    ((\D -> D)::E ANY -> E [ANY]) :*
                    ((\D -> D)::E ANY -> E (Maybe ANY)) :*
                    
                    ((\D D -> D) :: E ANY -> E ANY1 -> E (Either ANY ANY1)) :*
                    ((\D D -> D) :: E ANY -> E ANY1 -> E ((,) ANY ANY1)) :*
                    One
type E a = D Eq (Eq a)                    
runtimeEquals :: TypeRep -> ANY -> ANY -> Maybe Bool
runtimeEquals tr a b = do 
  dict :: D Eq ANY <- runtimeLookup dictType
  return $ withDictEquals (unsafeCoerce dict) a b
    where 
      dictType = fromJust $ 
                 matchT (typeOf (undefined::ANY)) tr 
                 (typeOf (undefined::E ANY)) 
      withDictEquals :: E ANY -> ANY -> ANY -> Bool
      withDictEquals D = (==)

--The types that can be decoded at runtime.
instance RuntimeLookup Binary where
    runtimeLookup = hlookup $
                    (D::B ()) :*
                    (D::B Bool) :*
                    (D::B Char) :*
                    (D::B Int) :*
                    (D::B Integer) :*
                    (D::B (Tree ANY)) :*

                    ((\D->D)::C1 []) :*
                    ((\D->D)::C1 Maybe) :*

                    ((\D D -> D)::C2 Either) :*
                    ((\D D -> D)::C2 (,)) :*
                    One

type B a = D Binary (Binary a)
--types of conversions for simple containers (tuples,lists,either etc.) 
--whose Binary instances look like (Binary a .. Binary z) => 
--Binary (container a .. z):
type C1 f = B ANY -> B (f ANY)
type C2 f = B ANY -> B ANY1 -> B (f ANY ANY1)
type C3 f = B ANY -> B ANY1 -> B ANY2 -> B (f ANY ANY1 ANY2)
type C4 f = B ANY -> B ANY1 -> B ANY2 -> B ANY3 -> 
    B (f ANY ANY1 ANY2 ANY3) 
type C5 f = B ANY -> B ANY1 -> B ANY2 -> B ANY3 -> B ANY4 ->
    B (f ANY ANY1 ANY2 ANY3 ANY4) 
deriving instance Typeable Binary
runtimeDecode :: TypeRep ->L.ByteString -> Maybe ANY
runtimeDecode tr bs = do
  dict :: D Binary ANY <- runtimeLookup dictType
  return $ withDictDecode (unsafeCoerce dict) bs
    where 
      dictType = fromJust $ 
                 matchT (typeOf (undefined::ANY)) tr 
                 (typeOf (undefined::B ANY)) 
      withDictDecode :: B ANY -> L.ByteString -> ANY
      withDictDecode D = decode
testRuntimeDecode :: (Typeable a, Binary a) => a -> Maybe a
testRuntimeDecode x = unsafeCoerce $ runtimeDecode (typeOf x) (encode x)

eval :: Tree a -> Process (Maybe a)
eval (Tree utt) = unsafeCoerce $ eval' utt
eval' :: UntypedTree -> Process (Maybe ANY)
eval' (Constant tr bs) = return $ runtimeDecode tr bs
eval' (Stat tr "compVs:") = --yell "This succeeded!" >> 
                            return $ Just $ unsafeCoerce $ \c body x->
                  
                  let mbool = runtimeEquals tr c x in
                      case mbool of 
                        Nothing -> 
                            error $
                            "The type " ++ show tr ++ " is not supported by " ++
                            "RuntimeLookup Eq; an Eq dict for it " ++ 
                            "cannot be looked up at runtime."
                        Just b -> 
                            if b 
                            then (body :: ANY)
                            else error "Match vs constant failed!"
eval' (Stat _ "comb:S") = return $ Just combinator_s
eval' (Stat _ "comb:K") = return $ Just combinator_k
eval' (Stat _ "comb:I") = return $ Just combinator_i
eval' (Apply utf utx) = do --yell $ "Evaluating: " ++ show utf
                           mf <- eval' utf 
                           --case mf of Nothing -> 
                            --           yell "mf failed!"
                             --         _ -> yell "mf succeeded!"
                           --yell $ "Evaluating: " ++ show utx
                           mx <- eval' utx
                           --case mx of Nothing -> 
                            --           yell "mx failed!"
                             --         _ -> yell "mx succeeded!"
                           return $ (unsafeCoerce mf) <*> mx              
eval' (Stat _ str) = do v <- unStatic (staticLabel str :: Static ANY)
                        return $ Just v
eval' (V _ v) = unsafeCoerce $ do
                     (tr,bs) <- readVarUntyped v
                     return $ runtimeDecode tr bs
eval' (TV _ tv) = unsafeCoerce $ do 
                   (tr,bs) <- readVarUntyped tv
                   let typeOfTree = fromJust $ 
                                    matchT (typeOf(undefined::ANY)) tr 
                                  (typeOf(undefined::Tree ANY))
                       maybeTree = unsafeCoerce $ runtimeDecode typeOfTree bs
                                 :: Maybe (Tree ANY)
                   case maybeTree of 
                     Nothing -> return Nothing
                     Just (Tree utt) -> eval' utt
{-eval' (Lam (Stat _ "_") body) = do me <- eval' body
                                   return $ 
                                          do e <- me
                                             return $ unsafeCoerce 
                                                        ((\_ -> e)::ANY->ANY)
eval' (Lam c@(Constant tr _) body) = do 
         mebody <- eval' body
         mec <- eval' c
         return $ 
                unsafeCoerce $ do ec <- mec
                                  ebody <- mebody
                                  return (\v -> 
                                       if fromJust 
                                              (runtimeEquals tr
                                                             v
                                                             ec)
                                       then ebody
                                       else error "Match vs constant failed!")-}
--The delayed computation of the body presents a problem: when we 
--return the function we no longer have access to the node.
--I see two possible ways around it: being naughty 
--(saving the remoteTable or 
--using unsafePerformIO to access the node in a pure context), 
--or using SKI combinators. I choose the latter.
eval' (Lam ps body) = do let f = foldr useSKI body ps
                         --yell "THE SKI'd UTT:"
                         --yell f
                         eval' f

useSKI :: UntypedTree -> UntypedTree -> UntypedTree
useSKI (Stat _ varName) s@(Stat tr str) | str == varName = 
                                            comb_iTree
useSKI v@(Stat _ _) (Apply utf utx) = comb_sTree `Apply`
                                      (useSKI v utf) `Apply`
                                      (useSKI v utx)
useSKI v@(Stat _ str) (Lam ps body) | any (\p -> case p of
                                                   Stat _ s ->
                                                       s == str
                                                   _ -> False) ps
                                        = comb_kTree `Apply`
                                          foldr useSKI body ps
                                    | otherwise = 
                                        --variable name str may 
                                        --occur in body
                                        useSKI v $ foldr useSKI body ps
useSKI c@(Constant tr _) body = compVsConstantTree tr `Apply`
                                c `Apply`
                                body
useSKI _ body = comb_kTree `Apply` body                   
      
comb_sTree = Stat undefined "comb:S"
comb_kTree = Stat undefined "comb:K"
comb_iTree = Stat undefined "comb:I"
--those TypeReps are ignored by eval'
--anyway
compVsConstantTree  tr = Stat tr "compVs:" 
--This is rather naughty: I'm hiding the TypeRep of the constant
--compVs will compare against in the Stat itself.

combinator_s = unsafeCoerce (\f g x -> (f x) (g x)) :: ANY
combinator_k = unsafeCoerce const :: ANY
combinator_i = unsafeCoerce id :: ANY
      
remotable :: [Name] -> [TypeQ] -> Q [Dec]
remotable ns tqs = do 
  ts <- sequence tqs
  ns'vs <- mapM forName ns
  ds'vs <- mapM forType ts
  makeRemoteTable (ns'vs ++ ds'vs)
--for each name, if it is polymorphic f ::(C1 a,C2 b...) => f:
--insert "f.poly" ((\D D ... -> f) :: D C1 (C1 a) ... -> f)
--instead.
--Otherwise continue as normal.
--for each constraint t@(C a b::Type), insert 
--"Dict "++show t d@(D :: D C (C a b)).

forName :: Name -> Q (String,ExpQ)
forName n = do 
  (origName,typ) <- getName'Type n
  return $ --if isAdHocPolymorphic typ 
           --then 
               (showName n, -- ++":poly"
                 toDictPolymorphicDynExp typ origName)
           --else (showName n, toDynExp typ origName)

toDynExp :: Type -> Name -> ExpQ
toDynExp typ n = do 
  let (typVars, typ') = case typ of 
                          ForallT vars [] mono -> (vars, mono)
                          _                    -> ([], typ)
  let dyn = case typVars of
                  [] -> [| shadowDynamic $(nameE n) |]
                  _  -> [| shadowDynamic ($(nameE n) :: 
                         $(monomorphize typVars typ)) |]
  dyn
toDictPolymorphicDynExp :: Type -> Name -> ExpQ
toDictPolymorphicDynExp typ n = 
  [| shadowDynamic $(sigE mkPolyExp mkPolyType) |]    
      where
        ps = preds typ
        dictPat = [p| D |] :: PatQ
        --tyvars = tyVarsOf typ
        mkPolyExp = 
               lamE (replicate (length ps) dictPat) (nameE n)
        --makes a monomorphic type where all constraints
        --are reified: Show a -> a -> String
        --becomes      D Show (Show ANY) -> ANY -> String
        mkPolyType = --do t <- forallT tyvars (return []) --EDIT
                             -- $ 
                           do  t <- mkPolyType' typ ps
                               ForallT tyvars _ t' <- addTypeableConstraints t
                               --I don't want any foralls left, so I move
                               --them up to the top with addTypeableConstraints
                               --and then remove them.
                               --shout t'
                               --yell t'
                               t'' <- monomorphize tyvars t' 
                               --yell "Monomorphized: "
                               --shout t''
                               return t''
--Incorrect monorphization was because I passed in the wrong tyvars.
--Now it monomorphizes away all type variables, but it still doesn't
--handle monads.
--possible bug here: does monomorphize pass over cxt?

--mkPolyType' may need to lift all internal forall's to top level
--(I thought Haskell did this automatically, 
--but return has type forall (m :: * -> *) . Monad m => 
--                    forall a . a -> m a).
--An alternative solution is for the functions which 
--add typeable constraints to map through the whole type.
--(I will pursue this approach). 
mkPolyType' :: Type -> [(Name,[Type])] -> TypeQ
mkPolyType' typ ps = case tyvars'Preds'Type typ of 
                       (tyvars,_,_)  ->
                           ForallT tyvars [] <$> mkPolyType'' typ ps
mkPolyType'' typ [] = case tyvars'Preds'Type typ of 
                        (_,_,t) -> return t
mkPolyType'' typ ((className,args):ps) = 
      [t| D $(conT className) $(mkConstraint className args) ->
            $(mkPolyType'' typ ps)
      |]
mkConstraint cl args = return $ 
                         foldr (\arg cstr -> AppT cstr arg)
                               (ConT cl)
                               args

tyVarsOf (ForallT tvs _ _) = tvs

nameE :: Name -> ExpQ
nameE n | (\c -> c == ':' || isUpper c) $ head $ nameBase n = 
              conE n
          | otherwise = varE n
        
--isAdHocPolymorphic :: Type -> Bool
--isAdHocPolymorphic typ = preds typ /= []
preds :: Type -> [(Name,[Type])]
preds typ = 
    case typ of 
      ForallT _ cs _ -> map (\(ClassP n ts) -> (n,ts)) cs
      --Hope EqualP isn't used for anything...
      _ -> []
forType :: Type -> Q (String,ExpQ)
forType typ = return $ ("D:"++showType typ,[| shadowDynamic
                                          (D :: D $className $(return typ)) |])
              where className = conT $ classNameOf typ
                    classNameOf (ConT n) = n
                    classNameOf (AppT typ _) = classNameOf typ

makeRemoteTable :: [(String,ExpQ)] -> Q [Dec]
makeRemoteTable str'exps = do
    --e <- mkRemoteTableExp ---------------------------------- DEBUG
    --(unsafePerformIO $ writeFile "Log.txt" (show $ ppr e) --
    --                     >> return (return ())) ------------
    sequence [sigD rtable [t| RemoteTable -> RemoteTable |]
             , sfnD rtable mkRemoteTableExp]
              where rtable = mkName "__RemoteTable"
                    mkRemoteTableExp = [| registerStatics
                                        $(mkKVPairs str'exps)
                                        |]
                    mkKVPairs [] = [| [] |]
                    mkKVPairs ((str,exp):str'exps) = 
                        [| ($(stringE str),$exp) : $(mkKVPairs str'exps) |]
registerStatics [] rtable = rtable
registerStatics ((s,dyn):s'dyns) rtable = 
    registerStatic s dyn $ registerStatics s'dyns rtable
                        

mkTree :: ExpQ -> ExpQ
mkTree eq = do e <- eq
               --yell "THE UNSIMPLIFIED TREE!"
               --yell e
       	       e' <- simplifyExp e
               --yell "THE SIMPLIFIED TREE!"
               --yell e'
               --yell "AND NOW THE TREE:"
       	       --t <- 
               mkTree' e'
               --shout t
               --return t
mkTree' :: Exp -> ExpQ
mkTree' lit@(LitE _) = [| constant $(return lit) |]
mkTree' (VarE n) | "V:" `isPrefixOf` nameBase n = 
                     varE $ mkName $ -- ++ "body:"
                          drop 2 $ 
                               nameBase n
                     --indicates it is a variable
                     --[| stat $(stringE $ nameBase n) |]
                 | otherwise = handleNamedE n
mkTree' (ConE n) = handleNamedE n
mkTree' (AppE f x) = [| $(mkTree' f) $$ $(mkTree' x) |]
mkTree' (SigE x t) = [| $(mkTree' x) :: $tree_t |]
                     where tree_t = do let (tyvs,ps,typ) = tyvars'Preds'Type t
                                       tree <- [t| Tree |]
                                       if null tyvs && null ps 
                                       then
                                           return (AppT tree typ)
                                       else
                                           return $ 
                                              ForallT tyvs ps (AppT tree typ)
mkTree' (LamE ps body) = do
  --pass in exp to ensure name is captured?
  --if you see V:x, make it vx
  let bodyTree = mkTree' body
  foldr patCombine bodyTree --removed lambdaBody constructor here 
            ps
    where
      {-patToTree WildP = [| stat "_" |]
      patToTree (VarP n) = [| stat $(stringE $ nameBase n) |]
                           --n really shouldn't have a module prefix,
                           --but better safe than sorry
      patToTree (LitP l) = mkTree (litE l)
      patToTree (ConP n []) = [| constant $(conE n) |]
                              --possibly a 'gotcha'
                              --because e.g. True is normally
                              --treated as a name, not a constant.-}
      patCombine pat bodyTreeQ = 
          case pat of 
            WildP -> [| lam (stat "_") $bodyTreeQ |]
            LitP l -> [| lam (constant $(litE l)) $bodyTreeQ |]
            VarP n ->  (lamE [varP n]  
                        [| lam $(varE n) $bodyTreeQ |])
                       `appE`
                       [| stat $(stringE $ nameBase n) |]
          --problem: let is too polymorphic!
          --solution: use a lambda instead
                           
          --Problem: \x -> x treats x like a normal name.
          --Do I need to add 'treat as variable' set to
          --mkTree'?
          --Nah, just tag it as a variable:
          --apply $(mkTree [| variable |])
          -- \x ... -> x = 
          --fail if x is repeated in pats? No need,
          --haskell does that for us
          --let x = stat "x" in
          --lam x (body)
          --Maybe I need to mark variables in simplifyExp?
          --Problem: types are ambiguous due to making new
          --stats V:n, I need to declare vn = V:n
          --has same type as pat: 
          --solution: 
          --(=:=) :: a -> a -> a
          --(=:=) = const
          --guess I need to make vn capturable,
          --no problem
          -- \x -> x ===> let vx = stat "V:x" in
          --                 Lam vx vx
          --yay! nested lambdas work right b.c.
          --of scoping rules.
mkTree' t = do yell "Non-exhaustive:"
               shout t
               error "Non-exhaustive error"

--Found the non-exhaustive mystery LetE bug:
--simplifyExp recursively call mkTree on (>>=),
--thus generating a let x = ... in \D -> x.
--It should simply put in a [| (>>=) |]
               

tyvars'Preds'Type :: Type -> ([TyVarBndr],Cxt,Type)
tyvars'Preds'Type (ForallT tyvs ps typ) = (tyvs,ps,typ)
tyvars'Preds'Type t = ([],[],t)
--When generating type for mkTree, ALWAYS propagate the foralls up/
--replace them. Nested foralls do not typecheck/makes the 
--type more ambiguous.
--Do I need type info from sigs to propagate all the way down?

shout t = unsafePerformIO (print (ppr t) 
                           >> return (return ()))
yell t = unsafePerformIO (putStrLn (show t)
                          >> return (return ()))
--addTypeableConstraints goes through the entire type
--and in all forall (a1,a2...) . cs => t, it adds the constraints
--(Typeable a1, Typeable a2 ...).
--It should also lift those constraints to the top:
--(forall a . Typeable a => a -> ()) is not Typeable (since
--we don't know a). forall a1 . c1 => forall a2 . c2 => t
--should hopefully be replaceable with forall a1 a2 . (c1,c2) => t
--in mkTree.
--For convenience, always returns a forall (even for monomorphic types).
addTypeableConstraints :: Type -> TypeQ
addTypeableConstraints (ForallT tvs ps typ) = do
  ForallT tvs' ps' typ' <- addTypeableConstraints typ 
               --bubble up the tvs and ps
  forallT (union tvs tvs') 
              ((union ps ps' `union`) <$> typeableReqs tvs) (return typ')
            where
              typeableReq (PlainTV n) = 
                  classP ''Typeable [varT n]
              typeableReq (KindedTV n k) = 
                  classP ''Typeable [sigT (varT n) k]
              typeableReqs = mapM typeableReq
addTypeableConstraints (AppT t1 t2) = do 
    ForallT tvs1 ps1 t1' <- addTypeableConstraints t1
    ForallT tvs2 ps2 t2' <- addTypeableConstraints t2
    forallT (union tvs1 tvs2) (return $ union ps1 ps2) $
            return $ AppT t1' t2'
    
addTypeableConstraints t = return $ ForallT [] [] t



handleNamedE :: Name -> ExpQ
handleNamedE n = do (origName,typ) <- getName'Type n
       	     	    --if isAdHocPolymorphic typ
		     	--then 
                    let ps = preds typ
                        expq = 
                            [| stat 
                               $(stringE $ show origName) ::
			           $(do  
                                      t <- mkPolyType' typ ps
                                      tree <- [t| Tree |]
                                      ForallT tvs ps typ <- 
                                          addTypeableConstraints t
                                      --shout (ForallT tvs ps 
                                      --           $ AppT tree typ)
                                      return $ ForallT tvs ps 
                                                 $ AppT tree typ
                                        )
                                      |]
                                 
			     in [| let x = $expq
                                   in  
                                   $(polyTree typ ps ps [| x |] origName) |]
                        --All values can be treated in the same way
                        
			--else [| stat $(stringE $ show origName) ::
			    -- 	Tree $(return typ) |] 
			where
                        polyTree :: Type -> [(Name,[Type])] -> 
                                    [(Name,[Type])] -> ExpQ -> Name -> 
                                    ExpQ
			polyTree typ [] ps expq origName = expq
                           
			polyTree typ (_:xs) ps expq origName = do
				 [| $(polyTree typ xs ps expq 
                                      origName) $$ dict |]
                        --It complains when I try $(mkTree[| return |]):
                        --illegal kind signature '* -> *'. It worked
                        --before, so that's weird. Maybe bc
                        --I lifted foralls?
                        --removing kind signatures from type variables
                        --in constraint. 
                        --This makes it ambiguous in situations when
                        --kind matters, but oh well. I'll solve that
                        --with a kind setter function or smth:
                        {-remKSigsConstraint :: Cxt -> Cxt
                        remKSigsConstraint = map remKSigsPred
                        remKSigsPred :: Pred -> Pred
                        remKSigsPred (ClassP n ts) = ClassP n $ 
                            map remKSigsType ts
                        remKSigsType (SigT t ksig) = remKSigsType t
                        remKSigsType (AppT _ _) = undefined-}

simplifyExp :: Exp -> ExpQ
simplifyExp (AppE f x) = appE (simplifyExp f) (simplifyExp x)
simplifyExp (InfixE (Just x) f Nothing) = appE (simplifyExp f) (simplifyExp x) 
simplifyExp (InfixE Nothing f (Just x)) = do n <- newName "v"
	    	    	      	    	     e <- lamE [varP n] $
                                                     simplifyExp f `appE`
                                                     varE n `appE`
                                                     simplifyExp x
                                             simplifyExp e
                                                                 
                                             --derp, solution: simplify lambda
                                             --recursively
simplifyExp (InfixE (Just x) f (Just y)) = simplifyExp f `appE`
                                           simplifyExp x `appE`
                                           simplifyExp y
simplifyExp (UInfixE x f y) = simplifyExp (InfixE (Just x) f (Just y))
simplifyExp (CondE cond t e) = [| if_then_else |] `appE`
                               simplifyExp cond `appE`
                               simplifyExp t `appE`
                               simplifyExp e
simplifyExp (DoE [NoBindS e]) = simplifyExp e
simplifyExp (DoE ((NoBindS e):stmts)) = [| (>>) |] `appE`
                                        simplifyExp e `appE`
                                        simplifyExp (DoE stmts)
simplifyExp (DoE ((BindS p e):stmts)) = [| (>>=) |] `appE` 
                                        (simplifyExp e) `appE`
                                        (simplifyExp $ LamE [p] 
                                        (DoE stmts))
                                        --bug manifesting as
                                        --s not in scope for
                                        --do s <- getLine; putStrLn s
                                        --was due to not marking variables
                                        --for special treatment
                                        --in this lambda.
simplifyExp comp@(CompE _) = [| requireIsAList $(simplifyExp comp) |]
simplifyExp (ListE es) = do let seqs = map simplifyExp es
                            handleList seqs
                            where
                              handleList [] = [| nil |]
                              handleList (seq:seqs) =  [| (:) |] `appE`
                                                       seq `appE`  
                                                       (handleList seqs)
simplifyExp (SigE e t) = sigE (simplifyExp e) (return t)
simplifyExp (LamE ps body) = lamE (map return ps) (markVariables ps <$> 
                                                   simplifyExp  body)
    where
      --collects all variables, 
      --then replaces all matching names N in the lambda body
      --with V:N 
      markVariables :: [Pat] -> Exp -> Exp
      markVariables = markVariables' . S.unions . map getVarsOfP
      markVariables' :: S.Set Name -> Exp -> Exp
      markVariables' s (VarE n) | S.member n s = markedAsVariable n 
                                | otherwise = VarE n
      markVariables' s (AppE f x) = AppE 
                                    (markVariables' s f)
                                    (markVariables' s x)
      markVariables' s v@(ConE _) = v
      markVariables' s l@(LitE _) = l
      markVariables' s (LamE ps body) = LamE ps $ markVariables' s body
      markVariables' s (SigE exp sig) = SigE (markVariables' s exp) sig
     -- markVarP WildP = [p| _ |]
      --markVarP c@(ConP _ []) = return c
      --markVarP (VarP n) = varP $ mkName $ ("V:"++) $ nameBase n
      markedAsVariable = VarE . mkName . ("V:"++) . nameBase
      getVarsOfP :: Pat -> S.Set Name
      getVarsOfP (VarP n) = S.singleton n
      getVarsOfP (ConP n []) = S.empty
      getVarsOfP WildP = S.empty
      getVarsOfP (LitP l) = S.empty
      getVarsOfP p = error $ 
                     "You've used a pattern outside the subset " ++
                     "allowed in mkTree: _, variables, literals " ++ 
                     "and 0-argument constructors: \n" ++ show p
      
--TODO complete this!
simplifyExp e = return e

 

requireIsAList :: Tree [a] -> Tree [a]
requireIsAList = id
---These will need to be in any remoteTable
if_then_else i t e = if i then t else e
nil = []
unit = ()
--(>>=),(>>),(:)
-------------------------------------------

dict :: (Typeable (tc::k), Typeable c) => Tree (D tc c)
dict = dict' undefined
dict' :: (Typeable (tc::k),Typeable c) => D tc c -> Tree (D tc c)
dict' (d :: D tc c) = stat ("D:"++showTypeRep cstr)
      where cstr = fromJust $ matchT
			    (typeOf (undefined :: D ANY ANY1))
      	    	   	    (typeOf d)
			    (typeOf (undefined :: ANY1))

{- Solution to circular typechecking problem:
data Treigh a = Treigh TypeRep deriving Show
dict :: Typeable a => a -> Treigh a
dict (x :: a) = treigh :: Treigh a
     where treigh = Treigh tr
     	   tr = typeOf (undefined :: a)
dic :: Typeable a => Treigh a
dic = dict undefined
-}
     	   
--Crisis! We need to access values in the RemoteTable 
--without knowing their type. Because of how fromDynamic
--is implemented, that means we must lie and say the value
--we're making dynamic is of type ANY.
--However, Dynamic is an abstract type and (understandably)
--prevents that. Therefore we have to construct a "bad" Dynamic
--using unsafeCoerce.
{-data Any
data ShadowDynamic = ShadowDynamic TypeRep Any-}
shadowDynamic :: a -> Data.Rank1Dynamic.Dynamic
shadowDynamic x = withDictToDynamic (unsafeCoerce anyTDict) x
	      
withDictToDynamic :: D Typeable (Typeable a) ->
   		   a -> Data.Rank1Dynamic.Dynamic
withDictToDynamic D = Data.Rank1Dynamic.toDynamic
anyTDict = D :: D Typeable (Typeable ANY)

{-unsafeCoerce $ ShadowDynamic 
                (typeOf (undefined::ANY))
                (unsafeCoerce x)-}

--Desired property: showTypeRep (typeOf x) ==
--                  showType (type x)
--Used for identifying Dicts:
--at compile time we know their type;
--at runtime we know their typerep
showTypeRep :: TypeRep -> String
showTypeRep tr = case splitTyConApp tr of
	       	      (tycon,ts) ->
		      		 tyConModule tycon ++
				 "." ++
				 tyConName tycon ++
				 ":" ++
				 (ts >>= showTypeRep)
				 
showType t = showsType t ""
	 where
		showsType (ConT n) = shows n . showString ":"
		showsType (AppT tf tx) = showsType tf . showsType tx

				 


--shadowDynamic is crashing ghci, maybe it's because it lacks a show 
--instance?
--instance Show ShadowDynamic where
--  showsPrec _ (ShadowDynamic t _) = 
--showString "<<" . shows t . showString ">>" 
--nope, still crashing. maybe it's because ANY /= Any?
--nope, not that either. TODO ask about the representation of
--objects at runtime.
--I managed to convert from Dynamic to ShadowDynamic, but not
--back again. I suspect the Dynamic data structure is larger,
--but I don't see why it would be.
--SOLUTION: Make spurious Typeable-dict containing the (Typeable ANY)
--instance.

--mkTree name = if name is polymorphic :: (C1 a,C2 b...) => f
--              then (Stat "name.poly" :: Tree (D C1 (C1 a) -> ... -> f) 
--                    $$ D $$ D ...
--              else (Stat name)
--mkTree (f x) = mkTree f $$ mkTree x

--Using unexported code from Control.Distributed.Process.Closure:
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Variation on 'funD' which takes a single expression to define the function
sfnD :: Name -> Q Exp -> Q Dec
sfnD n e = funD n [clause [] (normalB e) []]
-- | Compose a set of expressions
compose :: [Q Exp] -> Q Exp
compose []     = [| id |]
compose [e]    = e
compose (e:es) = [| $e . $(compose es) |]
-- | Fully qualified name; that is, the name and the _current_ module
--
-- We ignore the module part of the Name argument (which may or may not exist)
-- because we construct various names (`staticName`, `sdictName`, `tdictName`)
-- and those names certainly won't have Module components.
showFQN :: Name -> Q Exp
showFQN n = do
  loc <- location
  stringE (loc_module loc ++ "." ++ nameBase n)
-- | Look up the "original name" (module:name) and type of a top-level function
getName'Type :: Name -> Q (Name, Type)
getName'Type name = do
  info <- reify name
  case info of
    VarI origName typ _ _ -> return (origName, typ)
    ClassOpI origName typ _ _ -> return (origName, typ)
    DataConI origName typ _ _ -> return (origName, typ)
    _                     -> fail $ show name ++ " not found"
-- | Turn a polymorphic type into a monomorphic type using ANY and co
monomorphize :: [TyVarBndr] -> Type -> Q Type
monomorphize tvs =
    let subst = zip (map tyVarBndrName'Kind tvs) anys
    in everywhereM (mkM (applySubst subst))
  where
    anys :: [Q Type]
    anys = map typVar (iterate succ zero)

    typVar :: Q Type -> Q Type
    typVar t = [t| TypVar $t |]

    zero :: Q Type
    zero = [t| Zero |]

    succ :: Q Type -> Q Type
    succ t = [t| Succ $t |]

    applySubst :: [((Name,Kind), Q Type)] -> Type -> Q Type
    applySubst s (VarT n) =
      case lookupByName n s of
        Nothing -> return (VarT n)
        Just (k,t)  -> sigT t k
    applySubst s t = gmapM (mkM (applySubst s)) t
    lookupByName n = lookup n . map (\((name,kind),qt) -> (name,(kind,qt)))

--It would appear my problems with monads
--(let dreturn :: D Monad Monad ANY -> ANY1 -> ANY ANY1;
--     dreturn = \D -> return
--gives: couldn't match kind k with *,
--       could not deduce Monad m0)
--can be solved by adding kind signatures to each any:
-- dreturn :: D Monad Monad (ANY :: * -> *) -> (ANY1 :: *) 
--                       -> (ANY :: * -> *) -> (ANY ... ANY1 ...)       

-- | The name of a type variable binding occurrence
tyVarBndrName'Kind :: TyVarBndr -> (Name,Kind)
tyVarBndrName'Kind (PlainTV n)    = (n,StarT)
tyVarBndrName'Kind (KindedTV n k) = (n,k)


