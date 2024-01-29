module Check where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except

import Data.Bifunctor (first, bimap)
import Data.Map (Map)
import qualified Data.Map as Map

import ObjTT.Abs
import ObjTT.Print ( Print, printTree )

type Sig = Map Ident Type
type Cxt = [(Ident,Type)]

data Env = Env
  { envSig :: Sig
  , envCxt :: Cxt
  }

data TypeError
  = UnboundVariable Ident
  | UnboundIdentifier Ident
  | TypeMismatch Type Type
  deriving Show

type Index = Int

newtype Abs a = Abs { unAbs :: a }
  deriving (Eq, Show)

data Type
  = Id Type Term Term
  | Pi Type (Abs Type)
  | Univ
  | El Term
  deriving (Eq, Show)

data Term
  = Var Index
  | Def Ident
  | Refl Type Term
  | IdRec Type (Abs (Abs (Abs Type))) Term Term Term (Abs Term)
  | IdConv Type (Abs (Abs (Abs Type))) Term (Abs Term)
  | Lam Type (Abs Type) (Abs Term)
  | App Type (Abs Type) Term Term
  | BetaConv Type (Abs Type) Term (Abs Term)
  deriving (Eq, Show)

type M = ReaderT Env (Except TypeError)

runChecker :: M a -> Either TypeError a
runChecker m = runExcept (runReaderT m emptyEnv)

checkDecls :: [Decl] -> M ()
checkDecls = \case
  [] -> return ()
  (d:ds) -> do
    (x,t) <- checkDecl d
    addSignature x t $ checkDecls ds

checkDecl :: Decl -> M (Ident, Type)
checkDecl = \case
  DAxiom x e -> do
    t <- checkType e
    return (x, t)

checkType :: Exp -> M Type
checkType = \case
  EUniv -> return Univ
  EEl t -> do
    v <- checkExp t Univ
    return $ El v
  EId a b -> do
    (v, t) <- inferExp a
    w <- checkExp b t
    return $ Id t v w
  EPi x a b -> do
    ta <- checkType a
    tb <- addContext x ta $ checkType b
    return $ Pi ta (Abs tb)

checkExp :: Exp -> Type -> M Term
checkExp e t = do
  (v, t') <- inferExp e
  case t' == t of
    True  -> return v
    False -> throwError $ TypeMismatch t' t

inferExp :: Exp -> M (Term, Type)
inferExp = \case
  EVar x -> (first Var <$> lookupCxt x)
    `catchError` \case
      UnboundVariable _ -> lookupSig x
      err -> throwError err
  ERefl a -> do
    (v, t) <- inferExp a
    return (Refl t v, Id t v v)
  EIdRec x y u c p z d -> do
    (vp, t) <- inferExp p
    case t of
      Id ta va vb -> do
        tc <- Abs . Abs . Abs <$> do
          addContext x ta $ addContext y ta $ addContext u (Id ta (Var 1) (Var 0)) $ checkType c
        vd <- addContext z ta $ checkExp d $ substType3 (Var 0) (Var 0) (Refl ta (Var 0)) tc
        return (IdRec ta tc va vb vp (Abs vd), substType3 va vb vp tc)
  EIdConv x y u c a z d -> do
    (va, ta) <- inferExp a
    tc <- Abs . Abs . Abs <$> do
      addContext x ta $ addContext y ta $ addContext u (Id ta (Var 1) (Var 0)) $ checkType c
    vd <- Abs <$> do
      addContext z ta $ checkExp d $ substType3 (Var 0) (Var 0) (Refl ta (Var 0)) tc
    return (IdConv ta tc va vd,
            Id (substType3 va va (Refl ta va) tc)
               (IdRec ta tc va va (Refl ta va) vd)
               (substTerm1 va vd)
           )
  ELam x a e -> do
    ta <- checkType a
    (v, tb) <- addContext x ta $ inferExp e
    return (Lam ta (Abs tb) (Abs v), Pi ta (Abs tb))
  EApp f e -> do
    (v, t) <- inferExp f
    case t of
      Pi ta tb -> do
        w <- checkExp e ta
        return (App ta tb v w, substType1 w tb)
  EBetaConv a x f -> do
    (va, ta) <- inferExp a
    (vf, tb) <- bimap Abs Abs <$> do
      addContext x ta $ inferExp f
    return (BetaConv ta tb va vf,
      Id (substType1 va tb)
         (App ta tb (Lam ta tb vf) va)
         (substTerm1 va vf)
      )

emptyEnv :: Env
emptyEnv = Env
  { envSig = Map.empty
  , envCxt = []
  }

lookupCxt :: Ident -> M (Index, Type)
lookupCxt x = do
  cxt <- asks envCxt
  loop 0 cxt
  where
    loop :: Index -> Cxt -> M (Index, Type)
    loop i = \case
      [] -> throwError $ UnboundVariable x
      (y,t):cxt
        | x == y -> return (i, weakType (i+1) t)
        | otherwise -> loop (i+1) cxt

lookupSig :: Ident -> M (Term, Type)
lookupSig x = do
  sig <- asks envSig
  case Map.lookup x sig of
    Nothing -> throwError $ UnboundIdentifier x
    Just t -> return (Def x, t)

addContext :: Ident -> Type -> M a -> M a
addContext x t = local $ \ env -> env { envCxt = (x,t) : envCxt env }

addSignature :: Ident -> Type -> M a -> M a
addSignature x t = local $ \ env -> env { envSig = Map.insert x t $ envSig env }

weak :: Int -> Term -> Term
weak n = substTerm (map Var [n..])

weakType :: Int -> Type -> Type
weakType n = substType (map Var [n..])

substTerm1 :: Term -> Abs Term -> Term
substTerm1 v (Abs t) = substTerm (v : map Var [0..]) t

substType1 :: Term -> Abs Type -> Type
substType1 v (Abs t) = substType (v : map Var [0..]) t

substType3 :: Term -> Term -> Term -> Abs (Abs (Abs Type)) -> Type
substType3 va vb vc (Abs (Abs (Abs t))) = substType (va : vb : vc : map Var [0..]) t

substTerm :: [Term] -> Term -> Term
substTerm vs = \case
  Var i -> vs !! i
  Def x -> Def x
  Refl t v -> Refl (substType vs t) (substTerm vs v)
  IdRec ta tc a b p d ->
    IdRec
      (substType vs ta)
      (substAbs (substAbs (substAbs substType)) vs tc)
      (substTerm vs a)
      (substTerm vs b)
      (substTerm vs p)
      (substAbs substTerm vs d)
  IdConv ta tc a d ->
    IdConv
      (substType vs ta)
      (substAbs (substAbs (substAbs substType)) vs tc)
      (substTerm vs a)
      (substAbs substTerm vs d)
  Lam ta tb v -> Lam (substType vs ta) (substAbs substType vs tb) (substAbs substTerm vs v)
  BetaConv ta tb va vb ->
    BetaConv (substType vs ta) (substAbs substType vs tb) (substTerm vs va) (substAbs substTerm vs vb)

substType :: [Term] -> Type -> Type
substType vs = \case
  Univ -> Univ
  El v -> El $ substTerm vs v
  Id t a b -> Id (substType vs t) (substTerm vs a) (substTerm vs b)
  Pi ta tb -> Pi (substType vs ta) (substAbs substType vs tb)

substAbs :: ([Term] -> a -> a) -> [Term] -> Abs a -> Abs a
substAbs subst vs (Abs t) = Abs $ subst (liftS vs) t

liftS :: [Term] -> [Term]
liftS vs = Var 0 : map (weak 1) vs
