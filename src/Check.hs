module Check where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except

import Data.Bifunctor (first)
import Data.Map (Map)
import qualified Data.Map as Map

import ObjTT.Abs   ( Decl )
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

type Type = Term

type Index = Int

newtype Abs a = Abs { unAbs :: a }

data Term
  = Var Index
  | Def Ident
  | Id Type Term Term
  | Refl Type Term
  | IdRec Type (Abs (Abs (Abs Type)))) Term Term Term (Abs Term)
  | IdConv Type (Abs (Abs (Abs Type)))) Term (Abs Term)
  | Pi Type (Abs Type)
  | Lam Type (Abs Type) (Abs Term)
  | App Type (Abs Type) Term Term
  | BetaConv Type (Abs Type) Term (Abs Term)
  | Univ
  | El Term
  | Type
  deriving (Eq, Show)

type M = ReaderT Env (Except TypeError)

checkExp :: Exp -> Type -> M Term
checkExp e t = do
  (v, t') <- inferExp e
  case t' == t of
    True  -> return v
    False -> throwError $ TypeMismatch t' t

inferExp :: Exp -> M (Term, Type)
inferExp = \case
  EVar x -> first Var <$> lookupCxt x
    `catchError` \case
      UnboundVariable _ -> lookupSig x
      err -> throwError err
  EUniv -> return (Univ, Type)
  EEl t -> do
    v <- checkExp t Univ
    return (El v, Type)
  EId a b -> do
    (v, t) <- inferExp a
    w <- checkExp b t
    return $ Id t v w
  ERefl a -> do
    (v, t) <- inferExp a
    return $ Refl t v
  EPi a x b -> _


lookupCxt :: Ident -> M (Index, Type)
lookupCxt x = do
  cxt <- asks envCxt
  loop 0 cxt
  where
    loop :: Index -> Ident -> M (Index, Type)
    loop i = \case
      [] -> throwError $ UnboundVariable x
      (y,t):cxt
        | x == y -> return (i, weak i t)
        | otherwise -> loop (i+1) cxt

lookupSig :: Ident -> M (Term, Type)
lookupSig x = do
  sig <- asks envSig
  case Map.lookup x sig of
    Nothing -> throwError $ UnboundIdentifier x
    Just t -> return (Def x, t)

weak :: Int -> Term -> Term
weak = _
