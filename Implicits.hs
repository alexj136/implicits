module Main where

-- Implementation of the calculus in the paper "Foundations of implicit
-- function types" - Odersky et al.

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Except

main :: IO ()
main = return ()

--------------------------------------------------------------------------------
-- SYNTAX
--------------------------------------------------------------------------------

type Name = Integer

data Term
    = EVar Name
    | IVar Name
    | Lam Name Term
    | App Term Term
    | IQuery
    | ELet Name Type Term Term
    | ILet Type Term Term
    | If Term Term Term
    | TrueLit
    | FalseLit
    deriving (Show, Eq, Ord)

data Type
    = TVar Name
    | EFun Type Type
    | IFun Type Type
    | Forall Name Type
    | TBool
    deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- TYPING
--------------------------------------------------------------------------------

type Env = M.Map Name Type

inferType :: Env -> Env -> Term -> Maybe Type
inferType explEnv implEnv term = case term of
    EVar x   -> M.lookup x explEnv
    App t t' -> do
        EFun ty1 ty2 <- inferType explEnv implEnv t
        if checkType explEnv implEnv t' ty1 then Just ty2 else Nothing
    TrueLit  -> Just TBool
    FalseLit -> Just TBool
    _        -> undefined

checkType :: Env -> Env -> Term -> Type -> Bool
checkType explEnv implEnv term ty = case term of
    Lam x t    -> case ty of
        EFun ty1 ty2 -> checkType (M.insert x ty1 explEnv) implEnv t ty2
    If tb t t' ->
        checkType explEnv implEnv tb TBool
        && checkType explEnv implEnv t  ty
        && checkType explEnv implEnv t' ty
    _          -> case ty of
        IFun ty1 ty2 -> undefined -- rule (?-> I)
        _            -> inferType explEnv implEnv term == Just ty
