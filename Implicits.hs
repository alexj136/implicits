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

tySub :: Name -> Type -> Type -> Type
tySub = undefined

data Env = Env
    { explicits :: M.Map Name Type
    , implicits :: M.Map Name Type
    , typeVars  :: S.Set Name
    }

insertE, insertI :: Name -> Type -> Env -> Env
insertE x t (Env expl impl vars) = Env (M.insert x t expl) impl vars
insertI x t (Env expl impl vars) = Env expl (M.insert x t impl) vars
insertV :: Name -> Env -> Env
insertV x (Env expl impl vars) = Env expl impl (S.insert x vars)

inferType :: Env -> Term -> Maybe Type
inferType env term = case term of
    -- (Var)
    EVar x -> M.lookup x (explicits env)

    -- (Query)
    IQuery -> undefined

    -- (-> E)
    App t t' -> do
        EFun ty1 ty2 <- inferType env t
        if checkType env t' ty1 then Just ty2 else Nothing

    -- (Let-Ex)
    ELet x ty t t' ->
        if checkType env t ty then inferType (insertE x ty env) t' else Nothing

    -- (Let-Im)
    ILet ty t t' ->
        if checkType env t ty then
            inferType (insertE undefined ty env) t'
        else Nothing

    TrueLit  -> Just TBool
    FalseLit -> Just TBool

    _ -> case inferType env term of
        -- (?-> E)
        Just (IFun ty1 ty2) ->
            if checkType env IQuery ty1 then Just ty2 else Nothing

        -- (V E)
        Just (Forall x ty) -> Just $ tySub x undefined ty

        _ -> undefined

checkType :: Env -> Term -> Type -> Bool
checkType env term ty = case term of
    -- (-> I)
    Lam x t -> case ty of
        EFun ty1 ty2 -> checkType (insertE x ty1 env) t ty2

    If tb t t' ->
        checkType env tb TBool
        && checkType env t  ty
        && checkType env t' ty

    _ -> case ty of
        -- (?-> I)
        IFun ty1 ty2 -> undefined

        -- (V I)
        Forall x ty  -> checkType (insertV x env) term ty

        -- (Stitch)
        _ -> inferType env term == Just ty
