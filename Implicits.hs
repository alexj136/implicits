module Main where

-- Implementation of the calculus in the paper "Foundations of implicit
-- function types" - Odersky et al. We omit the Forall type here for simplicity.

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State

main :: IO ()
main = return ()

--------------------------------------------------------------------------------
-- SYNTAX
--------------------------------------------------------------------------------

type Name = Integer

data Term
    = EVar Name
    | Lam Name Term
    | App Term Term
    | ELet Name Type Term Term
    | If Term Term Term
    | TrueLit
    | FalseLit
    | IVar Name
    | ILet Type Term Term
    | IQuery
    deriving (Show, Eq, Ord)

data Type
    = EFun Type Type
    | IFun Type Type
    | TBool
    deriving (Show, Eq, Ord)

data PTerm
    = PVar Name
    | PLam Name PTerm
    | PApp PTerm PTerm
    | PLet Name PTerm PTerm
    | PIf PTerm PTerm PTerm
    | PTrueLit
    | PFalseLit
    deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- TYPING
--------------------------------------------------------------------------------

data Env = Env
    { explicits :: M.Map Name Type
    , implicits :: M.Map Name Type
    } deriving (Show, Eq, Ord)

emptyEnv :: Env
emptyEnv = Env M.empty M.empty

envInsertExplicit :: Name -> Type -> Env -> Env
envInsertExplicit x t (Env expl impl) = Env (M.insert x t expl) impl

envInsertImplicit :: Name -> Type -> Env -> Env
envInsertImplicit y t (Env expl impl) = Env expl (M.insert y t impl)

fresh :: StateT Name Maybe Name
fresh = state $ \s -> (s, s + 1)

inferType :: Env -> Term -> StateT Name Maybe (Type, PTerm)
inferType env term = case term of
    -- (Var)
    EVar x -> do
        ty <- lift $ M.lookup x (explicits env)
        return (ty, PVar x)

    -- (Query)
    IQuery -> error "not implemented"

    -- (-> E)
    App t1 t2 -> do
        (tyT1, t1Trans) <- inferType env t1
        case tyT1 of
            EFun tyA tyB -> do
                t2Trans <- checkType env t2 tyA
                return (tyB, PApp t1Trans t2Trans)
            _ -> lift Nothing

    -- (Let-Ex)
    ELet x ty t1 t2 -> do
        tTrans <- checkType env t1 ty
        (tyT2, t2Trans) <- inferType (envInsertExplicit x ty env) t2
        return $ (tyT2, PLet x tTrans t2Trans)

    -- (Let-Im)
    ILet ty t1 t2 -> do
        y <- fresh
        tTrans <- checkType env t1 ty
        (tyT2, t2Trans) <- inferType (envInsertImplicit y ty env) t2
        return $ (tyT2, PLet y tTrans t2Trans)

    TrueLit  -> return (TBool, PTrueLit )
    FalseLit -> return (TBool, PFalseLit)

    -- (?-> E)
    _ -> error "not implemented"

checkType :: Env -> Term -> Type -> StateT Name Maybe PTerm
checkType env term ty = case term of
    -- (-> I)
    Lam x t -> case ty of
        EFun ty1 ty2 -> do
            tTrans <- checkType (envInsertExplicit x ty1 env) t ty2
            return $ PLam x tTrans
        _ -> error "Lam checkType not given EFun"

    If gd tb fb -> do
        gdTrans <- checkType env gd TBool
        tbTrans <- checkType env tb ty
        fbTrans <- checkType env fb ty
        return $ PIf gdTrans tbTrans fbTrans

    _ -> case ty of
        -- (?-> I)
        IFun ty1 ty2 -> do
            y <- fresh
            trans <- checkType (envInsertImplicit y ty1 env) term ty2
            return $ PLam y trans

        -- (Stitch)
        _ -> do
            (inferredTy, trans) <- inferType env term
            if inferredTy == ty then return trans else lift Nothing
