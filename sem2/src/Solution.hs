module Solution where

import Types

----- utils -----
nat = Right Nat
bool = Right Bool

----- environment -----
type Env = [(Symbol, Type)]

extend :: (Symbol, Type) -> Env -> Env
extend var env = var : env

----- main -----
typeOf :: Term -> Either String Type
typeOf t = typeOf' t []

typeOf' :: Term -> Env -> Either String Type
typeOf' (Sym v) env = case lookup v env of
    Just t -> Right t
    Nothing -> Left $ "var" ++ show v ++ "not in scope"
typeOf' (Lam v ty t) env = case typeOf' t (extend (v, ty) env) of
    Right rty -> Right $ Fun ty rty
    Left err -> Left err
typeOf' (App t1 t2) env = case typeOf' t1 env of
    Right (Fun ty rty)
        | typeOf' t2 env == Right ty -> Right rty
        | otherwise -> Left "Type mismatch in Application"
    _ -> Left "Application without function"

typeOf' (Natural n) _ = nat
typeOf' (Add t1 t2) env
    | typeOf' t1 env == nat && typeOf' t2 env == nat = nat
    | otherwise = Left "Nat -> Nat -> Nat"
typeOf' (Mult t1 t2) env = typeOf' (Add t1 t2) env

typeOf' (Boolean b) _ = bool
typeOf' (Not t) env
    | typeOf' t env == bool = bool
    | otherwise = Left "Not :: Bool -> Bool"
typeOf' (And t1 t2) env
    | typeOf' t1 env == bool && typeOf' t2 env == bool = bool
    | otherwise = Left "Bool -> Bool -> Bool"
typeOf' (Or t1 t2) env = typeOf' (And t1 t2) env
typeOf' (Iff t1 t2 t3) env
    | typeOf' t1 env == bool && typeOf' t2 env == typeOf' t3 env = bool
    | otherwise = Left "Iff :: Bool -> Term -> Term -> Bool"

typeOf' (Pair t1 t2) env = case (typeOf' t1 env, typeOf' t2 env) of
    (Right ty1, Right ty2) -> Right $ PairT ty1 ty2
    (_, _) -> Left "Type error in Pair"
typeOf' (Fst t) env = case typeOf' t env of
    Right (PairT ty1 ty2) -> Right ty1
    Left err -> Left err
typeOf' (Snd t) env = case typeOf' t env of
    Right (PairT ty1 ty2) -> Right ty2
    Left err -> Left err

typeOf' (Nil ty) _ = Right $ List ty
typeOf' (IsNil t) env = case typeOf' t env of
    Right (List _) -> bool
    _ -> Left "IsNil :: List -> Bool"
typeOf' (Head t) env = case typeOf' t env of
    Right (List ty) -> Right ty
    Left err -> Left err
typeOf' (Tail t) env = case typeOf' t env of
    Right (List ty) -> Right $ List ty
    Left err -> Left err
typeOf' (Cons t1 t2) env = case (typeOf' t1 env, typeOf' t2 env) of
    (Right ty1, Right (List ty2))
        | ty1 == ty2 -> Right $ List ty1
        | otherwise -> Left "Type mismatch in List"
    (_, _) -> Left "Invalid list construction"

-- > typeOf $ Lam "x" Nat $ Add (Sym "x") (Natural 5)
-- Right (Fun Nat Nat)

-- > typeOf $ Lam "x" Bool $ Sym "x"
-- Right (Fun Bool Bool)

-- > typeOf $ Add (Natural 5) (Boolean False)
-- Left "..."

-- > typeOf $ App (Lam "x" Nat $ Sym "x") (Natural 5)
-- Right Nat

-- > typeOf $ App (Lam "x" Bool $ Boolean False) (Natural 5)
-- Left "..."

-- > typeOf $ Nil Nat
-- Right (List Nat)

-- > typeOf $ Cons (Natural 5) $ Cons (Boolean False) $ Nil Nat
-- Left "..."