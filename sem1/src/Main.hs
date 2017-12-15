module Main where

import Data.Unique
import System.IO.Unsafe (unsafePerformIO)

----- types -----
newtype Symbol = Symbol { unSymbol :: String } deriving (Eq,Show,Read)

data TermS = SymS Symbol        -- x
           | LamS Symbol TermS  -- \x -> t
           | AppS TermS TermS   -- t1 t2
           deriving (Eq,Show,Read)

data TermI = SymI Int
           | LamI TermI
           | AppI TermI TermI
           deriving (Eq,Show,Read)

data TermP = TermP TermS
           -- (4)
           | Natural Int
           | Plus TermP TermP
           | Mult TermP TermP
           -- (5*) +50%
           | Y TermP
           -- (5**) +50%
           -- mutually recursive
           -- (6)
           | Pair TermP TermP
           | Fst TermP
           | Snd TermP
           deriving (Eq,Show,Read)

----- utils -----
sym x = SymS (Symbol x)
lam x t = LamS (Symbol x) t
app t1 t2 = AppS t1 t2

----- alpha-conversion -----
alpha :: TermS -> TermS
alpha (SymS s) = SymS s
alpha (LamS s t) =
    let new = unsafePerformIO (getUniqueSymbol s)
    in LamS new (substitute s new (alpha t))
alpha (AppS t1 t2) = AppS (alpha t1) (alpha t2)

substitute :: Symbol -> Symbol -> TermS -> TermS
substitute old new (SymS s)
    | s == old = SymS new
    | otherwise = SymS s
substitute old new (LamS s t) = LamS s (substitute old new t)
substitute old new (AppS t1 t2) = AppS (substitute old new t1) (substitute old new t2)

getUniqueSymbol :: Symbol -> IO Symbol
getUniqueSymbol (Symbol s) = do
    u <- newUnique
    return (Symbol (s ++ show (hashUnique u)))

----- beta-reduction -----
beta :: TermS -> Maybe TermS
beta t =
    let res = beta' t
    in if res == t then Nothing else Just res

beta' :: TermS -> TermS
beta' (SymS s) = SymS s
beta' (LamS s t) = LamS s (beta' t)
beta' (AppS (LamS s t) t2) = replace s t t2
beta' (AppS (AppS t0 t1) t2) = AppS (beta' (AppS t0 t1)) (beta' t2)
beta' (AppS (SymS s) t2) = AppS (SymS s) (beta' t2)

replace :: Symbol -> TermS -> TermS -> TermS
replace old (SymS s) new
    | s == old = new
    | otherwise = SymS s
replace old (LamS s t) new = LamS s (replace old t new)
replace old (AppS t1 t2) new = AppS (replace old t1 new) (replace old t2 new) 

----- interpretation -----
toTermS :: TermP -> TermS
toTermS (TermP termS) = termS
toTermS (Natural n) = lam "s" $ lam "z" $ numberToTermS n
toTermS (Plus t1 t2) = app 
    (app (lam "x" $ lam "y" $ lam "s" $ lam "z" $ app 
    (app (sym "x") (sym "s")) (app (app (sym "y") (sym "s")) (sym "z")))
    (toTermS t1))
    (toTermS t2)
toTermS (Mult t1 t2) = app 
    (app (lam "x" $ lam "y" $ lam "s" $ lam "z" $ app
    (app (sym "x") (app (sym "y") (sym "s"))) (sym "z"))
    (toTermS t1))
    (toTermS t2)
toTermS (Pair t1 t2) = app
    (app (lam "f" $ lam "s" $ lam "b" $ app (app (sym "b") (sym "f")) (sym "s"))
    (toTermS t1)) (toTermS t2)
toTermS (Fst t) = app
    (lam "p" $ app (sym "p") (lam "t" $ lam "f" $ sym "t")) (toTermS t)
toTermS (Snd t) = app
    (lam "p" $ app (sym "p") (lam "t" $ lam "f" $ sym "f")) (toTermS t)
toTermS (Y t) = app
    (lam "f" $ app inner inner)
    (toTermS t)
    where inner = lam "x" $ app (sym "f") (lam "y" $ app (app (sym "x") (sym "x")) (sym "y"))

numberToTermS :: Int -> TermS
numberToTermS n
    | n == 0 = sym "z"
    | otherwise = app (sym "s") (numberToTermS (n-1))

----- definition of factorial -----
-- sample run: solve $ TermP $ app (toTermS $ Y $ TermP $ g) (toTermS $ Natural 3)
factorial = lam "fac" $ lam "n" $ iif
    (isZero $ sym "n")
    (toTermS $ Natural 1)
    (toTermS $ Mult (TermP $ sym "n") (TermP $ app (sym "fac") (pred' (sym "n"))))

pred' d = app (lam "n" $ lam "s" $ lam "z" $ app
    (app
    (app (sym "n") (lam "g" $ lam "h" $ app (sym "h") (app (sym "g") (sym "s"))))
    (lam "u" $ sym "z"))
    (lam "u" $ sym "u")) (d)

iif b x y = app (app (app
    (lam "b" $ lam "x" $ lam "y" $ app (app (sym "b") (sym "x")) (sym "y"))
    (b)) (x)) (y)

isZero n = app (lam "n" $ app
    (app (sym "n") (lam "x" $ lam "t" $ lam "f" $ sym "f"))
    (lam "t" $ lam "f" $ sym "t")) (n)

----- main -----
full :: (TermS -> a) -> (a -> Maybe a) -> TermS -> a
full a b term = lastUnf 10000 b (a term)
  where lastUnf :: Int -> (a -> Maybe a) -> a -> a
        lastUnf 0 _ x = x
        lastUnf n f x = case f x of
          Nothing -> x
          Just y -> lastUnf (n-1) f y

solve :: TermP -> Either TermI TermS
solve = Right . full id (beta . alpha) . toTermS

main :: IO ()
main = do
  s <- read <$> getLine
  print $ solve s