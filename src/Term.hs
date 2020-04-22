{-# LANGUAGE DeriveGeneric #-}
module Term where

import Data.List (intercalate)
import GHC.Generics (Generic)

data Term = Term String [Term]
  deriving (Eq, Ord, Generic)

instance Show Term where
  show (Term c []) = c
  show (Term c xs) = c ++ "(" ++ intercalate ", " (show <$> xs) ++ ")"

numRange :: [Integer]
numRange = [1 .. 100]

true :: Term
true = Term "true" []

false :: Term
false = Term "false" []

nil :: Term
nil = Term "nil" []

cons :: Term -> Term -> Term
cons a b = Term "cons" [a, b]

pair :: Term -> Term -> Term
pair a b = Term "pair" [a, b]

lt :: Term -> Term -> Term
lt (Term c1 []) (Term c2 []) =
  if (read c1 :: Integer) < read c2
    then true
    else false
lt _ _ = error "type mismatch"

partition :: Term -> Term -> Term
partition _ (Term "nil" []) = pair nil nil
partition n (Term "cons" [x, xs]) =
  let (Term "pair" [ys, zs]) = partition n xs
  in if lt x n == true
       then pair (cons x ys) zs
       else pair ys (cons x zs)
partition _ _ = error "type mismatch"

append :: Term -> Term -> Term
append (Term "nil" []) a = a
append (Term "cons" [x, xs]) a = cons x (append xs a)
append _ _ = error "type mismatch"

sort :: Term -> Term
sort (Term "nil" []) = nil
sort (Term "cons" [x, xs]) =
  let Term "pair" [ys, zs] = partition x xs
  in append (sort ys) (cons x (sort zs))
sort _ = error "type mismatch"

instance Num Term where
  a * b = Term "mul" [a, b]
  a + b = Term "add" [a, b]
  fromInteger n
    | n `elem` numRange = Term "num" [Term (show n) []]
    | otherwise = undefined
  abs = undefined
  signum = undefined
  negate = undefined

add :: Term -> Term -> Term
add (Term m []) (Term n []) =
  let x = read m + read n
  in if x `elem` numRange
       then Term (show x) []
       else error "type mismatch"
add _ _ = error "type mismatch"

mul :: Term -> Term -> Term
mul (Term m []) (Term n []) =
  let x = read m * read n
  in if x `elem` numRange
       then Term (show x) []
       else error "type mismatch"
mul _ _ = error "type mismatch"

eval :: Term -> Term
eval (Term "num" [n]) = n
eval (Term "add" [a, b]) = add (eval a) (eval b)
eval (Term "mul" [a, b]) = mul (eval a) (eval b)
eval _ = error "type mismatch"
