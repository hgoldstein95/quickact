module HT where

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Test.QuickCheck
import Data.Universe.Helpers (choices)

import Term

type Ty = String

type Constructor = String

data Description
  = Top
  | Cons Constructor
         [Description]
  | Eventually Description
  | Next Description
  deriving (Eq, Ord)

type HT = Map Ty [(Constructor, [Ty])]

instance Show Description where
  show Top = "⊤"
  show (Cons c []) = c
  show (Cons c ts) = c ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"
  show (Eventually d) = "(⋄" ++ show d ++ ")"
  show (Next d) = "(⚬" ++ show d ++ ")"

matches :: Term -> Description -> Bool
matches _ Top = True
matches (Term c' as') (Cons c as) =
  c == c' &&
  length as == length as' && all (uncurry . flip $ matches) (zip as as')
matches (Term _ as) (Next d) = any (`matches` d) as
matches t@(Term _ as) (Eventually d) =
  t `matches` d || any (`matches` Eventually d) as

splitN :: Int -> Int -> [[Int]]
splitN _ 0 = [[]]
splitN n l = do
  x <- [0 .. n]
  xs <- splitN (n - x) (l - 1)
  pure $ x : xs

covers :: Int -> Term -> [Description]
covers 0 _ = [Top]
covers n (Term c args) =
  (covers n =<< args) ++
  [ Eventually (Cons c args')
  | ns <- splitN (n - 1) (length args)
  , args' <- choices $ uncurry covers <$> zip ns args
  ]

reachableNext :: HT -> Ty -> Set Ty
reachableNext h t = S.fromList . concatMap snd $ h M.! t

reachableEventually :: HT -> Ty -> Set Ty
reachableEventually h t = go (S.singleton t)
  where
    go :: Set Ty -> Set Ty
    go ts =
      let new = S.unions . map (reachableNext h) $ S.toList ts
          ts' = ts `S.union` new
      in if ts == ts'
           then ts
           else go ts'

-- gen :: Int -> HT -> Ty -> [Description]
-- gen n h t = Eventually <$> genC n h t

gen :: Int -> HT -> Ty -> [Description]
gen 0 _ _ = pure Top
gen n h t = [Eventually d | t' <- reach, d <- genC n h t']
  where
    reach = S.toList $ reachableEventually h t

genC :: Int -> HT -> Ty -> [Description]
genC 0 _ _ = pure Top
genC n h t = do
  (c, ts) <- cs
  ms <- splitN n' (length ts)
  Cons c <$> sequence [gen m h ty | (m, ty) <- zip ms ts]
  where
    cs = h M.! t
    n' =
      if length cs == 1
        then n
        else n - 1

data Spec a = Spec
  { specH :: HT
  , specTy :: Ty
  , specToTerm :: a -> Term
  , specFromTerm :: Term -> a
  , specGen :: Gen a
  }

pairSpec :: Spec a -> Spec b -> Spec (a, b)
pairSpec sa sb =
  Spec
  { specH =
      M.insert ty [(ty, [specTy sa, specTy sb])] $ specH sa `M.union` specH sb
  , specTy = ty
  , specToTerm = \(a, b) -> Term ty [specToTerm sa a, specToTerm sb b]
  , specFromTerm = \(Term _ [a, b]) -> (specFromTerm sa a, specFromTerm sb b)
  , specGen = (,) <$> specGen sa <*> specGen sb
  }
  where
    ty = "PAIR[" ++ specTy sa ++ "," ++ specTy sb ++ "]"

type ThrownAway = Int

ccomb :: Ord a => Spec a -> Int -> Gen ([a], Int)
ccomb spec k = do
  (es, ta) <- fst <$> genTerms (0 :: Int) (0 :: Int) (S.fromList $ gen k h ty) S.empty
  pure (S.toList es, ta)
  where
    h = specH spec
    ty = specTy spec
    genTerms ta n ds es
      | S.null ds = pure ((es, ta), 0)
      | otherwise =
      if n == 100 -- we've gone through 100 examples without adding coverage
        then pure ((es, ta), n)
        else do
          x <- specGen spec
          let t = specToTerm spec x
          if any (matches t) ds
            then genTerms ta 0 (ds S.\\ S.fromList (covers k t)) (S.insert x es)
            else genTerms (ta + 1) (n + 1) ds es

lb :: HT
lb =
  M.fromList
    [ ("L", [("cons", ["B", "L"]), ("nil", [])])
    , ("B", [("true", []), ("false", [])])
    ]

lbspec :: Spec [Bool]
lbspec =
  Spec
  { specH = lb
  , specTy = "L"
  , specFromTerm = termToBoolList
  , specToTerm = termFromBoolList
  , specGen = arbitrary
  }

termToBoolList :: Term -> [Bool]
termToBoolList (Term "nil" []) = []
termToBoolList (Term "cons" [b, l]) = termToBool b : termToBoolList l
  where
    termToBool (Term "true" []) = True
    termToBool (Term "false" []) = False
    termToBool _ = error "bad term"
termToBoolList _ = error "bad term"

termFromBoolList :: [Bool] -> Term
termFromBoolList [] = Term "nil" []
termFromBoolList (True:xs) = Term "cons" [Term "true" [], termFromBoolList xs]
termFromBoolList (False:xs) = Term "cons" [Term "false" [], termFromBoolList xs]

data Expr
  = Add Expr
        Expr
  | Mul Expr
        Expr
  | One
  | Two
  | Three

instance Arbitrary Expr where
  arbitrary =
    oneof
      [ Add <$> arbitrary <*> arbitrary
      , Mul <$> arbitrary <*> arbitrary
      , pure One
      , pure Two
      , pure Three
      ]

instance Show Expr where
  show (Add e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
  show (Mul e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++ ")"
  show One = "1"
  show Two = "2"
  show Three = "3"

expr :: HT
expr =
  M.fromList
    [ ( "E"
      , [ ("add", ["E", "E"])
        , ("mul", ["E", "E"])
        , ("one", [])
        , ("two", [])
        , ("three", [])
        ])
    ]

termFromExpr :: Expr -> Term
termFromExpr (Add e1 e2) = Term "add" [termFromExpr e1, termFromExpr e2]
termFromExpr (Mul e1 e2) = Term "mul" [termFromExpr e1, termFromExpr e2]
termFromExpr One = Term "one" []
termFromExpr Two = Term "two" []
termFromExpr Three = Term "three" []

termToExpr :: Term -> Expr
termToExpr (Term "add" [t1, t2]) = Add (termToExpr t1) (termToExpr t2)
termToExpr (Term "mul" [t1, t2]) = Mul (termToExpr t1) (termToExpr t2)
termToExpr (Term "one" []) = One
termToExpr (Term "two" []) = Two
termToExpr (Term "three" []) = Three
termToExpr _ = error "bad term"

exprspec :: Spec Expr
exprspec =
  Spec
  { specH = expr
  , specTy = "E"
  , specFromTerm = termToExpr
  , specToTerm = termFromExpr
  , specGen = arbitrary
  }

combCheck :: Ord a => Spec a -> Int -> (a -> Bool) -> IO ()
combCheck spec t prop = do
  (tests, _) <- generate $ ccomb spec t
  mapM_ (quickCheck . prop) tests
