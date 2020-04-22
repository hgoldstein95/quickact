{-# LANGUAGE PartialTypeSignatures #-}

module BSTSpec where

import Criterion (nfAppIO, benchmark)
import Control.Monad (replicateM)
import qualified Data.List as L
import qualified Data.Map as M

import HT (ccomb, combCheck, pairSpec, Spec(..))
import Term hiding (nil)
import Test.QuickCheck

import BST

-- invariant properties
prop_ArbitraryValid :: BST Int Int -> Bool
prop_ArbitraryValid = valid

prop_InsertValid :: ((Int, Int), BST Int Int) -> Bool
prop_InsertValid ((k, v), t) = valid (insert k v t)

-- postcondition properties
prop_InsertPost :: (((Int, Int), BST Int Int), Int) -> Bool
prop_InsertPost (((k, v), t), k') =
  find k' (insert k v t) ==
  if k == k'
    then Just v
    else find k' t

prop_FindPostPresent :: ((Int, Int), BST Int Int) -> Bool
prop_FindPostPresent ((k, v), t) = find k (insert k v t) == Just v

prop_FindPostAbsent :: (Int, BST Int Int) -> Bool
prop_FindPostAbsent (k, t) = find k (delete k t) == Nothing

-- metamorphic properties
prop_SizeInsert :: ((Int, Int), BST Int Int) -> Bool
prop_SizeInsert ((k, v), t) = size (insert k v t) >= size t

(=~=)
  :: (Eq k, Eq v, Show k, Show v)
  => BST k v -> BST k v -> Bool
t1 =~= t2 = toList t1 == toList t2

prop_InsertInsert :: ((((Int, Int), Int), Int), BST Int Int) -> Bool
prop_InsertInsert ((((k, v), k'), v'), t) =
  insert k v (insert k' v' t) =~=
  if k == k'
    then insert k v t
    else insert k' v' (insert k v t)

-- Model based properties
deleteKey
  :: Eq k
  => k -> [(k, v)] -> [(k, v)]
deleteKey k = filter ((/= k) . fst)

prop_InsertModel :: ((Int, Int), BST Int Int) -> Bool
prop_InsertModel ((k, v), t) =
  toList (insert k v t) == L.insert (k, v) (deleteKey k $ toList t)

genInt :: Gen Int
genInt = elements [-100, -1, 0, 1, 100]

intSpec :: Spec Int
intSpec =
  Spec
  { specH =
      M.fromList [("Int", [(show n, []) | n <- [-100, -1, 0, 1, 100] :: [Int]])]
  , specTy = "Int"
  , specFromTerm = \(Term n []) -> read n
  , specToTerm = \n -> Term (show n) []
  , specGen = genInt
  }

genBST :: Gen (BST Int Int)
genBST = do
  kvs <- (,) <$> genInt <*> ((,) <$> genInt <*> genInt)
  pure $ foldr (uncurry insert) nil kvs

bstFromTerm :: Term -> BST Int Int
bstFromTerm (Term "Leaf" []) = Leaf
bstFromTerm (Term "Branch" [l, k, v, r]) =
  Branch
    (bstFromTerm l)
    (specFromTerm intSpec k)
    (specFromTerm intSpec v)
    (bstFromTerm r)
bstFromTerm _ = error "bad term"

bstToTerm :: BST Int Int -> Term
bstToTerm Leaf = Term "Leaf" []
bstToTerm (Branch l k v r) =
  Term
    "Branch"
    [bstToTerm l, specToTerm intSpec k, specToTerm intSpec v, bstToTerm r]

bstSpec :: Spec (BST Int Int)
bstSpec =
  Spec
  { specH =
      M.fromList
        [("BST", [("Leaf", []), ("Branch", ["BST", "Int", "Int", "BST"])])] `M.union`
      specH intSpec
  , specTy = "BST"
  , specFromTerm = bstFromTerm
  , specToTerm = bstToTerm
  , specGen = genBST
  }

data TestSet a = TestSet
  { tsTests :: [a]
  , tsThrownAway :: Int
  }

data Experiment a = Experiment
  { eName :: String
  , eTests :: [TestSet a]
  }

instance Show (Experiment a) where
  show e =
    "Experiment ⟨" ++
    eName e ++
    "⟩\n\tAverage Test Suite Size = " ++ show (avgSize :: Double) ++
    "\n\tAverage Tests Thrown Away = " ++ show (avgTrashed :: Double)
    where
      ntests = fromIntegral $ length (eTests e)
      avgSize = sum (map (fromIntegral . length . tsTests) $ eTests e) / ntests
      avgTrashed = sum (map (fromIntegral . tsThrownAway) $ eTests e) / ntests


data ExperimentResult = ExperimentResult
  { erName :: String
  , erTotalTestSets :: Int
  , erAvgTestsPerSet :: Double
  , erAvgFailuresPerSet :: Double
  }

instance Show ExperimentResult where
  show er =
    "Name\t\t\t\t\t\t\t\t\t\t\t" ++
    erName er ++
    "\n" ++
    "Total Test Sets\t\t\t\t\t\t" ++
    show (erTotalTestSets er) ++
    "\n" ++
    "Avg. Tests Per Set\t\t\t\t" ++
    show (erAvgTestsPerSet er) ++
    "\n" ++
    "Avg. Failures Per Set\t\t\t" ++
    show (erAvgFailuresPerSet er) ++
    "\n" ++
    "Expected Tests to Failure\t" ++
    expTTF ++
    "\n"
    where expTTF = if erAvgFailuresPerSet er == 0
            then "X"
            else show $ (erAvgTestsPerSet er + 1) / (erAvgFailuresPerSet er + 1)

runExperiment :: (a -> Bool) -> Experiment a -> ExperimentResult
runExperiment prop Experiment {eName = name, eTests = ts} =
  ExperimentResult
  { erName = name
  , erTotalTestSets = numSets
  , erAvgTestsPerSet =
      fromIntegral (sum (map (length . tsTests) ts)) / fromIntegral numSets
  , erAvgFailuresPerSet = fromIntegral (sum countFails) / fromIntegral numSets
  }
  where
    numSets = length ts
    countFails =
      [length $ filter (not . prop) testSet | testSet <- tsTests <$> ts]

randomTestSet :: Gen a -> IO (TestSet a)
randomTestSet g = do
  tests <- generate $ replicateM 10000 g
  pure $ TestSet tests 0

combinatorialTestSet :: Ord a => Spec a -> Int -> IO (TestSet a)
combinatorialTestSet spec n = do
  (tests, ta) <- generate $ ccomb spec n
  pure $ TestSet tests ta

randomExperiment :: String -> Gen a -> IO (Experiment a)
randomExperiment name g = do
  testSets <- replicateM 30 (randomTestSet g)
  pure $ Experiment name testSets

combinatorialExperiment :: Ord a => String -> Spec a -> Int -> IO (Experiment a)
combinatorialExperiment name spec n = do
  testSets <- replicateM 30 (combinatorialTestSet spec n)
  pure $ Experiment name testSets

executeExperiment :: (a -> Bool) -> Experiment a -> IO ()
executeExperiment prop e =
  putStrLn . showResult $ runExperiment prop e
  -- if result == Nothing
  --   then putStrLn "T"
  --   else pure ()
  where
    -- secs = 300
    -- time = secs * 1000000
    showResult er =
      let expTTF = if erAvgFailuresPerSet er == 0
                   then "X"
                   else show $ erAvgTestsPerSet er / erAvgFailuresPerSet er
      in erName er ++ "|" ++ expTTF

pairGen :: Gen a -> Gen b -> Gen (a, b)
pairGen x y = (,) <$> x <*> y

experiments :: IO ()
experiments = do
  -- -- r_ib <- randomExperiment "" (genInt `pairGen` genBST)
  -- c2_ib <- combinatorialExperiment "c2ib" (intSpec `pairSpec` bstSpec) 2
  -- -- c3_ib <- combinatorialExperiment "" (intSpec `pairSpec` bstSpec) 3

  -- -- r_iib <- randomExperiment "" (genInt `pairGen` genInt `pairGen` genBST)
  -- c2_iib <- combinatorialExperiment "c2iib" (intSpec `pairSpec` intSpec `pairSpec` bstSpec) 2
  -- -- c3_iib <- combinatorialExperiment "" (intSpec `pairSpec` intSpec `pairSpec` bstSpec) 3

  -- -- r_iiiib <- randomExperiment "" (genInt `pairGen` genInt `pairGen` genInt `pairGen` genInt `pairGen` genBST)
  -- c2_iiiib <- combinatorialExperiment "c2iiiib" (intSpec `pairSpec` intSpec `pairSpec` intSpec `pairSpec` intSpec `pairSpec` bstSpec) 2
  -- -- c3_iiiib <- combinatorialExperiment "" (intSpec `pairSpec` intSpec `pairSpec` intSpec `pairSpec` intSpec `pairSpec` bstSpec) 3

  -- -- r_iibi <- randomExperiment "" (genInt `pairGen` genInt `pairGen` genBST `pairGen` genInt)
  -- c2_iibi <- combinatorialExperiment "c2iibi" (intSpec `pairSpec` intSpec `pairSpec` bstSpec `pairSpec` intSpec) 2
  -- -- c3_iibi <- combinatorialExperiment "" (intSpec `pairSpec` intSpec `pairSpec` bstSpec `pairSpec` intSpec) 3

  -- print c2_ib
  -- print c2_iib
  -- print c2_iiiib
  -- print c2_iibi

  benchmark $ nfAppIO generate (ccomb (intSpec `pairSpec` intSpec `pairSpec` bstSpec) 5)

  -- let singleExperiment_ib prop name = do
  --       executeExperiment prop (r_ib { eName = name ++ ", Random" })
  --       executeExperiment prop (c2_ib { eName = name ++ ", Combinatorial (t = 2)" })
  --       -- executeExperiment prop (c3_ib { eName = name ++ ", Combinatorial (t = 3)" })

  -- let singleExperiment_iib prop name = do
  --       executeExperiment prop (r_iib { eName = name ++ ", Random" })
  --       executeExperiment prop (c2_iib { eName = name ++ ", Combinatorial (t = 2)" })
  --       -- executeExperiment prop (c3_iib { eName = name ++ ", Combinatorial (t = 3)" })

  -- let singleExperiment_iiiib prop name = do
  --       executeExperiment prop (r_iiiib { eName = name ++ ", Random" })
  --       executeExperiment prop (c2_iiiib { eName = name ++ ", Combinatorial (t = 2)" })
  --       -- executeExperiment prop (c3_iiiib { eName = name ++ ", Combinatorial (t = 3)" })

  -- let singleExperiment_iibi prop name = do
  --       executeExperiment prop (r_iibi { eName = name ++ ", Random" })
  --       executeExperiment prop (c2_iibi { eName = name ++ ", Combinatorial (t = 2)" })
  --       -- executeExperiment prop (c3_iibi { eName = name ++ ", Combinatorial (t = 3)" })

  -- singleExperiment_iib prop_InsertValid "Insert Valid"
  -- singleExperiment_iibi prop_InsertPost "Insert Post"
  -- singleExperiment_iib prop_FindPostPresent "Find Post Present"
  -- singleExperiment_ib prop_FindPostAbsent "Find Post Absent"
  -- singleExperiment_iib prop_SizeInsert "Size Insert"
  -- singleExperiment_iiiib prop_InsertInsert "Insert Insert"
  -- singleExperiment_iib prop_InsertModel "Insert Model"

  -- putStrLn "---- END ----"
