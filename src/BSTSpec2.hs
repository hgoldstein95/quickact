module BSTSpec2 where

import Control.Applicative
import Control.Monad (replicateM, when)
import Data.Function
import qualified Data.List as L
import qualified Data.Map as M
import Term hiding (nil)

import HT (ccomb, pairSpec, Spec(..))
-- import Data.Maybe
import Test.QuickCheck

import BST8

newtype Key2 =
  Key Int
  deriving (Eq, Ord, Show)

type Key = Int

type Val = Int

type Tree = BST Key Val

instance Arbitrary Key2 where
  arbitrary = do
    NonNegative n <- scale (`div` 2) arbitrary
    return $ Key n
  shrink (Key k) = Key <$> shrink k

-- invariant properties
prop_ArbitraryValid :: Tree -> Bool
prop_ArbitraryValid = valid

prop_NilValid :: Bool
prop_NilValid = valid (nil :: Tree)

type KVT = ((Key, Val), Tree)

type KVTK = (((Key, Val), Tree), Key)

type KT = (Key, Tree)

type TT = (Tree, Tree)

type TTT = ((Tree, Tree), Tree)

type TTK = ((Tree, Tree), Key)

type KVKVT = ((((Key, Val), Key), Val), Tree)

type KVTT = (((Key, Val), Tree), Tree)

type KKT = ((Key, Key), Tree)

prop_InsertValid :: KVT -> Bool
prop_InsertValid ((k, v), t) = valid (insert k v t)

prop_DeleteValid :: KT -> Bool
prop_DeleteValid (k, t) = valid (delete k t)

prop_UnionValid :: TT -> Bool
prop_UnionValid (t, t') = valid (union t t')

-- postcondition properties
prop_InsertPost :: KVTK -> Bool
prop_InsertPost (((k, v), t), k') =
  find k' (insert k v t) ==
  if k == k'
    then Just v
    else find k' t

prop_DeletePost :: KKT -> Bool
prop_DeletePost ((k, k'), t) =
  find k' (delete k t) ==
  if k == k'
    then Nothing
    else find k' t

prop_FindPostPresent :: KVT -> Bool
prop_FindPostPresent ((k, v), t) = find k (insert k v t) == Just v

prop_FindPostAbsent :: KT -> Bool
prop_FindPostAbsent (k, t) = find k (delete k t) == Nothing

prop_InsertDeleteComplete :: KT -> Bool
prop_InsertDeleteComplete (k, t) =
  case find k t of
    Nothing -> t == delete k t
    Just v -> t == insert k v t

prop_UnionPost :: TTK -> Bool
prop_UnionPost ((t, t'), k) = find k (union t t') == (find k t <|> find k t')

-- metamorphic properties
prop_SizeInsert :: KVT -> Bool
prop_SizeInsert ((k, v), t) = size (insert k v t) >= size t

(=~=)
  :: (Eq k, Eq v, Show k, Show v)
  => BST k v -> BST k v -> Bool
t1 =~= t2 = toList t1 == toList t2

prop_InsertInsert :: KVKVT -> Bool
prop_InsertInsert ((((k, v), k'), v'), t) =
  insert k v (insert k' v' t) =~=
  if k == k'
    then insert k v t
    else insert k' v' (insert k v t)

prop_InsertDelete :: KVTK -> Bool
prop_InsertDelete (((k, v), t), k') =
  insert k v (delete k' t) =~=
  if k == k'
    then insert k v t
    else delete k' (insert k v t)

prop_InsertUnion :: KVTT -> Bool
prop_InsertUnion (((k, v), t), t') =
  insert k v (union t t') =~= union (insert k v t) t'

prop_DeleteNil :: Int -> Bool
prop_DeleteNil k = delete k nil == (nil :: Tree)

prop_DeleteInsert :: KVTK -> Bool
prop_DeleteInsert (((k, v'), t), k') =
  delete k (insert k' v' t) =~=
  if k == k'
    then delete k t
    else insert k' v' (delete k t)

prop_DeleteDelete :: KKT -> Bool
prop_DeleteDelete ((k, k'), t) =
  delete k (delete k' t) =~= delete k' (delete k t)

prop_DeleteUnion :: TTK -> Bool
prop_DeleteUnion ((t, t'), k) =
  delete k (union t t') =~= union (delete k t) (delete k t')

prop_UnionInsert :: KVTT -> Bool
prop_UnionInsert (((k, v), t), t') =
  union (insert k v t) t' =~= insert k v (union t t')

prop_UnionNil1 :: Tree -> Bool
prop_UnionNil1 t = union nil t == t

prop_UnionNil2 :: Tree -> Bool
prop_UnionNil2 t = union t nil == t

prop_UnionDeleteInsert :: KVTT -> Bool
prop_UnionDeleteInsert (((k, v), t), t') =
  union (delete k t) (insert k v t') =~= insert k v (union t t')

prop_UnionDeleteDelete :: TTK -> Bool
prop_UnionDeleteDelete ((t, t'), k) =
  union (delete k t) (delete k t') =~= delete k (union t t')

prop_UnionUnionIdem :: Tree -> Bool
prop_UnionUnionIdem t = union t t =~= t

prop_UnionUnionAssoc :: TTT -> Bool
prop_UnionUnionAssoc ((t1, t2), t3) =
  union (union t1 t2) t3 == union t1 (union t2 t3)

prop_FindNil :: Key -> Bool
prop_FindNil k = find k (nil :: Tree) == Nothing

prop_FindInsert :: Key -> (Key, Val) -> Tree -> Property
prop_FindInsert k (k', v') t =
  find k (insert k' v' t) ===
  if k == k'
    then Just v'
    else find k t

prop_FindDelete :: Key -> Key -> Tree -> Property
prop_FindDelete k k' t =
  find k (delete k' t) ===
  if k == k'
    then Nothing
    else find k t

prop_FindUnion :: Key -> Tree -> Tree -> Property
prop_FindUnion k t t' = find k (union t t') === (find k t <|> find k t')

-- Congruence properties
-- data Equivs k v =
--   BST k v :=~=: BST k v
--   deriving (Show)
-- instance (Arbitrary k, Arbitrary v, Ord k) =>
--          Arbitrary (Equivs k v) where
--   arbitrary = do
--     kvs <- L.nubBy ((==) `on` fst) <$> arbitrary
--     kvs' <- shuffle kvs
--     return (tree kvs :=~=: tree kvs')
--     where
--       tree = foldr (uncurry insert) nil
--   shrink (t1 :=~=: t2) = [t1' :=~=: patch t1' t2 | t1' <- shrink t1]
--     where
--       patch t1' t2 =
--         foldr delete (foldr (uncurry insert) t2 insertions) deletions
--         where
--           deletions = [k | k <- keys t2, isNothing (find k t1')]
--           insertions = [(k, v) | k <- keys t1', let Just v = find k t1']
-- prop_Equivs :: Equivs Key Val -> Bool
-- prop_Equivs (t :=~=: t') = t =~= t'
-- {-
-- prop_ShrinkEquivs :: Equivs Key Val -> Property
-- prop_ShrinkEquivs (t :=~=: t') =
--   t =~= t' ==>
--     all (\(t :=~=: t') -> t =~= t') (shrink (t :=~=: t'))
--   where t =~= t' = toList t == toList t'
-- -}
-- prop_InsertPreservesEquivWeak :: Key -> Val -> Tree -> Tree -> Property
-- prop_InsertPreservesEquivWeak k v t t' =
--   toList t == toList t' ==> insert k v t =~= insert k v t'
-- prop_InsertPreservesEquiv :: Key -> Val -> Equivs Key Val -> Property
-- prop_InsertPreservesEquiv k v (t :=~=: t') = insert k v t =~= insert k v t'
-- prop_DeletePreservesEquiv :: Key -> Equivs Key Val -> Property
-- prop_DeletePreservesEquiv k (t :=~=: t') = delete k t =~= delete k t'
-- prop_UnionPreservesEquiv :: Equivs Key Val -> Equivs Key Val -> Property
-- prop_UnionPreservesEquiv (t1 :=~=: t1') (t2 :=~=: t2') =
--   union t1 t2 =~= union t1' t2'
-- prop_FindPreservesEquiv :: Key -> Equivs Key Val -> Property
-- prop_FindPreservesEquiv k (t :=~=: t') = find k t === find k t'
-- Completeness of insertion
prop_InsertComplete :: Tree -> Bool
prop_InsertComplete t = t == foldl (flip $ uncurry insert) nil (insertions t)

prop_InsertCompleteForDelete :: KT -> Bool
prop_InsertCompleteForDelete (k, t) = prop_InsertComplete (delete k t)

prop_InsertCompleteForUnion :: TT -> Bool
prop_InsertCompleteForUnion (t, t') = prop_InsertComplete (union t t')

-- Model based properties
prop_NilModel :: Bool
prop_NilModel = toList (nil :: Tree) == []

prop_InsertModel :: KVT -> Bool
prop_InsertModel ((k, v), t) =
  toList (insert k v t) == L.insert (k, v) (deleteKey k $ toList t)

deleteKey :: Key -> [(Key, Val)] -> [(Key, Val)]
deleteKey k = filter ((/= k) . fst)

prop_DeleteModel :: KT -> Bool
prop_DeleteModel (k, t) = toList (delete k t) == deleteKey k (toList t)

prop_UnionModel :: TT -> Bool
prop_UnionModel (t, t') =
  toList (union t t') ==
  L.sort (L.unionBy ((==) `on` fst) (toList t) (toList t'))

prop_FindModel :: KT -> Bool
prop_FindModel (k, t) = find k t == L.lookup k (toList t)

-- Measurement
{-
prop_Measure :: Key -> BST Key Val -> Property
prop_Measure k t = withMaxSuccess 100000 $
  label (if k `elem` keys t then "present" else "absent") $
  label (if t==nil               then "empty"    else
         if keys t==[k]          then "just k"   else
         if (all (>=k) (keys t)) then "at start" else
         if (all (<=k) (keys t)) then "at end"   else
         "middle") $
  True
-}
--  collect (k `elem` keys t) True
{-
prop_MeasureSize :: Int -> Property
prop_MeasureSize n = forAll (resize n arbitrary) $ \(k,t) -> withMaxSuccess 100000 $
  collect (k `elem` keys (t :: Tree)) True
-}
{-
prop_Unique :: Key -> Key -> Bool
prop_Unique x y = x/=y

prop_Elem :: Key -> Tree -> Bool
prop_Elem k t =
  not (k `elem` keys t)
-}
-- passing p = (p .&&. label "passing" True) .||. label "failing" True
-- -- Test all properties in the module: don't touch this code!
-- return []
-- runTests :: IO Bool
-- --runTests = $quickCheckAll
-- runTests = $forAllProperties $ quickCheckWithResult stdArgs {maxSuccess = 10000}
-- measureTests = do
--   writeFile "mttfs.txt" ""
--   $forAllProperties $ qcmttf
-- qcmttf p = do
--   m <- mttf p
--   if m <= 0
--     then do
--       appendFile "mttfs.txt" $ replace <$> show m ++ "\n"
--       (m < 0) `when` putStrLn "Sometimes passes, sometimes fails"
--       quickCheckResult True
--     else do
--       appendFile "mttfs.txt" (replace <$> show m ++ "\n")
--       putStrLn $ "Mean time to failure: " ++ show m
--       r <- quickCheckResult False
--       return $ r {numTests = round m}
--         -- replace '.' = ',' -- for Swedish-style decimals
--   where
--     replace c = c
-- ttf p = do
--   r <- quickCheckWithResult stdArgs {chatty = False, maxSuccess = 10000} p
--   case r of
--     Success {} -> return Nothing
--     Failure {} -> return $ Just $ numTests r
--     _ -> return Nothing
-- mttf
--   :: Testable p
--   => p -> IO Double
-- mttf p = do
--   m <- ttf p
--   case m of
--     Nothing -> return 0
--     Just n -> loop 1000 [n]
--   where
--     loop :: Int -> [Int] -> IO Double
--     loop 0 ns = return $ (fromIntegral $ sum ns) / (fromIntegral $ length ns)
--     loop k ns = do
--       m <- ttf p
--       case m of
--         Nothing -> return (-1) --error "Sometimes passes, sometimes fails"
--         Just n -> loop (k - 1) (n : ns)
intSpec :: Spec Key
intSpec =
  Spec
  { specH = M.fromList [("Int", [(show n, []) | n <- [0 .. 5] :: [Int]])]
  , specTy = "Int"
  , specFromTerm = \(Term n []) -> read n
  , specToTerm = \n -> Term (show n) []
  , specGen = arbitrary
  }

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
  , specGen = arbitrary
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
  show e = show (avgSize :: Double)
    -- "Experiment ⟨" ++
    -- eName e ++
    -- "⟩\n\tAverage Test Suite Size = " ++
    -- show (avgSize :: Double) ++
    -- "\n\tAverage Tests Thrown Away = " ++ show (avgTrashed :: Double)
    where
      ntests = fromIntegral $ length (eTests e)
      avgSize = sum (map (fromIntegral . length . tsTests) $ eTests e) / ntests
      -- avgTrashed = sum (map (fromIntegral . tsThrownAway) $ eTests e) / ntests

data ExperimentResult = ExperimentResult
  { erName :: String
  , erTotalTestSets :: Int
  , erAvgTestsPerSet :: Double
  , erAvgFailuresPerSet :: Double
  , erFracSetsWithFailure :: Double
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
    "\n" ++ "Expected Tests to Failure\t" ++ expTTF ++ "\n"
    where
      expTTF =
        if erAvgFailuresPerSet er == 0
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
  , erFracSetsWithFailure =
      sum
        (map
           (\x ->
              if x > 0
                then 1
                else 0)
           countFails) /
      fromIntegral numSets
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
  testSets <- replicateM 20 (randomTestSet g)
  pure $ Experiment name testSets

combinatorialExperiment :: Ord a => String -> Spec a -> Int -> IO (Experiment a)
combinatorialExperiment name spec n = do
  testSets <- replicateM 20 (combinatorialTestSet spec n)
  pure $ Experiment name testSets

-- executeExperiment :: String -> (a -> Bool) -> Experiment a -> IO ()
-- executeExperiment name prop e =
--   putStrLn . showResult $ runExperiment prop (e { eName = name ++ eName e })
--   -- if result == Nothing
--   --   then putStrLn "T"
--   --   else pure ()
--   where
--     -- secs = 300
--     -- time = secs * 1000000
--     showResult er =
--       let expTTF = if erAvgFailuresPerSet er == 0
--                    then "X"
--                    else show $ erAvgTestsPerSet er / erAvgFailuresPerSet er
--       in erName er ++ "," ++ expTTF
executeExperiment :: String -> (a -> Bool) -> Experiment a -> IO ()
executeExperiment name prop e =
  putStrLn . showResult $ runExperiment prop (e {eName = name ++ eName e})
  where
    showResult er = erName er ++ "," ++ show fracerr ++ "," ++ mttf
      where
        fracerr = erFracSetsWithFailure er
        mttf =
          if fracerr < 0.9
            then "X"
            else show $ (erAvgTestsPerSet er + 1) / (erAvgFailuresPerSet er + 1)

pairGen :: Gen a -> Gen b -> Gen (a, b)
pairGen x y = (,) <$> x <*> y

experiments :: IO ()
experiments = do
  let do3 = False

  let spec_kvt = intSpec `pairSpec` intSpec `pairSpec` bstSpec
  let spec_kvtk =
        intSpec `pairSpec` intSpec `pairSpec` bstSpec `pairSpec` intSpec
  let spec_kt = intSpec `pairSpec` bstSpec
  let spec_tt = bstSpec `pairSpec` bstSpec
  let spec_ttt = bstSpec `pairSpec` bstSpec `pairSpec` bstSpec
  let spec_ttk = bstSpec `pairSpec` bstSpec `pairSpec` intSpec
  let spec_kvkvt =
        intSpec `pairSpec` intSpec `pairSpec` intSpec `pairSpec` intSpec `pairSpec`
        bstSpec
  let spec_kvtt =
        intSpec `pairSpec` intSpec `pairSpec` bstSpec `pairSpec` bstSpec
  let spec_kkt = intSpec `pairSpec` intSpec `pairSpec` bstSpec

  let genExperiments g s = do
        r <- randomExperiment " - Random" g
        c2 <- combinatorialExperiment " - Combinatorial (t = 2)" s 2
        c3 <-
          if do3
            then combinatorialExperiment " - Combinatorial (t = 3)" s 3
            else pure c2
        pure (r, c2, c3)

  -- (_r_t, _c2_t, c3_t) <- genExperiments arbitrary bstSpec
  (_r_kvt, _c2_kvt, c3_kvt) <- genExperiments (arbitrary :: Gen KVT) spec_kvt
  (_r_kvtk, _c2_kvtk, c3_kvtk) <- genExperiments (arbitrary :: Gen KVTK) spec_kvtk
  (_r_kt, _c2_kt, c3_kt) <- genExperiments (arbitrary :: Gen KT) spec_kt
  (_r_tt, _c2_tt, c3_tt) <- genExperiments (arbitrary :: Gen TT) spec_tt
  (_r_ttt, _c2_ttt, c3_ttt) <- genExperiments (arbitrary :: Gen TTT) spec_ttt
  (_r_ttk, _c2_ttk, c3_ttk) <- genExperiments (arbitrary :: Gen TTK) spec_ttk
  (_r_kvkvt, _c2_kvkvt, c3_kvkvt) <-
    genExperiments (arbitrary :: Gen KVKVT) spec_kvkvt
  (_r_kvtt, _c2_kvtt, c3_kvtt) <- genExperiments (arbitrary :: Gen KVTT) spec_kvtt
  -- (_r_kkt, _c2_kkt, c3_kkt) <- genExperiments (arbitrary :: Gen KKT) spec_kkt

  putStrLn $ show c3_kt
  putStrLn $ show c3_ttk
  putStrLn $ show c3_kvt
  putStrLn $ show c3_kvtt
  putStrLn $ show c3_kvtk
  putStrLn $ show c3_kvkvt
  putStrLn $ show c3_tt

  -- executeExperiment "Arbitrary Valid" prop_ArbitraryValid r_t
  -- executeExperiment "Arbitrary Valid" prop_ArbitraryValid c2_t
  -- when do3 $ executeExperiment "Arbitrary Valid" prop_ArbitraryValid c3_t
  -- executeExperiment "Insert Valid" prop_InsertValid r_kvt
  -- executeExperiment "Insert Valid" prop_InsertValid c2_kvt
  -- when do3 $ executeExperiment "Insert Valid" prop_InsertValid c3_kvt
  -- executeExperiment "Delete Valid" prop_DeleteValid r_kt
  -- executeExperiment "Delete Valid" prop_DeleteValid c2_kt
  -- when do3 $ executeExperiment "Delete Valid" prop_DeleteValid c3_kt
  -- executeExperiment "Union Valid" prop_UnionValid r_tt
  -- executeExperiment "Union Valid" prop_UnionValid c2_tt
  -- when do3 $ executeExperiment "Union Valid" prop_UnionValid c3_tt
  -- executeExperiment "Insert Post" prop_InsertPost r_kvtk
  -- executeExperiment "Insert Post" prop_InsertPost c2_kvtk
  -- when do3 $ executeExperiment "Insert Post" prop_InsertPost c3_kvtk
  -- executeExperiment "Delete Post" prop_DeletePost r_kkt
  -- executeExperiment "Delete Post" prop_DeletePost c2_kkt
  -- when do3 $ executeExperiment "Delete Post" prop_DeletePost c3_kkt
  -- executeExperiment "Find Post Present" prop_FindPostPresent r_kvt
  -- executeExperiment "Find Post Present" prop_FindPostPresent c2_kvt
  -- when do3 $ executeExperiment "Find Post Present" prop_FindPostPresent c3_kvt
  -- executeExperiment "Find Post Absent" prop_FindPostAbsent r_kt
  -- executeExperiment "Find Post Absent" prop_FindPostAbsent c2_kt
  -- when do3 $ executeExperiment "Find Post Absent" prop_FindPostAbsent c3_kt
  -- executeExperiment "Insert Delete Complete" prop_InsertDeleteComplete r_kt
  -- executeExperiment "Insert Delete Complete" prop_InsertDeleteComplete c2_kt
  -- when do3 $
  --   executeExperiment "Insert Delete Complete" prop_InsertDeleteComplete c3_kt
  -- executeExperiment "Union Post" prop_UnionPost r_ttk
  -- executeExperiment "Union Post" prop_UnionPost c2_ttk
  -- when do3 $ executeExperiment "Union Post" prop_UnionPost c3_ttk
  -- executeExperiment "Size Insert" prop_SizeInsert r_kvt
  -- executeExperiment "Size Insert" prop_SizeInsert c2_kvt
  -- when do3 $ executeExperiment "Size Insert" prop_SizeInsert c3_kvt
  -- executeExperiment "Insert Insert" prop_InsertInsert r_kvkvt
  -- executeExperiment "Insert Insert" prop_InsertInsert c2_kvkvt
  -- when do3 $ executeExperiment "Insert Insert" prop_InsertInsert c3_kvkvt
  -- executeExperiment "Insert Delete" prop_InsertDelete r_kvtk
  -- executeExperiment "Insert Delete" prop_InsertDelete c2_kvtk
  -- when do3 $ executeExperiment "Insert Delete" prop_InsertDelete c3_kvtk
  -- executeExperiment "Insert Union" prop_InsertUnion r_kvtt
  -- executeExperiment "Insert Union" prop_InsertUnion c2_kvtt
  -- when do3 $ executeExperiment "Insert Union" prop_InsertUnion c3_kvtt
  -- executeExperiment "Delete Insert" prop_DeleteInsert r_kvtk
  -- executeExperiment "Delete Insert" prop_DeleteInsert c2_kvtk
  -- when do3 $ executeExperiment "Delete Insert" prop_DeleteInsert c3_kvtk
  -- executeExperiment "Delete Delete" prop_DeleteDelete r_kkt
  -- executeExperiment "Delete Delete" prop_DeleteDelete c2_kkt
  -- when do3 $ executeExperiment "Delete Delete" prop_DeleteDelete c3_kkt
  -- executeExperiment "Delete Union" prop_DeleteUnion r_ttk
  -- executeExperiment "Delete Union" prop_DeleteUnion c2_ttk
  -- when do3 $ executeExperiment "Delete Union" prop_DeleteUnion c3_ttk
  -- executeExperiment "Union Insert" prop_UnionInsert r_kvtt
  -- executeExperiment "Union Insert" prop_UnionInsert c2_kvtt
  -- when do3 $ executeExperiment "Union Insert" prop_UnionInsert c3_kvtt
  -- executeExperiment "Union Nil1" prop_UnionNil1 r_t
  -- executeExperiment "Union Nil1" prop_UnionNil1 c2_t
  -- when do3 $ executeExperiment "Union Nil1" prop_UnionNil1 c3_t
  -- executeExperiment "Union Nil2" prop_UnionNil2 r_t
  -- executeExperiment "Union Nil2" prop_UnionNil2 c2_t
  -- when do3 $ executeExperiment "Union Nil2" prop_UnionNil2 c3_t
  -- executeExperiment "Union Delete Insert" prop_UnionDeleteInsert r_kvtt
  -- executeExperiment "Union Delete Insert" prop_UnionDeleteInsert c2_kvtt
  -- when do3 $
  --   executeExperiment "Union Delete Insert" prop_UnionDeleteInsert c3_kvtt
  -- executeExperiment "Union Delete Delete" prop_UnionDeleteDelete r_ttk
  -- executeExperiment "Union Delete Delete" prop_UnionDeleteDelete c2_ttk
  -- when do3 $
  --   executeExperiment "Union Delete Delete" prop_UnionDeleteDelete c3_ttk
  -- executeExperiment "Union Union Idem" prop_UnionUnionIdem r_t
  -- executeExperiment "Union Union Idem" prop_UnionUnionIdem c2_t
  -- when do3 $ executeExperiment "Union Union Idem" prop_UnionUnionIdem c3_t
  -- executeExperiment "Union Union Assoc" prop_UnionUnionAssoc r_ttt
  -- executeExperiment "Union Union Assoc" prop_UnionUnionAssoc c2_ttt
  -- when do3 $ executeExperiment "Union Union Assoc" prop_UnionUnionAssoc c3_ttt
  -- executeExperiment "Insert Complete" prop_InsertComplete r_t
  -- executeExperiment "Insert Complete" prop_InsertComplete c2_t
  -- when do3 $ executeExperiment "Insert Complete" prop_InsertComplete c3_t
  -- executeExperiment
  --   "Insert Complete for Delete"
  --   prop_InsertCompleteForDelete
  --   r_kt
  -- executeExperiment
  --   "Insert Complete for Delete"
  --   prop_InsertCompleteForDelete
  --   c2_kt
  -- when do3 $
  --   executeExperiment
  --     "Insert Complete for Delete"
  --     prop_InsertCompleteForDelete
  --     c3_kt
  -- executeExperiment "Insert Complete for Union" prop_InsertCompleteForUnion r_tt
  -- executeExperiment
  --   "Insert Complete for Union"
  --   prop_InsertCompleteForUnion
  --   c2_tt
  -- when do3 $
  --   executeExperiment
  --     "Insert Complete for Union"
  --     prop_InsertCompleteForUnion
  --     c3_tt
  -- executeExperiment "Insert Model" prop_InsertModel r_kvt
  -- executeExperiment "Insert Model" prop_InsertModel c2_kvt
  -- when do3 $ executeExperiment "Insert Model" prop_InsertModel c3_kvt
  -- executeExperiment "Delete Model" prop_DeleteModel r_kt
  -- executeExperiment "Delete Model" prop_DeleteModel c2_kt
  -- when do3 $ executeExperiment "Delete Model" prop_DeleteModel c3_kt
  -- executeExperiment "Union Model" prop_UnionModel r_tt
  -- executeExperiment "Union Model" prop_UnionModel c2_tt
  -- when do3 $ executeExperiment "Union Model" prop_UnionModel c3_tt
  -- executeExperiment "Find Model" prop_FindModel r_kt
  -- executeExperiment "Find Model" prop_FindModel c2_kt
  -- when do3 $ executeExperiment "Find Model" prop_FindModel c3_kt
