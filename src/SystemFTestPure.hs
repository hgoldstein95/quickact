{-# LANGUAGE DeriveDataTypeable, PartialTypeSignatures, ImplicitParams, FlexibleInstances, DeriveGeneric, TupleSections, TypeApplications #-}
{-# options_ghc -Wno-missing-methods -Wno-partial-type-signatures #-}

{-
  Generators and properties for SystemF
-}

module SystemFTestPure where

import SystemF

-- import Criterion (nfAppIO, benchmark)
import Test.QuickCheck

import qualified Data.Map as M

import System.Timeout (timeout)
import System.IO.Unsafe (unsafePerformIO)

import Data.List
import Data.Maybe
import Data.Typeable hiding (typeOf)
import Data.Data hiding (typeOf)
import Control.Monad

import Term hiding (eval)
import HT hiding (Expr)

import Text.ParserCombinators.Parsec
import Data.CSV
import Text.Printf

------------------------------------------
-- GENERATION
------------------------------------------

genType :: _ => Int -> Gen Type
genType ftv = sized (arb ftv)
    where arb ftv 0 = elements $ [Base {-, TBool -}] ++ (TVar <$> [0 .. ftv-1])
          arb ftv n = oneof [arb ftv 0,
                             (:->) <$> arb ftv (n `div` 6) <*> arb ftv (n `div` 4),
                             ForAll <$> arb (ftv+1) (n-1)
                            ]

genExpr :: _ => Gen (Maybe Expr)
genExpr =
  sized $ (\n -> do t <- genType 0; arb 0 [] t n)
    where arb :: Int -> [Type] -> Type -> Int -> Gen (Maybe Expr)
          arb ftv c t 0 = oneofMaybe $
                          [ return $ Just Con | t == Base ] ++
                          -- [ return $ Just BTrue | t == TBool ] ++
                          -- [ return $ Just BFalse | t == TBool ] ++
                          [ return $ Just $ Var i | (i,t') <- zip [0..] c, t == t' ] ++
                          [ fmap (Lam t1) <$> arb ftv (t1:c) t2 0 | (t1 :-> t2) <- [t] ] ++
                          [ fmap TLam <$> arb (ftv+1) (map (liftType 0) c) t1 0 | (ForAll t1) <- [t] ]   -- MUTANT?
          arb ftv c t n = frequency $
                          [ (6, arb ftv c t 0) ] ++
                          [ (8, fmap (Lam t1) <$> (arb ftv (t1:c) t2 (n-1))) | (t1 :-> t2) <- [t] ] ++
                          [ (4, fmap TLam <$> (arb (ftv+1) (map (liftType 0) c) t1 (n-1))) | (ForAll t1) <- [t] ] ++
                          [ (8, do t2 <- do
                                         arbT <- resize 10 $ genType ftv   -- for now; should be bigger?
                                         elements (nub $ michal c t ++ [arbT])
                                   me1 <- arb ftv c (t2 :-> t) (n `div` 2)
                                   me2 <- arb ftv c t2 (n `div` 2)
                                   return $ (:@:) <$> me1 <*> me2) ] ++
                          [ (4, do t1t2 <- genT1T2 t
                                   case t1t2 of
                                     Just (t1, t2) -> do
                                       me1 <- arb ftv c t1 (n - 1)
                                       return $ TApp <$> me1 <*> return t2
                                     Nothing -> return Nothing) ]--  ++
                          -- [ (0, do e1 <- arb ftv c TBool (n `div` 3)
                          --          e2 <- arb ftv c t (n `div` 3)
                          --          e3 <- arb ftv c t (n `div` 3)
                          --          return $ Cond <$> e1 <*> e2 <*> e3) ]


michal c t = [t' | varType <- c,
                   t' <- aux varType]
  where aux (t1 :-> t2) | t==t2 = [t1]
                        | t/=t2 = aux t2
        aux _                   = []


-- Check if a type has any type variables.
-- TODO: replace with "isClosed"
hasTVars :: Type -> Bool
hasTVars (TVar _)    = True
hasTVars (t1 :-> t2) = hasTVars t1 || hasTVars t2
hasTVars (ForAll t)  = hasTVars t
hasTVars TBool       = False
hasTVars Base        = False


isClosed :: Type -> Bool
isClosed = isClosed' 0
  where
    isClosed' :: Int -> Type -> Bool
    isClosed' tc (TVar x)    = x < tc
    isClosed' tc (t1 :-> t2) = isClosed' tc t1 && isClosed' tc t2
    isClosed' tc (ForAll t)  = isClosed' (tc+1) t
    isClosed' _ TBool        = True
    isClosed' _ Base         = True

-- Randomly fetch a subterm of a type
fetchSubType :: Type -> Gen (Maybe Type)
fetchSubType t =
  oneofMaybe $
  [ return (Just t) | isClosed t ] ++
  [ fetchSubType t1 | (t1 :-> t2) <- [t] ] ++
  [ fetchSubType t2 | (t1 :-> t2) <- [t] ] ++
  [ fetchSubType t' | (ForAll t') <- [t] ]

oneofMaybe :: [Gen (Maybe a)] -> Gen (Maybe a)
oneofMaybe [] = return Nothing
oneofMaybe gs = oneof gs

-- "Replace (some occurrences of) closed type s in type t by (TVar n)"
replaceSubType :: Int -> Type -> Type -> Gen Type
replaceSubType n s t =
  oneof $
  [ return t ] ++
  [ return $ TVar n | s == t ] ++
  [ do t1' <- replaceSubType n s t1; t2' <- replaceSubType n s t2; return $ t1' :-> t2' | (t1 :-> t2) <- [t] ] ++
  [ do t'' <- replaceSubType (n+1) s t'; return $ ForAll t'' | (ForAll t') <- [t], t' == s ]


-- Generate t1 t2 such that t1{0:=t2} = t
genT1T2 :: Type -> Gen (Maybe (Type, Type))
genT1T2 t = do
  let t' = let ?mutant = NoMutant in liftType 0 t
  t2 <- fetchSubType t'
  case t2 of
    Just t2' -> do t1 <- replaceSubType 0 t2' t'
                   return $ Just (ForAll t1, t2')
    Nothing  -> return Nothing


------------------------------------------
-- GENERATION CONFIGURATIONS
------------------------------------------

data GenConfig = GC { gcName :: String
                    , gcTake :: Gen Expr -> Gen Expr
                    , gcBaseChoice :: [Gen Expr] -> Gen Expr
                    , gcRecChoice :: [(Int, Gen Expr)] -> Gen Expr
                    , gcRetryType :: Int
                    , gcRetryTApp :: Int
                    , gcRetryFun :: Int
                    }

instance PrintfArg GenConfig where
  formatArg x fmt
    | fmtChar (vFmt 's' fmt) == 's' = formatString (show x) (fmt { fmtChar = 's', fmtPrecision = Nothing })
  formatArg _ fmt = errorBadFormat $ fmtChar fmt


data GenConfigType = GCPlain
                   | GCBacktrack
                   | GCRetryLeaf
                   | GCRetryType
                   | GCRetryTypeCut
                   | GCRetryFun
                   | GCRetryFunCut
                   deriving (Data, Typeable, Show, Eq)

gcOfGcType :: GenConfigType -> GenConfig
gcOfGcType GCPlain = gcPlain
gcOfGcType GCBacktrack = gcBacktrack
gcOfGcType GCRetryLeaf = gcSimple1
gcOfGcType GCRetryType = gcSimple2
gcOfGcType GCRetryFun  = gcSimple3
gcOfGcType GCRetryTypeCut = gcRetryTypeCut
gcOfGcType GCRetryFunCut = gcRetryFunCut


instance Show GenConfig where
  show gc = show (gcName gc, gcRetryType gc, gcRetryFun gc, gcRetryTApp gc)


takeG n = id
retry n = id
cut = id

gcPlain = GC { gcName = "Random"
             , gcTake = id
             , gcBaseChoice = oneof
             , gcRecChoice = frequency
             , gcRetryType = 1
             , gcRetryFun = 1
             , gcRetryTApp = 1
             }

gcBacktrack = GC { gcName = "Hybrid"
                 , gcTake = takeG 10
                 , gcBaseChoice = oneof
                 , gcRecChoice = cut . frequency
                 , gcRetryType = 1
                 , gcRetryFun = 2
                 , gcRetryTApp = 1
                 }

gcSimple1 = gcPlain { gcName = "Simple1 (leaves only)"
                    , gcBaseChoice = oneof -- LOOK HERE
                    , gcTake = takeG 1
                    }

gcSimple2 = gcPlain { gcName = "Simple2 (retry type)"
                    , gcRetryType = 2
                    , gcTake = takeG 1
                    }

gcRetryTypeCut = gcPlain { gcName = "Retry type with cut"
                         , gcRetryType = 2
                         , gcRecChoice = cut . frequency
                         , gcTake = takeG 1
                         }

gcSimple3 = gcPlain { gcName = "Simple3 (retry fun)"
                    , gcRetryFun = 2
                    , gcTake = takeG 1
                    }

gcRetryFunCut = gcPlain { gcName = "Retry fun with cut"
                        , gcRecChoice = cut . frequency
                        , gcRetryFun = 2
                        , gcTake = takeG 1
                        }


all_configs = [ GCPlain ]
{-
              , GCRetryLeaf
              , GCRetryType, GCRetryTypeCut
              , GCRetryFun,  GCRetryFunCut
              ]
-}

------------------------------------------
-- SHRINKING
------------------------------------------

shrinkType :: Type -> [Type]
shrinkType Base  = []
shrinkType TBool = [Base]
shrinkType (t1 :-> t2) = Base : t1 : t2 : [ t1' :-> t2 | t1' <- shrinkType t1 ] ++
                                          [ t1 :-> t2' | t2' <- shrinkType t2 ]
shrinkType (TVar n) = Base : [TVar n' | n' <- shrink n]
shrinkType (ForAll t) = Base : t : [ForAll t' | t' <- shrinkType t]

shrinkExpr' Con = []
shrinkExpr' (Var n) = Con : [Var n' | n' <- shrink n]
shrinkExpr' (Lam t e) = Con : e : [Lam t' e | t' <- shrinkType t] ++
                                  [Lam t e' | e' <- shrinkExpr' e]
shrinkExpr' (e1 :@: e2) = Con : e1 : e2 : [e1' :@: e2 | e1' <- shrinkExpr' e1] ++ [e1 :@: e2' | e2' <- shrinkExpr' e2]
shrinkExpr' (Cond e1 e2 e3) = Con : e1 : e2 : e3 : [Cond e1' e2 e3 | e1' <- shrinkExpr' e1] ++ [Cond e1 e2' e3 | e2' <- shrinkExpr' e2] ++ [Cond e1 e2 e3' | e3' <- shrinkExpr' e3]
shrinkExpr' BTrue = [Con]
shrinkExpr' BFalse = [Con, BTrue]
shrinkExpr' (TLam e) = Con : e : [TLam e' | e' <- shrinkExpr' e]
shrinkExpr' (TApp e t) = Con : e : [TApp e' t | e' <- shrinkExpr' e] ++ [TApp e t' | t' <- shrinkType t]

shrinkExpr :: _ => Expr -> [Expr]
shrinkExpr e = [ e' | e' <- shrinkExpr' e, wellTyped e']
               ++ [ e'' | e' <- shrinkExpr' e, e'' <- shrinkExpr' e', wellTyped e'']
               ++ [ e' | Just e' <- [step e], size e' < size e] --, typeOf e' = typeOf e]

------------------------------------------
-- LAMBDA CSV GEN
------------------------------------------

-- lambda_csv_gen :: String -> [(Mutant, PropType)] -> [GenConfigType] ->
--                   Int -> Int -> Int -> Int -> Int -> IO ()
-- lambda_csv_gen file setups cs tpt gt numTests runs max_size = do
--   results <- forM [ (mutant, pt, config) | (mutant, pt) <- setups , config <- map gcOfGcType cs ] $ \(m,pt,c) -> do
--     putStrLn $ "Running Config: " ++ show (m,c,pt)
--     res <- do let ?mutant = m
--                   ?config = c
--               gatherStatsPure runs gt numTests max_size (forAll genExpr $ propTimeout tpt (propOfPropType pt))
--     return (m, pt, c, res)
--   putStrLn $ unlines $ map (\(m, p, c, r) -> show (m, p, c, statsShow r)) results

--   -- To CSV
--   let csvStr = genCsvFile $ map (\(m, p, c, r) -> [show m, show p, show c] ++ statsToCSV r) results
--   writeFile file csvStr

--
--lambda_csv_gen' :: String -> IO ()
--lambda_csv_gen' file = do
--  results <- forM [ (mutant, config) | mutant <- all_mutants , config <- all_configs ] $ \(m,c) -> do
--    putStrLn $ "Running Config: " ++ show (m,c)
--    res <- do let ?mutant = m
--                  ?config = c
--              mttf (-1) 1000 (forAll genExpr $ propTimeout 10000 (\e -> bToE e $ prop_normalform e))
--    return (m, c, res)
--  putStrLn $ unlines $ map show results
--
--  -- To CSV
--  let csvStr = genCsvFile $ map (\(m, c, r) -> [show m, show c] ++ mttfToCSV r) results
--  writeFile file csvStr

------------------------------------------
-- LAMBDA STATS
------------------------------------------

-- lambda_stats :: _ => Int -> _
-- lambda_stats n = do
--   let aux :: Int -> IO [Expr]
--       aux 0 = return []
--       aux m = do
--         es <- catMaybes <$> sample' genExpr
--         let es' = take m es
--         es'' <- aux (m - length es')
--         return (es' ++ es'')
--   es <- aux n -- sequence $ replicate 10000 $ concat <$> sampleList (genExpr :: Gen Expr)
--   putStrLn "Number of terms:"
--   print $ length $ es
--   putStrLn "Number of non-Con terms:"
--   print $ length $ filter (/=Con) $ es
--   putStrLn "Number of unique terms:"
--   print $ length $ nub' $ es
--   putStrLn "Distribution of sizes:"
--   print $ dist $ map size $ es
--   putStrLn "Distribution of sizes of unique terms:"
--   print $ dist $ map size $ nub' $ es
--   let terms = es
--   let totVars = sum $ map (length . vars) $ terms
--   let totLams = sum $ map lambdas $ terms
--   print "Total vars / lambdas:"
--   print $ fromIntegral totVars / fromIntegral totLams
--   print "Reduction sequence lengths:"
--   print $ dist $ map (length . eval) terms
--   print "Reduction sequence lengths for unique terms:"
--   print $ dist $ map (length . eval) $ nub' terms

  -- where dist es = map (\gs -> (head gs, length gs)) $ group $ sort $ es

-- nub' = map head . group . sort

------------------------------------------
-- LAMBDA STATS
------------------------------------------
{-
lambda_stats :: _ => _
lambda_stats = do
  es <- sequence $ replicate 10000 $ concat <$> sampleList (genExpr :: Gen Expr)
  putStrLn "Number of terms:"
  print $ length $ concat es
  putStrLn "Number of non-Con terms:"
  print $ length $ filter (/=Con) $ concat es
  putStrLn "Number of unique terms:"
  print $ length $ nub' $ concat es
  putStrLn "Distribution of sizes:"
  print $ dist $ map size $ concat es
  putStrLn "Distribution of sizes of unique terms:"
  print $ dist $ map size $ nub' $ concat es
  let terms = concat es
  let totVars = sum $ map (length . vars) $ terms
  let totLams = sum $ map lambdas $ terms
  print "Total vars / lambdas:"
  print $ fromIntegral totVars / fromIntegral totLams
  print "Reduction sequence lengths:"
  print $ dist $ map (length . eval) terms
  print "Reduction sequence lengths for unique terms:"
  print $ dist $ map (length . eval) $ nub' terms

  where dist es = map (\gs -> (head gs, length gs)) $ group $ sort $ es

nub' = map head . group . sort
-}

------------------------------------------
-- PROPERTIES
------------------------------------------

data PropType = PropStrongNormalization
              | PropStrongNormalizationStep
              | PropEvalMakesProgress
              | PropStepMakesProgress
              | PropEvalShort
              | PropBigSmallStep
              | PropHnfNoStep
              | PropEvalNoMoreSteps
              | PropGenWellTyped
              | PropPreservation
              | PropParallelPreservation
              | PropPreservationMulti
              | PropProgress
              | PropEvalSame
              | PropPSame
              | PropEvalStepSame
              | PropTest
  deriving (Show, Read, Eq, Ord, Enum, Bounded, Data, Typeable)

instance Testable (Either String ()) where
  property (Left  s) = whenFail (putStrLn s) False
  property (Right _) = property True

propOfPropType :: _ => PropType -> (Expr -> Property)
propOfPropType PropStrongNormalization e = property $ prop_normalform e
propOfPropType PropStrongNormalizationStep e = property $ prop_normalform' e
propOfPropType PropEvalMakesProgress e = property $ prop_evalMakesProgress e
propOfPropType PropStepMakesProgress e = property $ prop_stepMakesProgress e
propOfPropType PropEvalShort e = property $ prop_evalShort e
propOfPropType PropBigSmallStep e = property $ prop_bigSmallStep e
propOfPropType PropHnfNoStep e = property $ prop_hnfNoStep e
propOfPropType PropEvalNoMoreSteps e = property $ prop_evalNoMoreSteps e
propOfPropType PropGenWellTyped e = property $ prop_wellTyped e
propOfPropType PropPreservation e = prop_preservation e
propOfPropType PropParallelPreservation e = prop_ppreservation e
propOfPropType PropPreservationMulti e = prop_preservation_multi 0 20 e
propOfPropType PropProgress e = property $ prop_progress e
propOfPropType PropEvalSame e = property $ prop_evalSame e
propOfPropType PropPSame e = property $ prop_PSame e
propOfPropType PropEvalStepSame e = property $ prop_evalStepSame e
propOfPropType PropTest e = property $ prop_test e


bToE :: (Show a) => a -> Bool -> Either String ()
bToE _ True = Right ()
bToE x False = Left (show x)

prop_normalform e = isHnf . last . eval $ e
prop_normalform' e = isHnf . last . eval' $ e

prop_wellTyped e = wellTyped e

prop_evalMakesProgress e =
  and (zipWith (/=) es $ drop 1 es)
  where es = eval e

prop_stepMakesProgress e =
  and (zipWith (/=) es $ drop 1 es)
  where es = eval' e

prop_evalShort e =
  length (eval e) < 100

prop_bigSmallStep e =
  let es = eval e
      es' = eval' e
  in last es == last es'

prop_hnfNoStep e =
  (not $ isHnf e) || (isNothing $ step e)

prop_evalNoMoreSteps e =
  isNothing $ step (last $ eval e)

prop_preservation e =
  case step e of
    Just s ->
      whenFail (do putStrLn $ "Original:  " ++ show e
                   putStrLn $ "With Type: " ++ show (typeOf e)
                   putStrLn $ "Steps To:  " ++ show s
                   putStrLn $ "With Type: " ++ show (typeOf s)
               )
               (typeOf e == typeOf s)
    Nothing -> discard

prop_ppreservation e =
  let s = pstep e in
  whenFail (do putStrLn $ "Original:  " ++ show e
               putStrLn $ "With Type: " ++ show (typeOf e)
               putStrLn $ "Steps To:  " ++ show s
               putStrLn $ "With Type: " ++ show (typeOf s)
           )
           (typeOf e == typeOf s)

prop_preservation_multi n max e =
  if n == max then collect n True else
  case step e of
    Just s ->
      whenFail (do putStrLn $ "Original:  " ++ show e
                   putStrLn $ "With Type: " ++ show (typeOf e)
                   putStrLn $ "Steps To:  " ++ show s
                   putStrLn $ "With Type: " ++ show (typeOf s)
               )
               $ if typeOf e == typeOf s then prop_preservation_multi (n+1) max s
                 else property False
    Nothing -> collect n True

prop_progress e = isHnf e || canStep e

prop_evalSame e =
  take 100 (let ?mutant = NoMutant in eval e) == take 100 (eval e)

prop_pevalSame e =
  (let ?mutant = NoMutant in peval e) == peval e

prop_PSame e =
  (let ?mutant = NoMutant in pstep e) == pstep e

prop_evalStepSame e =
  take 100 (let ?mutant = NoMutant in eval' e) == take 100 (eval' e)

prop_test e =
  case e of
    (Lam _ (Lam _ _)) :@: (Lam _ _) -> False
    Lam _ e -> prop_test e
    TLam e -> prop_test e
    e1 :@: e2 -> prop_test e1 && prop_test e2
    TApp e1 _ -> prop_test e1
    Cond e1 e2 e3 -> prop_test e1 && prop_test e2 && prop_test e3
    _ -> True

propTimeout :: Int -> (Expr -> Property) -> Maybe Expr -> Property
propTimeout microseconds p Nothing  = discard
propTimeout microseconds p (Just e) =
  unsafePerformIO $ do
    res <- timeout microseconds $ return $! p e
    case res of
      Just x -> return x
      Nothing -> discard

-- checkProperty mutant config propType numTests tpt = do
--   let qcConfig = stdArgs {maxSuccess = numTests, maxDiscardRatio = 10, maxSize = 100}
--   let ?mutant = mutant
--       ?config = gcOfGcType $ config
--   quickCheckWithResult qcConfig $ forAll genExpr $ propTimeout tpt (propOfPropType propType)

typeFromTerm :: Term -> Type
typeFromTerm (Term "Base" []) = Base
typeFromTerm (Term "TBool" []) = TBool
typeFromTerm (Term "Func" [t1, t2]) = typeFromTerm t1 :-> typeFromTerm t2
typeFromTerm (Term "TVar" [Term n []]) = TVar 0
typeFromTerm (Term "ForAll" [t]) = ForAll $ typeFromTerm t
typeFromTerm _ = error "bad term"

typeToTerm :: Type -> Term
typeToTerm Base = Term "Base" []
typeToTerm TBool = Term "TBool" []
typeToTerm (t1 :-> t2) = Term "Func" [typeToTerm t1, typeToTerm t2]
typeToTerm (TVar n) = Term "TVar" []
typeToTerm (ForAll t) = Term "ForAll" [typeToTerm t]

typeSpec :: Spec Type
typeSpec =
  Spec
  { specH =
      M.fromList
      [ ("Type", [ ("Base", [])
                 , ("TBool", [])
                 , ("Func", ["Type", "Type"])
                 , ("TVar", [])
                 , ("Forall", ["Type"])
                 ])
      ]
  , specTy = "Type"
  , specFromTerm = typeFromTerm
  , specToTerm = typeToTerm
  , specGen = genType 0
  }

exprFromTerm :: Term -> Expr
exprFromTerm (Term "Con" []) = Con
exprFromTerm (Term "Var" []) = Var 0
exprFromTerm (Term "Lam" [t, e]) = Lam (typeFromTerm t) (exprFromTerm e)
exprFromTerm (Term "App" [e1, e2]) = exprFromTerm e1 :@: exprFromTerm e2
exprFromTerm (Term "Cond" [e1, e2, e3]) = Cond (exprFromTerm e1) (exprFromTerm e2) (exprFromTerm e3)
exprFromTerm (Term "BTrue" []) = BTrue
exprFromTerm (Term "BFalse" []) = BFalse
exprFromTerm (Term "TLam" [e]) = TLam (exprFromTerm e)
exprFromTerm (Term "TApp" [e, t]) = TApp (exprFromTerm e) (typeFromTerm t)
exprFromTerm _ = error "bad term"

exprToTerm :: Expr -> Term
exprToTerm Con = Term "Con" []
exprToTerm (Var _) = Term "Var" []
exprToTerm (Lam t e) = Term "Lam" [typeToTerm t, exprToTerm e]
exprToTerm (e1 :@: e2) = Term "App" [exprToTerm e1, exprToTerm e2]
exprToTerm (Cond e1 e2 e3) = Term "Cond" [exprToTerm e1, exprToTerm e2, exprToTerm e3]
exprToTerm BTrue = Term "BTrue" []
exprToTerm BFalse = Term "BFalse" []
exprToTerm (TLam e) = Term "TLam" [exprToTerm e]
exprToTerm (TApp e t) = Term "TApp" [exprToTerm e, typeToTerm t]

untilJust :: Monad m => m (Maybe a) -> m a
untilJust m = do
  x <- m
  case x of
    Nothing -> untilJust m
    Just y -> pure y

exprSpec :: _ => Spec Expr
exprSpec =
  Spec
  { specH =
      M.fromList
        [ ("Expr", [ ("Con", [])
                   , ("Var", [])
                   , ("Lam", ["Type", "Expr"])
                   , ("App", ["Expr", "Expr"])
                   , ("Cond", ["Expr", "Expr", "Expr"])
                   , ("BTrue", [])
                   , ("BFalse", [])
                   , ("TLam", ["Expr"])
                   , ("TApp", ["Expr", "Type"])
                   ])
        ] `M.union`
      specH typeSpec
  , specTy = "Expr"
  , specFromTerm = exprFromTerm
  , specToTerm = exprToTerm
  , specGen = untilJust genExpr
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
    "⟩\n\tAverage Test Suite Size = " ++
    show (avgSize :: Double) ++
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

experiments :: IO ()
experiments = do
  let ?mutant = NoMutant
  r <- randomExperiment "" (untilJust genExpr)
  c2 <- combinatorialExperiment "" exprSpec 2
  c3 <- combinatorialExperiment "" exprSpec 3
  c4 <- combinatorialExperiment "" exprSpec 4


  let singleExperiment prop name = do
        executeExperiment (name ++ " - Random") prop r
        executeExperiment (name ++ " - Combinatorial (t = 2)") prop c2
        executeExperiment (name ++ " - Combinatorial (t = 3)") prop c3
        executeExperiment (name ++ " - Combinatorial (t = 4)") prop c4

  let allMutants = [ LiftVar
                   , LiftLam
                   , LiftTLamA
                   , LiftTLamB
                   , LiftTApp
                   , SubstVar
                   , SubstLT
                   , SubstInTypeNoDecr
                   , SubstInTypeLT
                   , LiftTypeTVar
                   , LiftTypeForAll
                   , TSubstNoIncr
                   , AppForgetSubst
                   , TAppForgetSubst
                   , SubstSwapped
                   , SubstNoIncr
                   , SubstNoLift
                   , SubstInTypeNoIncr
                   , SubstNoLiftT
                   , LiftTNoIncr
                   ]

  let testMutant mutant = do
        let ?mutant = mutant
        singleExperiment prop_evalSame (show mutant ++ ",Big Step")
        singleExperiment prop_pevalSame (show mutant ++ ",Parallel")

  mapM_ testMutant allMutants
  -- mapM_ print $ gen 2 (specH exprSpec) (specTy exprSpec)
