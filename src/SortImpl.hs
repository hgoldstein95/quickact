module SortImpl where

insert :: [Int] -> Int -> [Int]
insert [] y = [y]
insert (x : xs) y
  | y < x = y : x : xs
  | otherwise = x : insert xs y

sort :: [Int] -> [Int]
sort = foldl insert []
