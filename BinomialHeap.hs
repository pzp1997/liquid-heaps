{-|
  Binominal Heap

  - Purely Functional Data Structures
-}

module Data.Heap.Binominal where
-- (
--   -- * Data structures
--     Heap(..)
--   , Tree(..)
--   -- * Creating heaps
--   , empty
--   , singleton
--   , insert
--   , fromList
--   -- * Converting to a list
--   , toList
--   -- * Deleting
--   , deleteMin
--   -- * Checking heaps
--   , null
--   -- * Helper functions
--   , merge
--   , minimum
--   , valid
--   , heapSort
--   ) where

import Control.Applicative hiding (empty)
import Data.List (foldl', unfoldr)
import Data.Maybe
import Prelude hiding (minimum, maximum, null)
import qualified Prelude as L (null)

{-@ type Nat = {v:Int | 0 <= v} @-}

{-@ data Tree a =
    Node
        { rank :: Nat
        , root :: a
        , subtrees :: [BoundedTree a root]
        }
@-}

data Tree a =
    Node
        { rank :: Int
        , root :: a
        , subtrees :: [Tree a]
        }

newtype Heap a = Heap [Tree a]

-- | Trees with value less than X
{-@ type BoundedTree a X = Tree {v:a | X <= v} @-}

{-@ treeIsBoundedByItsRootLemma :: t:(Tree a) -> BoundedTree a (root t) @-}
treeIsBoundedByItsRootLemma :: Tree a -> Tree a
treeIsBoundedByItsRootLemma (Node {rank=r, root=x, subtrees=ts}) =
  Node {rank=r, root=x, subtrees=ts}

{-@ boundedTreeTransitivityLemma :: x:a -> {y:a | x <= y} -> BoundedTree a y -> BoundedTree a x @-}
boundedTreeTransitivityLemma :: a -> a -> Tree a -> Tree a
boundedTreeTransitivityLemma x y tree = tree


-- instance (Eq a, Ord a) => Eq (Heap a) where
--     h1 == h2 = heapSort h1 == heapSort h2

----------------------------------------------------------------

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ link :: Tree a -> Tree a -> Tree a @-}
link t1@(Node {rank=r1, root=x1, subtrees=ts1}) t2@(Node {rank=r2, root=x2, subtrees=ts2})
  | x1 <= x2  =
    let t2BoundedByX2 = treeIsBoundedByItsRootLemma t2 in
    let t2BoundedByX1 = boundedTreeTransitivityLemma x1 x2 t2BoundedByX2 in
    Node (r1+1) x1 (t2BoundedByX1:ts1)
  | otherwise =
    let t1BoundedByX1 = treeIsBoundedByItsRootLemma t1 in
    let t1BoundedByX2 = boundedTreeTransitivityLemma x2 x1 t1BoundedByX1 in
      Node (r2+1) x2 (t1BoundedByX2:ts2)

{-@ empty :: Heap a @-}
empty :: Heap a
empty = Heap []

-- {-@ null :: h:(Heap a) -> {v:Bool | v <=> h == empty} @-}
{-@ null :: h:(Heap a) -> Bool @-}
null :: Heap a -> Bool
null (Heap ts) = L.null ts

{-@ singleton :: a -> Heap a @-}
singleton :: a -> Heap a
singleton x = Heap [Node 0 x []]

{-| Insertion. Worst-case: O(log N), amortized: O(1)

Properties we would like to verify:
  1. well-formed
  2. increases length by 1
  3. elements we would expect
-}

{-@ sumNat :: Nat -> Nat -> Nat @-}
sumNat :: Int -> Int -> Int
sumNat x y = x + y

{-@ sumNatList :: [Nat] -> Nat @-}
sumNatList :: [Int] -> Int
sumNatList [] = 0
sumNatList (x:xs) = sumNat x (sumNatList xs)

-- {-@ sizeOfTree :: t:(Tree a) -> Nat / [0] @-}
-- sizeOfTree :: Tree a -> Int
-- sizeOfTree (Node {subtrees=ts}) = sumNat 1 (sumNatList (map sizeOfTree ts))

-- {-@ sizeOfTrees :: [Tree a] -> {v:Int | 0 <= v} @-}
-- sizeOfTrees :: [Tree a] -> Int
-- sizeOfTrees ts = foldl' (\acc t -> acc + sizeOfTree t) 0 ts

-- {-@ measure size @-}
-- {-@ size :: Heap a -> {v:Int | 0 <= v} @-}
-- size :: Heap a -> Int
-- size (Heap ts) = sizeOfTrees ts

{-@ insert :: Ord a => a -> Heap a -> Heap a @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x (Heap ts) = Heap (insert' (Node 0 x []) ts)

{-@ insert' :: Ord a => Tree a -> [Tree a] -> [Tree a] @-}
insert' :: Ord a => Tree a -> [Tree a] -> [Tree a]
insert' t [] = [t]
insert' t ts@(t':ts')
  | rank t < rank t' = t : ts
  | otherwise        = insert' (link t t') ts'

{-@ fromList :: Ord a => [a] -> Heap a @-}
fromList :: Ord a => [a] -> Heap a
fromList = foldl' (flip insert) empty

-- ----------------------------------------------------------------

-- {-| Creating a list from a heap. Worst-case: O(N)

-- >>> let xs = [5,3,5]
-- >>> length (toList (fromList xs)) == length xs
-- True
-- >>> toList empty
-- []
-- -}

-- {-@ toList :: Ord a => Heap a -> [a] @-}
-- toList :: Ord a => Heap a -> [a]
-- toList h =
--   case deleteMin2 h of
--     Just (x, h) -> x : toList h
--     Nothing -> []


-- toList :: Heap a -> [a]
-- toList (Heap ts) = concatMap toList' ts

-- {-@ toList' :: Tree a -> [a] @-}
-- toList' (Node _ x []) = [x]
-- toList' (Node _ x ts) = x : concatMap toList' ts

-- ----------------------------------------------------------------

-- {-| Finding the minimum element. Worst-case: O(log N), amortized: O(log N)

-- >>> minimum (fromList [3,5,1])
-- Just 1
-- >>> minimum empty
-- Nothing
-- -}

{-@ minimum :: Ord a => Heap a -> Maybe a @-}
minimum :: Ord a => Heap a -> Maybe a
minimum (Heap ts) = root . fst <$> deleteMin' ts

-- ----------------------------------------------------------------

-- {-| Deleting the minimum element. Worst-case: O(log N), amortized: O(log N)

-- >>> deleteMin (fromList [5,3,7]) == fromList [5,7]
-- True
-- >>> deleteMin empty == empty
-- True
-- -}

{-@ deleteMin :: Ord a => Heap a -> Heap a @-}
deleteMin :: Ord a => Heap a -> Heap a
deleteMin (Heap ts) =
  case deleteMin' ts of
    Nothing                  -> empty
    Just (Node _ _ ts1, ts2) -> Heap (merge' (reverse ts1) ts2)

{-@ deleteMin2 :: Ord a => Heap a -> Maybe (a, Heap a) @-}
deleteMin2 :: Ord a => Heap a -> Maybe (a, Heap a)
deleteMin2 (Heap []) = Nothing
deleteMin2 h         = (\m -> (m, deleteMin h)) <$> minimum h

{-@ deleteMin' :: Ord a => [Tree a] -> Maybe (Tree a, [Tree a]) @-}
deleteMin' :: Ord a => [Tree a] -> Maybe (Tree a, [Tree a])
deleteMin' [] = Nothing
deleteMin' (t:ts) =
  case deleteMin' ts of
    Nothing -> Just (t, [])
    Just (t', ts') ->
      if root t < root t'
      then Just (t, ts)
      else Just (t', t:ts')

{-| Merging two heaps. Worst-case: O(log N), amortized: O(log N)

Properties to verify
1. well-formedness
2. sum of counts of all elements from both should be in both
-}

{-@ merge :: Ord a => Heap a -> Heap a -> Heap a @-}
merge :: Ord a => Heap a -> Heap a -> Heap a
merge (Heap ts1) (Heap ts2) = Heap (merge' ts1 ts2)

{-@ merge' :: Ord a => [Tree a] -> [Tree a] -> [Tree a] @-}
merge' :: Ord a => [Tree a] -> [Tree a] -> [Tree a]
merge' ts1 [] = ts1
merge' [] ts2 = ts2
merge' ts1@(t1:ts1') ts2@(t2:ts2')
  | rank t1 < rank t2 = t1 : merge' ts1' ts2
  | rank t2 < rank t1 = t2 : merge' ts1 ts2'
  | otherwise         = insert' (link t1 t2) (merge' ts1' ts2')

-- ----------------------------------------------------------------
-- -- Basic operations
-- ----------------------------------------------------------------

-- {-| Checking validity of a heap.
-- -}

-- valid :: Ord a => Heap a -> Bool
-- valid t = isOrdered (heapSort t)

-- heapSort :: Ord a => Heap a -> [a]
-- heapSort t = unfoldr deleteMin2 t

-- isOrdered :: Ord a => [a] -> Bool
-- isOrdered [] = True
-- isOrdered [_] = True
-- isOrdered (x:y:xys) = x <= y && isOrdered (y:xys) -- allowing duplicated keys
