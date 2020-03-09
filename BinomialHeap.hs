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
{-@ type Pos = {v:Int | 1 <= v} @-}

{-@ measure sumSizeList @-}
{-@ sumSizeList :: [Tree a] -> Nat @-}
sumSizeList :: [Tree a] -> Int
sumSizeList [] = 0
sumSizeList (x:xs) = size x + sumSizeList xs

{-@ measure heapSize @-}
{-@ heapSize :: Heap a -> Nat @-}
heapSize :: Heap a -> Int
heapSize h =
  case h of
    Heap ts -> sumSizeList ts

{-@ data Tree a =
    Node
        { rank :: Nat
        , root :: a
        , subtrees :: [BoundedTree a root]
        , size :: {v:Pos | v == 1 + sumSizeList subtrees}
        }
@-}

data Tree a =
    Node
        { rank :: Int
        , root :: a
        , subtrees :: [Tree a]
        , size :: Int
        }

{-@ data Heap a = Heap { unheap :: [Tree a] } @-}
data Heap a = Heap { unheap :: [Tree a] }

{-@ type NEHeap a = {h:Heap a | 0 < heapSize h} @-}

-- | Trees with value less than X
{-@ type BoundedTree a X = Tree {v:a | X <= v} @-}

{-@ treeIsBoundedByItsRootLemma :: t:(Tree a) -> {v:BoundedTree a (root t) | size v == size t} @-}
treeIsBoundedByItsRootLemma :: Tree a -> Tree a
treeIsBoundedByItsRootLemma (Node {rank=r, root=x, subtrees=ts, size=sz}) =
  Node {rank=r, root=x, subtrees=ts, size=sz}

-- TODO double check if we need this lemma
{-@ boundedTreeTransitivityLemma :: x:a -> {y:a | x <= y} -> t:(BoundedTree a y) -> {v:BoundedTree a x | size v == size t} @-}
boundedTreeTransitivityLemma :: a -> a -> Tree a -> Tree a
boundedTreeTransitivityLemma x y tree = tree

-- instance (Eq a, Ord a) => Eq (Heap a) where
--     h1 == h2 = heapSort h1 == heapSort h2

----------------------------------------------------------------

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

-- TODO add size to link's refinement type
{-@ link :: t1:(Tree a) -> t2:(Tree a) -> {v:Tree a | size v == size t1 + size t2} @-}
link :: Ord a => Tree a -> Tree a -> Tree a
link t1@(Node {rank=r1, root=x1, subtrees=ts1, size=sz1}) t2@(Node {rank=r2, root=x2, subtrees=ts2, size=sz2})
  | x1 <= x2  =
    let t2BoundedByX2 = treeIsBoundedByItsRootLemma t2 in
    let t2BoundedByX1 = boundedTreeTransitivityLemma x1 x2 t2BoundedByX2 in
    Node (r1+1) x1 (t2BoundedByX1:ts1) (sz1 + sz2)
  | otherwise =
    let t1BoundedByX1 = treeIsBoundedByItsRootLemma t1 in
    let t1BoundedByX2 = boundedTreeTransitivityLemma x2 x1 t1BoundedByX1 in
    Node (r2+1) x2 (t1BoundedByX2:ts2) (sz1 + sz2)

{-@ empty :: {v:Heap a | heapSize v == 0} @-}
empty :: Heap a
empty = Heap []

-- {-@ null :: h:(Heap a) -> {v:Bool | v <=> h == empty} @-}
{-@ null :: h:(Heap a) -> {v:Bool | v <=> heapSize h == 0} @-}
null :: Heap a -> Bool
null h = heapSize h == 0

{-@ singleton :: a -> {v:Heap a | heapSize v == 1} @-}
singleton :: a -> Heap a
singleton x = Heap [Node 0 x [] 1]

{-| Insertion. Worst-case: O(log N), amortized: O(1)

Properties we would like to verify:
  1. well-formed
  2. increases length by 1
  3. elements we would expect
-}

{-@ insert :: Ord a => a -> h:(Heap a) -> {v:Heap a | 1 + heapSize h == heapSize v } @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x (Heap ts) = Heap (insert' (Node 0 x [] 1) ts)

{-@ insert' :: Ord a => t:(Tree a) -> ts:([Tree a]) -> {v:[Tree a] | sumSizeList v == size t + sumSizeList ts } @-}
insert' :: Ord a => Tree a -> [Tree a] -> [Tree a]
insert' t [] = [t]
insert' t ts@(t':ts')
  | rank t < rank t' = t : ts
  | otherwise        = insert' (link t t') ts'

{-@ measure len @-}
{-@ len :: [a] -> Nat @-}
len :: [a] -> Int
len [] = 0
len (_:xs) = 1 + len xs

{-@ fromList :: Ord a => xs:[a] -> {v:Heap a | heapSize v == len xs} @-}
fromList :: Ord a => [a] -> Heap a
fromList [] = empty
fromList (x:xs) = insert x (fromList xs)

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

{-@ minimum :: NEHeap a -> a @-}
minimum :: Ord a => Heap a -> a
minimum = root . fst . deleteMin' . unheapNonempty

-- ----------------------------------------------------------------

-- {-| Deleting the minimum element. Worst-case: O(log N), amortized: O(log N)

-- >>> deleteMin (fromList [5,3,7]) == fromList [5,7]
-- True
-- >>> deleteMin empty == empty
-- True
-- -}

{-@ reverseHeapList :: xs:[Tree a] -> {v:[Tree a] | sumSizeList v == sumSizeList xs} @-}
reverseHeapList :: [Tree a] -> [Tree a]
reverseHeapList xs = reverseHeapListAux xs []

{-@ reverseHeapListAux :: xs:[Tree a] -> acc:[Tree a] -> {v:[Tree a] | sumSizeList v == sumSizeList xs + sumSizeList acc} @-}
reverseHeapListAux :: [Tree a] -> [Tree a] -> [Tree a]
reverseHeapListAux [] acc = acc
reverseHeapListAux (x:xs) acc = reverseHeapListAux xs (x:acc)

{-@ unheapNonempty :: h:(NEHeap a) -> {v:[Tree a] | 0 < len v && sumSizeList v == heapSize h} @-}
unheapNonempty :: Heap a -> [Tree a]
unheapNonempty (Heap ts@(_:_)) = ts

{-@ deleteMin :: h:(NEHeap a) -> {v:Heap a | 1 + heapSize v == heapSize h} @-}
deleteMin :: Ord a => Heap a -> Heap a
deleteMin h =
  let (Node _ _ ts1 _, ts2) = deleteMin' (unheapNonempty h) in
  Heap (merge' (reverseHeapList ts1) ts2)

{-@ deleteMin2 :: h:NEHeap a -> {v:(a, Heap a) | 1 + heapSize (snd v) == heapSize h} @-}
deleteMin2 :: Ord a => Heap a -> (a, Heap a)
deleteMin2 h         = (minimum h, deleteMin h)

{-@ deleteMin' :: {xs:[Tree a] | 0 < len xs} -> {v:(Tree a, [Tree a]) | size (fst v) + sumSizeList (snd v) == sumSizeList xs} @-}
deleteMin' :: Ord a => [Tree a] -> (Tree a, [Tree a])
deleteMin' [t] = (t, [])
deleteMin' (t:ts) =
  let (t', ts') = deleteMin' ts in
  if root t < root t'
  then (t, ts)
  else (t', t:ts')

{-| Merging two heaps. Worst-case: O(log N), amortized: O(log N)

Properties to verify
1. well-formedness
2. sum of counts of all elements from both should be in both
-}

{-@ merge :: Ord a => h1:(Heap a) -> h2:(Heap a) -> {v:(Heap a) | heapSize v == heapSize h1 + heapSize h2} @-}
merge :: Ord a => Heap a -> Heap a -> Heap a
merge (Heap ts1) (Heap ts2) = Heap (merge' ts1 ts2)

{-@ merge' :: Ord a => ts1:[Tree a] -> ts2:[Tree a] -> {v:[Tree a] | sumSizeList v == sumSizeList ts1 + sumSizeList ts2} @-}
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
