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

----------------------------------------------------------------



{-@ data Tree a =
    Node
        { _rank :: Int
        , _root :: a
        , subtrees :: [BoundedTree a _root]
        }
@-}

data Tree a =
    Node
        { _rank :: Int
        , _root :: a
        , subtrees :: [Tree a]
        }

-- | Trees with value less than X
{-@ type BoundedTree a X = Tree {v:a | X <= v} @-}


{-@ boundedTreeTransitivityLemma :: x:a -> {y:a | x <= y} -> BoundedTree a y -> BoundedTree a x @-}
boundedTreeTransitivityLemma :: a -> a -> Tree a -> Tree a
boundedTreeTransitivityLemma x y tree = tree


newtype Heap a = Heap [Tree a]

-- instance (Eq a, Ord a) => Eq (Heap a) where
--     h1 == h2 = heapSort h1 == heapSort h2

----------------------------------------------------------------

{-@ rank :: Tree a -> Int @-}
rank (Node { _rank=r }) = r

{-@ root :: Tree a -> a @-}
root (Node { _root=x }) = x

{-@ measure root @-}

-- {-@ treeIsBoundedByItsRootLemma :: t:(Tree a) -> BoundedTree a (root t) @-}
-- treeIsBoundedByItsRootLemma :: Tree a -> Tree a
-- treeIsBoundedByItsRootLemma tree = tree


{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

-- {-@ isBoundedTree :: Ord a => x:a -> BoundedTree a x -> b -> b @-}
-- isBoundedTree :: Ord a => a -> Tree a -> b -> b
-- isBoundedTree root tree z = z

-- {-@ isBoundedTree :: x:a -> Tree {v:a | x <= v} -> BoundedTree a x @-}
-- isBoundedTree :: a -> Tree a -> Tree a
-- isBoundedTree root tree@(Node {_rank=r, _root=x, subtrees=ts}) =
--     case ts of
--         [] -> Node r x []
--         _ -> Node r x ts


{-@ isBoundedTree :: Tree {v:a | x <= v} -> BoundedTree a x @-}
isBoundedTree :: Tree a -> Tree a
isBoundedTree root tree@(Node {_rank=r, _root=x, subtrees=ts}) =
    case ts of
        [] -> Node r x []
        _ -> Node r x ts

-- x1 <= x2 -> BoundedTree a x2 -> BoundedTree a x1

{-@ link :: Ord a => Tree a -> Tree a -> Tree a @-}
link t1@(Node {_rank=r1, _root=x1, subtrees=ts1}) t2@(Node {_rank=r2, _root=x2, subtrees=ts2})
  | x1 <= x2  =
    --   assert (x1 <= x2) $
    --    isBoundedTree x1 ts1 $
    --    isBoundedTree x2 ts2 $
        let t2Bounded = boundedTreeTransitivityLemma x1 x2 (isBoundedTree x2 t2) in
        Node (r1+1) x1 (t2Bounded:ts1)
    --    isBoundedTree x2 t2 $
                -- x1 <= x2
                -- \forall v \in ts1, x1 <= v
                -- \forall v \in ts2, x2 <= v
                -- Goal: \forall v \in ts2, x1 <= v



  | otherwise = Node (r2+1) x2 (t1:ts2)

----------------------------------------------------------------

-- {-| Empty heap.
-- -}

-- empty :: Heap a
-- empty = Heap []

-- {-|
-- See if the heap is empty.

-- >>> Data.Heap.Binominal.null empty
-- True
-- >>> Data.Heap.Binominal.null (singleton 1)
-- False
-- -}

-- null :: Heap a -> Bool
-- null (Heap ts) = L.null ts

-- {-| Singleton heap.
-- -}

-- singleton :: a -> Heap a
-- singleton x = Heap [Node 0 x []]

-- ----------------------------------------------------------------

-- {-| Insertion. Worst-case: O(log N), amortized: O(1)

-- >>> insert 7 (fromList [5,3]) == fromList [3,5,7]
-- True
-- >>> insert 5 empty            == singleton 5
-- True
-- -}

-- insert :: Ord a => a -> Heap a -> Heap a
-- insert x (Heap ts) = Heap (insert' (Node 0 x []) ts)

-- insert' :: Ord a => Tree a -> [Tree a] -> [Tree a]
-- insert' t [] = [t]
-- insert' t ts@(t':ts')
--   | rank t < rank t' = t : ts
--   | otherwise        = insert' (link t t') ts'

-- ----------------------------------------------------------------

-- {-| Creating a heap from a list.

-- >>> empty == fromList []
-- True
-- >>> singleton 'a' == fromList ['a']
-- True
-- >>> fromList [5,3] == fromList [5,3]
-- True
-- -}

-- fromList :: Ord a => [a] -> Heap a
-- fromList = foldl' (flip insert) empty

-- ----------------------------------------------------------------

-- {-| Creating a list from a heap. Worst-case: O(N)

-- >>> let xs = [5,3,5]
-- >>> length (toList (fromList xs)) == length xs
-- True
-- >>> toList empty
-- []
-- -}

-- toList :: Heap a -> [a]
-- toList (Heap ts) = concatMap toList' ts

-- toList' :: Tree a -> [a]
-- toList' (Node _ x []) = [x]
-- toList' (Node _ x ts) = x : concatMap toList' ts

-- ----------------------------------------------------------------

-- {-| Finding the minimum element. Worst-case: O(log N), amortized: O(log N)

-- >>> minimum (fromList [3,5,1])
-- Just 1
-- >>> minimum empty
-- Nothing
-- -}

-- minimum :: Ord a => Heap a -> Maybe a
-- minimum (Heap ts) = root . fst <$> deleteMin' ts

-- ----------------------------------------------------------------

-- {-| Deleting the minimum element. Worst-case: O(log N), amortized: O(log N)

-- >>> deleteMin (fromList [5,3,7]) == fromList [5,7]
-- True
-- >>> deleteMin empty == empty
-- True
-- -}

-- deleteMin :: Ord a => Heap a -> Heap a
-- deleteMin (Heap ts) = case deleteMin' ts of
--     Nothing                  -> empty
--     Just (Node _ _ ts1, ts2) -> Heap (merge' (reverse ts1) ts2)

-- deleteMin2 :: Ord a => Heap a -> Maybe (a, Heap a)
-- deleteMin2 (Heap []) = Nothing
-- deleteMin2 h         = (\m -> (m, deleteMin h)) <$> minimum h

-- deleteMin' :: Ord a => [Tree a] -> Maybe (Tree a, [Tree a])
-- deleteMin' []     = Nothing
-- deleteMin' [t]    = Just (t,[])
-- deleteMin' (t:ts)
--   | root t < root t' = Just (t,  ts)
--   | otherwise        = Just (t', t:ts')
--   where
--     Just (t',ts')    = deleteMin' ts

-- ----------------------------------------------------------------
-- {-| Merging two heaps. Worst-case: O(log N), amortized: O(log N)

-- >>> merge (fromList [5,3]) (fromList [5,7]) == fromList [3,5,5,7]
-- True
-- -}

-- merge :: Ord a => Heap a -> Heap a -> Heap a
-- merge (Heap ts1) (Heap ts2) = Heap (merge' ts1 ts2)

-- merge' :: Ord a => [Tree a] -> [Tree a] -> [Tree a]
-- merge' ts1 [] = ts1
-- merge' [] ts2 = ts2
-- merge' ts1@(t1:ts1') ts2@(t2:ts2')
--   | rank t1 < rank t2 = t1 : merge' ts1' ts2
--   | rank t2 < rank t1 = t2 : merge' ts1 ts2'
--   | otherwise         = insert' (link t1 t2) (merge' ts1' ts2')

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
