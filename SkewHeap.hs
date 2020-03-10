{-|
  Skew Heap

  - the fun of programming
-}

module Data.Heap.Skew where
--   -- * Data structures
--     Skew(..)
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
import qualified Data.Set as S
import Data.Set (Set)

----------------------------------------------------------------
{-@ type AtLeast a X = {v:a | X <= v} @-}
{-@ data Skew a = Leaf | Node (root :: a) (left :: Skew (AtLeast a root)) (right :: Skew (AtLeast a root)) @-}
data Skew a = Leaf | Node a (Skew a) (Skew a) deriving Show

-- -- ----------------------------------------------------------------

{- Working with sets (both lists and Heaps) -}

-- set of a heap
{-@ measure elts @-}
{-@ elts :: Skew a -> Set a @-}
elts :: (Ord a) => Skew a -> Set a
elts Leaf = S.empty
elts (Node rt l r) = S.union (S.singleton rt) (S.union (elts l) (elts r))

-- set of a list
{-@ measure eltsList @-}
{-@ eltsList :: [a] -> Set a @-}
eltsList :: Ord a => [a] -> Set a
eltsList [] = S.empty
eltsList (x : xs) = S.union (S.singleton x) (eltsList xs)

{-@ predicate EqElts X Y = ((elts X) = (elts Y)) @-}

-- assertions
{-@ assert :: TT -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{- Size of a heap -}

{-@ measure size @-}
{-@ size :: Skew a -> Nat @-}
size :: Skew a -> Int
size Leaf = 0
size (Node _ l r) = 1 + size l + size r

{-| Empty heap.-}

{-@ empty :: {r: Skew a | size r = 0 && elts r = S.empty}@-}
empty :: Skew a
empty = Leaf

{- See if the heap is empty.-}

{-@ null :: s:(Skew t) -> {b : Bool | b <=> size s = 0} @-}
null :: Skew t -> Bool
null Leaf         = True
null (Node _ _ _) = False

{-| Singleton heap.-}

{-@ singleton :: x:a -> {r: Skew a | size r = 1 && elts r = S.singleton x } @-}
singleton :: a -> Skew a
singleton x = Node x Leaf Leaf

----------------------------------------------------------------

{-| Insertion. -}

{-@ insert :: x:a -> s:(Skew a) -> {r: Skew a | size r = 1 + size s && elts r = S.union (elts s) (S.singleton x)} @-}
insert :: Ord a => a -> Skew a -> Skew a
insert x t = merge (singleton x) t

----------------------------------------------------------------

{-| Creating a heap from a list. -}
{-@ fromList :: l:[a] -> {r: Skew a | size r = len l && elts r = eltsList l} @-}
fromList :: Ord a => [a] -> Skew a
fromList [] = Leaf
fromList (x : xs) = insert x (fromList xs)

----------------------------------------------------------------

{-| Creating a list from a heap. Worst-case: O(N) -}

{-@ measure fst' @-}
fst' :: (a,b,c) -> a
fst' (x, _, _) = x

{-@ measure snd' @-}
snd' :: (a,b,c) -> b
snd' (_, x, _) = x

{-@ measure trd' @-}
trd' :: (a,b,c) -> c
trd' (_, _, x) = x

{-@ predicate EltsOfTriple X Y Z = (S.union (S.singleton X) (S.union Y Z)) @-}
{-@ predicate SizeOfTriple F X Y = (1 + (F X) + (F Y)) @-}

{-@ combineInorder :: x:a -> l1:[a] -> l2:[a] ->
    {r: [a] |
        eltsList r = EltsOfTriple x (eltsList l1) (eltsList l2) &&
        len r = SizeOfTriple len l1 l2
    }
@-}
combineInorder :: a -> [a] -> [a] -> [a]
combineInorder x [] l2 = x : l2
combineInorder x (h:t) l2 = h : combineInorder x t l2

{-@ destructNode :: {s: Skew a | 0 < size s} ->
    {v:(a, Skew a, Skew a) |
        elts s = EltsOfTriple (fst' v) (elts (snd' v)) (elts (trd' v)) &&
        size s = SizeOfTriple size (snd' v) (trd' v)
    }
@-}
destructNode :: Skew a -> (a, Skew a, Skew a)
destructNode (Node x l r) = (x, l, r)

{-@ toList :: s:(Skew a) -> {l: [a] | len l = size s && elts s = eltsList l} / [size s] @-}
toList :: Skew a -> [a]
toList Leaf = []
toList s =
    let (x', l', r') = destructNode s in
    combineInorder x' (toList l') (toList r')

----------------------------------------------------------------

{-| Finding the minimum element.-}

{-@ measure minimum @-}
{-@minimum :: {s:Skew a | 0 < size s} -> a @-}
minimum :: Skew a -> a
minimum (Node x _ _) = x

----------------------------------------------------------------

{-| Deleting the minimum element. -}

{-@deleteMin ::  {s: Skew a | 0 < size s} -> {r: Skew a | size r + 1 = size s} @-}
deleteMin :: Ord a => Skew a -> Skew a
deleteMin t@(Node _ _ _) = snd (deleteMin2 t)

--difference property does not work because the min could appear multiple times in the heap
{-@ deleteMin2 :: {s: Skew a | 0 < size s} -> {r: (a, Skew {x: a | fst(r) <= x}) | size (snd r) + 1 = size s && S.union (elts (snd r)) (S.singleton (fst r)) = elts s} @-}
deleteMin2 :: Ord a => Skew a -> (a, Skew a)
deleteMin2 (Node x l r)    = (x, merge l r)

----------------------------------------------------------------

{-| Merging two heaps-}

-- A nonempty skew heap is bounded by its root
{-@ skewBoundedByRoot :: {s:(Skew a) | 0 < size s} -> {r : Skew (AtLeast a (minimum s)) | size s = size r && EqElts s r} @-}
skewBoundedByRoot :: Skew a -> Skew a
skewBoundedByRoot (Node rt l r) = Node rt l r

-- Boundedness is transitive
{-@ boundedSkewTransitive :: x:a -> s:(Skew (AtLeast a x)) -> {y: a | y <= x} -> {r : Skew (AtLeast a y) | size s = size r && EqElts s r} @-}
boundedSkewTransitive :: a -> Skew a -> a -> Skew a
boundedSkewTransitive _ s _ = s

{-@ merge ::t1:(Skew a) -> t2:(Skew a) -> {r: Skew a | size r = size t1 + size t2 && ((elts r) = (S.union (elts t1) (elts t2)))}  /[size t1 + size t2] @-}
merge :: Ord a => Skew a -> Skew a -> Skew a
merge t1 Leaf = t1
merge Leaf t2 = t2
merge t1@(Node rt1 l1 r1) t2@(Node rt2 l2 r2) =
    if rt1 <= rt2 then
        Node rt1 r1 (merge l1 (boundedSkewTransitive rt2 (skewBoundedByRoot (Node rt2 l2 r2)) rt1))
    else Node rt2 r2 (merge l2 (boundedSkewTransitive rt1 (skewBoundedByRoot (Node rt1 l1 r1)) rt2))

----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

-- {-| Checking validity of a heap.
-- -}

-- valid :: Ord a => Skew a -> Bool
-- valid t = isOrdered (heapSort t)

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ heapSort :: s:(Skew a) -> {v:IncrList a | len v = size s && eltsList v = elts s} / [size s] @-}
heapSort :: Ord a => Skew a -> [a]
heapSort Leaf = []
heapSort h@(Node _ _ _) =
    let (minElt, h') = deleteMin2 h in
        minElt : heapSort h'

{-@ sortUsingHeap :: xs:[a] -> {v:IncrList a | len v = len xs && eltsList v = eltsList xs} @-}
sortUsingHeap :: Ord a => [a] -> [a]
sortUsingHeap = heapSort . fromList

-- isOrdered :: Ord a => [a] -> Bool
-- isOrdered [] = True
-- isOrdered [_] = True
-- isOrdered (x:y:xys) = x <= y && isOrdered (y:xys) -- allowing duplicated keys
