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
{-@ type Bounded a X = {n : a | X <= n } @-}
{-@ data Skew a = Leaf | Node (root :: a) (left :: Skew (Bounded a root)) (right :: Skew (Bounded a root)) @-}
data Skew a = Leaf | Node a (Skew a) (Skew a) deriving Show


-- -- instance (Eq a, Ord a) => Eq (Skew a) where
-- --     h1 == h2 = heapSort h1 == heapSort h2

-- -- ----------------------------------------------------------------

-- -- {-| Empty heap.
-- -- -}

{-@ empty :: {r: Skew a | size r = 0 && elts r = S.empty}@-}
empty :: Skew a
empty = Leaf

-- -- {-|
-- -- See if the heap is empty.

-- -- >>> Data.Heap.Skew.null empty
-- -- True
-- -- >>> Data.Heap.Skew.null (singleton 1)
-- -- False
-- -- -}

-- -- null :: Skew t -> Bool
-- -- null Leaf         = True
-- -- null (Node _ _ _) = False

-- -- {-| Singleton heap.
-- -- -}

{-@ singleton :: x:a -> {r: Skew a | size r = 1 && elts r = S.singleton x } @-}
singleton :: a -> Skew a
singleton x = Node x Leaf Leaf

-- -- ----------------------------------------------------------------

-- -- {-| Insertion.

-- -- >>> insert 7 (fromList [5,3]) == fromList [3,5,7]
-- -- True
-- -- >>> insert 5 empty            == singleton 5
-- -- True
-- -- -}

{-@ insert :: x:a -> s:(Skew a) -> {r: Skew a | size r = 1 + size s && elts r = S.union (elts s) (S.singleton x)} @-}
insert :: Ord a => a -> Skew a -> Skew a
insert x t = merge (singleton x) t

-- -- ----------------------------------------------------------------

-- -- {-| Creating a heap from a list.

-- -- >>> empty == fromList []
-- -- True
-- -- >>> singleton 'a' == fromList ['a']
-- -- True
-- -- >>> fromList [5,3] == fromList [5,3]
-- -- True
-- -- -}
{-@ fromList :: l:[a] -> {r: Skew a | size r = len l && elts r = S.fromList l} @-}
fromList :: Ord a => [a] -> Skew a
fromList [] = Leaf
fromList (x : xs) = insert x (fromList xs)

-- -- ----------------------------------------------------------------

-- -- {-| Creating a list from a heap. O(N)

-- -- >>> let xs = [5,3,5]
-- -- >>> length (toList (fromList xs)) == length xs
-- -- True
-- -- >>> toList empty
-- -- []
-- -- -}

-- {-@ app :: l1:[a] -> l2:[a] -> {r: [a] | eltsList r = S.union (eltsList l1) (eltsList l2)} @-}
-- app :: [a] -> [a] -> [a]
-- app [] l2 = l2
-- app (x:t) l2 = x : (app t l2)

-- {-@ toList :: s:(Skew a) ->  {l: [a] | len l = size s && elts s = eltsList l} @-}
-- toList :: Skew a -> [a]
-- toList Leaf = []
-- toList (Node x l r) = app (toList l) (x : (toList r))
    
--      inorder t []
--   where
--     inorder Leaf xs         = xs
--     inorder (Node x l r) xs = inorder l (x : inorder r xs)

-- -- ----------------------------------------------------------------

-- -- {-| Finding the minimum element.

-- -- >>> minimum (fromList [3,5,1])
-- -- Just 1
-- -- >>> minimum empty
-- -- Nothing
-- -- -}

{-@ type Nat = Bounded Int 0 @-}

{-@ measure size @-}
{-@ size :: Skew a -> Nat @-}
size :: Skew a -> Int
size Leaf = 0
size (Node _ l r) = 1 + size l + size r

{-@ measure minimum @-}
{-@minimum :: {s:Skew a | 0 < size s} -> a @-}
minimum :: Skew a -> a
minimum (Node x _ _) = x

-- -- ----------------------------------------------------------------

-- -- {-| Deleting the minimum element.

-- -- >>> deleteMin (fromList [5,3,7]) == fromList [5,7]
-- -- True
-- -- >>> deleteMin empty == empty
-- -- True
-- -- -}

{-@deleteMin ::  {s: Skew a | 0 < size s} -> {r: Skew a | size r + 1 = size s} @-}
deleteMin :: Ord a => Skew a -> Skew a
deleteMin t@(Node _ _ _) = snd (deleteMin2 t)

--difference property does not work because the min could appear multiple times in the heap
{-@ deleteMin2 :: {s: Skew a | 0 < size s} -> {r: (a, Skew {x: a | fst(r) <= x}) | size (snd r) + 1 = size s && S.union (elts (snd r)) (S.singleton (fst r)) = elts s} @-}
deleteMin2 :: Ord a => Skew a -> (a, Skew a)
deleteMin2 (Node x l r)    = (x, merge l r)

-- -- ----------------------------------------------------------------
-- -- {-| Merging two heaps

-- -- >>> merge (fromList [5,3]) (fromList [5,7]) == fromList [3,5,5,7]
-- -- True
-- -- -}

{-@ measure elts @-}
{-@ elts :: Skew a -> Set a @-}
elts :: (Ord a) => Skew a -> Set a
elts Leaf = S.empty
elts (Node rt l r) = S.union (S.union (S.singleton rt) (elts l)) (elts r)

{-@ measure eltsList @-}
{-@ eltsList :: [a] -> Set a @-}
eltsList :: Ord a => [a] -> Set a 
eltsList [] = S.empty
eltsList (x : xs) = S.union (S.singleton x) (eltsList xs)

{-@ predicate EqElts X Y = ((elts X) = (elts Y)) @-}
{-@ type HeapS a S = {v:Skew a | elts v = S} @-}
--{-@ type HeapUn R X Y = EqElts (elts R) (S.union (elts X) (elts Y)) @-}

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ skewBoundedByRoot :: {s:(Skew a) | 0 < size s} -> {r : Skew (Bounded a (minimum s)) | size s = size r && EqElts s r} @-}
skewBoundedByRoot :: Skew a -> Skew a
skewBoundedByRoot (Node rt l r) = Node rt l r

{-@ boundedSkewTransitive :: x:a -> s:(Skew (Bounded a x)) -> {y: a | y <= x} -> {r : Skew (Bounded a y) | size s = size r && EqElts s r} @-}
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

-- -- ----------------------------------------------------------------
-- -- -- Basic operations
-- -- ----------------------------------------------------------------

-- -- {-| Checking validity of a heap.
-- -- -}

-- -- valid :: Ord a => Skew a -> Bool
-- -- valid t = isOrdered (heapSort t)

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ heapSort :: s:(Skew a) -> {v: IncrList a | len v = size s} / [size s] @-}
heapSort :: Ord a => Skew a -> [a]
heapSort Leaf = []
heapSort h@(Node _ _ _) =
    let (minElt, h') = deleteMin2 h in
        minElt : heapSort h'

-- -- isOrdered :: Ord a => [a] -> Bool
-- -- isOrdered [] = True
-- -- isOrdered [_] = True
-- -- isOrdered (x:y:xys) = x <= y && isOrdered (y:xys) -- allowing duplicated keys