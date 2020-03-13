{-|
  Binominal Heap

  - Purely Functional Data Structures
-}

-- Drop module qualifers from pretty-printed names
{-@ LIQUID "--short-names" @-}
-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
-- Disable ADTs (only used with exactDC)
{-@ LIQUID "--no-adt" @-}

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

import Prelude hiding (minimum, maximum, null)
import Language.Haskell.Liquid.Prelude
import qualified Data.List as List
import qualified Data.Set as S
import Data.Set (Set)

{-@ type AtLeast a X = {n:a | X <= n} @-}
{-@ type Pos = GeInt 1 @-}
{-@ type NEList a = {xs:[a] | 0 < len xs} @-}
{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ measure treeListSize @-}
{-@ treeListSize :: xs:[Tree a] -> {v:Nat | (len xs <= v) && (v = 0 <=> len xs = 0)} @-}
treeListSize :: [Tree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = size x + treeListSize xs

-- unionEltsList :: [Tree a] -> Set a
-- unionEltsList [] = S.empty
-- unionEltsList (x:xs) = S.union (heapElts x) (unionEltsList xs)

{-@ measure maxRankList @-}
{-@ maxRankList :: [Tree a] -> Nat @-}
maxRankList :: [Tree a] -> Int
maxRankList [] = 0
maxRankList (x:xs) =
  let r = rank x in
  let r' = maxRankList xs in
  if r < r' then r' else r

{-@ measure lubRank @-}
{-@ lubRank :: xs:[Tree a] -> {v:Nat |
                                (0 = len xs) => (v = 0) &&
                                (0 < len xs) => (v = maxRankList xs + 1)
                              }
@-}
lubRank :: [Tree a] -> Int
lubRank [] = 0
lubRank ts = 1 + maxRankList ts

{-@ measure heapSize @-}
{-@ heapSize :: h:Heap a -> {v:Nat | (len (unheap h) <= v) && (v = treeListSize (unheap h))} @-}
-- {-@ heapSize :: h:(Heap a) -> {v:Nat | (len (unheap h) <= v) && (v = 0 <=> len (unheap h) = 0)} @-}
heapSize :: Heap a -> Int
heapSize (Heap ts) = treeListSize ts

{-@ reflect pow2 @-}
{-@ pow2 :: Nat -> Pos @-}
pow2 :: Int -> Int
pow2 n = if n == 0 then 1 else 2 * pow2 (n - 1)

-- TODO We'd like to say rank :: {v:Nat | v = lubRank subtrees && v = len subtrees}
-- but we need more lemmas to make this go through in link
-- TODO We'd like to say that size = pow2 rank, but we need to strengthen some other things first
{-@ data Tree [size] a =
    Node
        { root :: a
        , subtrees :: [AtLeastTree a root]
        , rank :: {v:Nat | v = len subtrees}
        , size :: {v:Pos | v = 1 + treeListSize subtrees}
        }
@-}
data Tree a =
    Node
        { root :: a
        , subtrees :: [Tree a]
        , rank :: Int
        , size :: Int
        }
    deriving (Eq)

-- | Trees with value at least X
{-@ type AtLeastTree a X = Tree (AtLeast a X) @-}
{-@ data Heap a = Heap { unheap :: [Tree a] } @-}
data Heap a = Heap { unheap :: [Tree a] }

{-@ type NEHeap a = {h:Heap a | 0 < len (unheap h)} @-}

{-@ type NESet a = {s:Set a | s != S.empty} @-}
-- {-@ predicate EqElts X Y = ((elts X) = (elts Y)) @-}
-- {-@ type HeapS a S = {v:[a] | elts v = S} @-}

instance (Eq a, Ord a) => Eq (Heap a) where
  h1 == h2 = heapSort h1 == heapSort h2

-- TODO maybe use self-invariants to encode this
{-@ treeIsBoundedByItsRootLemma :: t:(Tree a) -> {v:AtLeastTree a (root t) | treeElts v = treeElts t && size v = size t} @-}
treeIsBoundedByItsRootLemma :: Tree a -> Tree a
treeIsBoundedByItsRootLemma (Node {rank=r, root=x, subtrees=ts, size=sz}) =
  Node {rank=r, root=x, subtrees=ts, size=sz}

-- TODO double check if we need this lemma
{-@ boundedTreeTransitivityLemma :: x:a -> {y:a | x <= y} -> t:AtLeastTree a y ->
  {v:AtLeastTree a x | treeElts v = treeElts t && size v = size t} @-}
boundedTreeTransitivityLemma :: a -> a -> Tree a -> Tree a
boundedTreeTransitivityLemma x y tree = tree

{-@ boundedTreeListTransitivityLemma :: x:a -> {y:a | x <= y} -> ts:[AtLeastTree a y] ->
  {v:[AtLeastTree a x] | treeListElts v = treeListElts ts && treeListSize v = treeListSize ts}
@-}
boundedTreeListTransitivityLemma :: a -> a -> [Tree a] -> [Tree a]
boundedTreeListTransitivityLemma x y ts = ts

{- Elements measures -}

{-@ measure heapElts @-}
{-@ heapElts :: h:Heap a -> {v:Set a | v = treeListElts (unheap h)} @-}
-- {-@ heapElts :: h:Heap a -> {v:Set a | v = S.empty <=> len (unheap h) = 0
--                                     && v = treeListElts (unheap h)} @-}
heapElts :: (Ord a) => Heap a -> Set a
-- heapElts (Heap []) = S.empty
heapElts (Heap ts) = treeListElts ts

{-@ measure treeListElts @-}
{-@ treeListElts :: ts:[Tree a] -> Set a @-}
-- {-@ treeListElts :: ts:[Tree a] -> {v:Set a | v = S.empty <=> len ts = 0} @-}
treeListElts :: (Ord a) => [Tree a] -> Set a
treeListElts [] = S.empty
treeListElts (t:ts) = S.union (treeElts t) (treeListElts ts)

{-@ measure treeElts @-}
{-@ treeElts :: t:Tree a -> NESet a @-}
treeElts :: Ord a => Tree a -> Set a
treeElts (Node x [] _ _) = S.singleton x
treeElts (Node x (t:ts) r sz) =
  let remainder = Node x ts (r - 1) (sz - size t) in
  S.union (treeElts t) (treeElts remainder)

{-@ measure listElts @-}
{-@ listElts :: [a] -> Set a @-}
listElts :: Ord a => [a] -> Set a
listElts [] = S.empty
listElts (x : xs) = S.union (S.singleton x) (listElts xs)

{-@ predicate EltsSize S X Y = (heapElts S = X && heapSize S = Y) @-}

----------------------------------------------------------------

{-@ assert :: TT -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

-- {-@ assertAtLeastTree :: x:a -> AtLeastTree a x -> b -> b @-}
-- assertAtLeastTree :: a -> Tree a -> b -> b
-- assertAtLeastTree _ _ x = x

-- {-@ assertAtLeastTreeList :: x:a -> [AtLeastTree a x] -> b -> b @-}
-- assertAtLeastTreeList :: a -> [Tree a] -> b -> b
-- assertAtLeastTreeList _ _ x = x

{-@ link :: t1:(Tree a) -> t2:(Tree a) ->
  {v:Tree a | treeElts v = S.union (treeElts t1) (treeElts t2)
           && size v = size t1 + size t2}
@-}
link :: Ord a => Tree a -> Tree a -> Tree a
link t1@(Node x1 ts1 r1 sz1) t2@(Node x2 ts2 r2 sz2)
  | x1 <= x2  =
    let t2BoundedByX2 = treeIsBoundedByItsRootLemma t2 in
    let t2BoundedByX1 = boundedTreeTransitivityLemma x1 x2 t2BoundedByX2 in
    Node x1 (t2BoundedByX1:ts1) (1 + r1) (sz1 + sz2)
  | otherwise =
    let t1BoundedByX1 = treeIsBoundedByItsRootLemma t1 in
    let t1BoundedByX2 = boundedTreeTransitivityLemma x2 x1 t1BoundedByX1 in
    Node x2 (t1BoundedByX2:ts2) (1 + r2) (sz1 + sz2)

{-@ empty :: {v:Heap a | EltsSize v S.empty 0} @-}
empty :: Heap a
empty = Heap []

-- {-@ null :: h:(Heap a) -> {v:Bool | v <=> heapElts h = S.empty} @-}
{-@ null :: h:(Heap a) -> {v:Bool | v <=> heapSize h == 0} @-}
null :: Heap a -> Bool
null h = heapSize h == 0

{-@ singleton :: x:a -> {v:Heap a | EltsSize v (S.singleton x) 1} @-}
singleton :: Ord a => a -> Heap a
singleton x = Heap [Node x [] 0 1]

{-| Insertion. Worst-case: O(log N), amortized: O(1)

Properties we would like to verify:
  1. well-formed
  2. increases length by 1
  3. elements we would expect
-}

-- {-@ insert :: x:a -> h:Heap a -> {v:Heap a | EltsSize v (S.union (S.singleton x) (heapElts h)) (1 + heapSize h)} @-}
{-@ insert :: x:a -> h:Heap a ->
  {v:Heap a | EltsSize v (S.union (S.singleton x) (heapElts h)) (1 + heapSize h)} @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x (Heap ts) = Heap (insert' (Node x [] 0 1) ts)

{-@ insert' :: t:Tree a -> ts:[Tree a] ->
  {v:[Tree a] | treeListElts v = S.union (treeElts t) (treeListElts ts)
             && treeListSize v = size t + treeListSize ts}
@-}
insert' :: Ord a => Tree a -> [Tree a] -> [Tree a]
insert' t [] = [t]
insert' t ts@(t':ts')
  | rank t < rank t' = t : ts
  | otherwise        = insert' (link t t') ts'

{-@ fromList :: xs:[a] -> {v:Heap a | heapElts v = listElts xs && heapSize v = len xs} @-}
fromList :: Ord a => [a] -> Heap a
fromList [] = empty
fromList (x:xs) = insert x (fromList xs)

-- ----------------------------------------------------------------

{-| Creating a list from a heap. Worst-case: O(N) -}

-- TODO encode elt information in type
{-@ toList :: h:Heap a -> {v:[a] | len v = heapSize h} @-}
toList :: Heap a -> [a]
toList (Heap ts) = treeListToList ts

{-@ treeListToList :: ts:[Tree a] -> {v:[a] | len v = treeListSize ts} @-}
treeListToList :: [Tree a] -> [a]
treeListToList [] = []
treeListToList (t:ts) = treeToList t ++ treeListToList ts

{-@ treeToList :: t:Tree a -> {v:[a] | len v = size t} @-}
-- {-@ treeToList :: t:Tree a -> {v:[a] | listElts v = treeElts t && len v = size t} @-}
treeToList :: Tree a -> [a]
treeToList (Node x [] _ _) = [x]
treeToList (Node x (t:ts) r sz) =
  let remainder = Node x ts (r - 1) (sz - size t) in
  treeToList t ++ treeToList remainder

{-| Finding the minimum element. Worst-case: O(log N), amortized: O(log N) -}

-- TODO encode elt information in type
{-@ minimum :: NEHeap a -> a @-}
minimum :: Ord a => Heap a -> a
minimum = root . fst . deleteMin' . unheapNonempty

{-| Deleting the minimum element. Worst-case: O(log N), amortized: O(log N) -}

{-@ reverseHeapList :: ts:[Tree a] -> {v:[Tree a] | treeListElts v = treeListElts ts && treeListSize v = treeListSize ts} @-}
reverseHeapList :: [Tree a] -> [Tree a]
reverseHeapList ts = reverseHeapListAux ts []

{-@ reverseHeapListAux :: ts:[Tree a] -> acc:[Tree a] ->
  {v:[Tree a] |
    treeListElts v = S.union (treeListElts ts) (treeListElts acc) &&
    treeListSize v = treeListSize ts + treeListSize acc}
@-}
reverseHeapListAux :: [Tree a] -> [Tree a] -> [Tree a]
reverseHeapListAux [] acc = acc
reverseHeapListAux (t:ts) acc = reverseHeapListAux ts (t:acc)

{-@ unheapNonempty :: h:(NEHeap a) -> {v:NEList (Tree a) | EltsSize h (treeListElts v) (treeListSize v)} @-}
unheapNonempty :: Heap a -> [Tree a]
unheapNonempty (Heap ts@(_:_)) = ts

-- TODO encode elt information in type
{-@ deleteMin :: h:(NEHeap a) -> {v:Heap a | 1 + heapSize v = heapSize h} @-}
deleteMin :: Ord a => Heap a -> Heap a
deleteMin h =
  let (Node _ ts1 _ _, ts2) = deleteMin' (unheapNonempty h) in
  Heap (merge' (reverseHeapList ts1) ts2)

-- TODO encode elt information in type
{-@ deleteMin2 :: h:NEHeap a -> (e::a, {v:Heap {x:a | e <= x} | 1 + heapSize v = heapSize h}) @-}
-- {-@ deleteMin2 :: h:NEHeap a -> (e::a, {v:Heap {x:a | e <= x} | S.union (S.singleton e) (heapElts v) = heapElts h && 1 + heapSize v = heapSize h}) @-}
deleteMin2 :: Ord a => Heap a -> (a, Heap a)
deleteMin2 h =
  let (Node minElt ts1 _ _, ts2) = deleteMin' (unheapNonempty h) in
  (minElt, Heap (merge' (reverseHeapList ts1) ts2))

{-@ deleteMin' :: xs:(NEList (Tree a)) ->
  {v:(Tree a, [AtLeastTree a (root (fst v))]) |
    S.union (treeElts (fst v)) (treeListElts (snd v)) = treeListElts xs &&
    size (fst v) + treeListSize (snd v) = treeListSize xs}
@-}
deleteMin' :: Ord a => [Tree a] -> (Tree a, [Tree a])
deleteMin' [t] = (t, [])
deleteMin' (t:ts) =
  let (t', ts') = deleteMin' ts in
  let x = root t in
  let x' = root t' in
  let tBounded = treeIsBoundedByItsRootLemma t in
  let tBounded' = treeIsBoundedByItsRootLemma t' in
  if x < x'
  then
    let hd = boundedTreeTransitivityLemma x x' tBounded' in
    let tl = boundedTreeListTransitivityLemma x x' ts' in
    (t, hd:tl)
  else
    let hd = boundedTreeTransitivityLemma x' x tBounded in
    (t', hd:ts')

{-| Merging two heaps. Worst-case: O(log N), amortized: O(log N)

Properties to verify
1. well-formedness
2. sum of counts of all elements from both should be in both
-}

{-@ merge :: h1:Heap a -> h2:Heap a ->
  {v:Heap a | EltsSize v (S.union (heapElts h1) (heapElts h2)) (heapSize h1 + heapSize h2)} @-}
merge :: Ord a => Heap a -> Heap a -> Heap a
merge (Heap ts1) (Heap ts2) = Heap (merge' ts1 ts2)

{-@ merge' :: ts1:[Tree a] -> ts2:[Tree a] ->
  {v:[Tree a] | treeListElts v = S.union (treeListElts ts1) (treeListElts ts2)
             && treeListSize v = treeListSize ts1 + treeListSize ts2} @-}
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

-- {-@ valid :: Heap a -> TT @-}
-- valid :: Ord a => Heap a -> Bool
-- valid t = isOrdered (heapSort t)

-- TODO prove that the elements are the same
{-@ heapSort :: h:(Heap a) -> {v:IncrList a | len v = heapSize h} / [heapSize h] @-}
heapSort :: Ord a => Heap a -> [a]
heapSort (Heap []) = []
heapSort h@(Heap (_:_)) =
  let (minElt, h') = deleteMin2 h in
  minElt : heapSort h'

-- TODO prove that the elements are the same
{-@ sortUsingHeap :: xs:[a] -> {v:IncrList a | len v = len xs} @-}
sortUsingHeap :: Ord a => [a] -> [a]
sortUsingHeap = heapSort . fromList


-- {-@ measure isOrdered @-}
-- {-@ isOrdered :: [a] -> Bool @-}
-- isOrdered :: Ord a => [a] -> Bool
-- isOrdered [] = True
-- isOrdered [x] = True
-- isOrdered (x:xs) = x <= (headNE xs) && isOrdered xs

-- {-@ measure headNE @-}
-- {-@ headNE :: {v:[a] | 0 < len v} -> a @-}
-- headNE :: [a] -> a
-- headNE (x:_) = x

-- {-@ isOrderedIfIncrList :: IncrList a -> {v:[a] | isOrdered v} @-}
