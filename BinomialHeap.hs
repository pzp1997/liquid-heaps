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

import Prelude hiding (minimum, maximum, null)
import qualified Data.List as List
import qualified Data.Set as S
import Data.Set (Set)

{-@ type AtLeast X = {v:Int | X <= v} @-}
{-@ type Nat = AtLeast 0 @-}
{-@ type Pos = AtLeast 1 @-}

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ measure sumSizeList @-}
{-@ sumSizeList :: xs:[Tree a] -> {v:Nat | len xs <= v} @-}
sumSizeList :: [Tree a] -> Int
sumSizeList [] = 0
sumSizeList (x:xs) = size x + sumSizeList xs

{-@ measure heapSize @-}
{-@ heapSize :: h:(Heap a) -> {v:Nat | len (unheap h) <= v} @-}
heapSize :: Heap a -> Int
heapSize (Heap ts) = sumSizeList ts

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

{-@ type NEHeap a = {h:Heap a | 0 < len (unheap h)} @-}

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

{-@ boundedTreeListTransitivityLemma :: x:a -> {y:a | x <= y} -> ts:[BoundedTree a y] -> {v:[BoundedTree a x] | sumSizeList v == sumSizeList ts} @-}
boundedTreeListTransitivityLemma :: a -> a -> [Tree a] -> [Tree a]
boundedTreeListTransitivityLemma x y ts = ts

{-@ sublistSizeLemma :: t:(Tree a) -> ts:[Tree a] -> {v: Nat | v = size t + sumSizeList ts && sumSizeList ts < v } @-}
sublistSizeLemma :: Tree a -> [Tree a] -> Int
sublistSizeLemma x xs =
  assert (0 < size x) $
  sumSizeList (x : xs)

{-@ type BoundedSizeTree a X = {t : Tree a | size t <= X}  @-}
{-@ type BoundedSizeTrees a X = [BoundedSizeTree a X]  @-}

{-@ subtreeTransitiveLemma :: x:Nat  -> BoundedSizeTrees a x -> {y: Nat | x <= y} -> BoundedSizeTrees a y @-}
subtreeTransitiveLemma :: Int -> [Tree a] -> Int -> [Tree a]
subtreeTransitiveLemma _ ts _ = ts

{-@ consTreeLemma :: x:Nat ->BoundedSizeTree a x -> BoundedSizeTrees a x -> BoundedSizeTrees a x @-}
consTreeLemma ::Int -> Tree a -> [Tree a] -> [Tree a]
consTreeLemma _ t ts = t : ts

{-@ testTrick :: x:Nat -> {ts:(BoundedSizeTreesStrict a x) | ts != [] } -> {t: Tree a | size t < x} @-}
testTrick :: Int -> [Tree a] -> Tree a
testTrick _ (h:tl) = h

{-@ boundedSizeSubtreeLemma :: l:[Tree a] -> BoundedSizeTrees a (sumSizeList l) @-}
boundedSizeSubtreeLemma :: [Tree a] -> [Tree a]
boundedSizeSubtreeLemma [] = []
boundedSizeSubtreeLemma (t : ts) =
  let ih = boundedSizeSubtreeLemma ts in
  let sizetts = sublistSizeLemma t ts in
  let sizets = sumSizeList ts in
  let refinedSubtrees = subtreeTransitiveLemma sizets ih sizetts in
  consTreeLemma sizetts t refinedSubtrees
-- instance (Eq a, Ord a) => Eq (Heap a) where
--     h1 == h2 = heapSort h1 == heapSort h2
-- | sumSizeList l = sumSizeList v

-- {-@ measure elts @-}
-- {-@ elts :: Heap a -> Set a @-}
-- elts :: (Ord a) => Heap a -> Set a
-- elts (Heap (t1:ts)) = eltsTree t1


-- elts (Heap []) = S.empty
-- elts (Heap (t1:ts)) = List.foldl' (\acc t -> S.union (eltsTree t) acc) S.empty (t1:ts)

-- {-@ measure eltsTree @-}
-- {-@ eltsTree :: t:(Tree a) -> Set a / [size t] @-}
-- eltsTree :: (Ord a) => Tree a -> Set a
-- eltsTree (Node r x ts _) = S.singleton x
-- eltsTree (Node r x (t:ts) sz) =
--   let remainder = Node r x ts (sz - size t) in
--   S.union (S.union (S.singleton x) (eltsTree t)) (eltsTree remainder)

{-@ type BoundedSizeTreeStrict a X = {t : Tree a | size t < X}  @-}
{-@ type BoundedSizeTreesStrict a X = [BoundedSizeTreeStrict a X]  @-}

{-@ strictTransitivitySizeBoundLemma ::  x:Nat -> ts: ([BoundedSizeTree a x]) -> {y: Nat | x < y} -> [BoundedSizeTreeStrict a y] @-}
strictTransitivitySizeBoundLemma :: Int -> [Tree a] -> Int -> [Tree a]
strictTransitivitySizeBoundLemma _ ts _ = ts

{-@ lazy eltsTree @-}
{-@ eltsTree :: t:(Tree a) -> Set a / [size t] @-}
eltsTree :: (Ord a) => Tree a -> Set a
eltsTree t@(Node r x ts sz) =
  let boundBySumSizeList = (boundedSizeSubtreeLemma ts) in
  let boundByOverallSize = strictTransitivitySizeBoundLemma (sumSizeList ts) boundBySumSizeList (size t) in
--  assert (sz == 1 + sum (map size ts)) $
  assert (sumSizeList ts < size t) $
  List.foldl' S.union (S.singleton x) (map eltsTree boundByOverallSize)

-- {-@ predicate EqElts X Y = ((elts X) = (elts Y)) @-}
-- {-@ type HeapS a S = {v:[a] | elts v = S} @-}

----------------------------------------------------------------

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ assertBoundedTree :: x:a -> BoundedTree a x -> b -> b @-}
assertBoundedTree :: a -> Tree a -> b -> b
assertBoundedTree _ _ x = x

{-@ assertBoundedTreeList :: x:a -> [BoundedTree a x] -> b -> b @-}
assertBoundedTreeList :: a -> [Tree a] -> b -> b
assertBoundedTreeList _ _ x = x

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

{-| Creating a list from a heap. Worst-case: O(N) -}

-- {-@ toList :: Ord a => Heap a -> [a] @-}
-- toList :: Ord a => Heap a -> [a]
-- toList h =
--   case deleteMin2 h of
--     Just (x, h) -> x : toList h
--     Nothing -> []

-- {-@ type SubtreeList a X = > @-}

-- {-@ subtreesChildrenAreSmaller :: Tree a -> ts:([Tree a]<{\x -> size x <= sumSizeList ts}>) @-}
-- subtreesChildrenAreSmaller :: Tree a -> [Tree a]
-- subtreesChildrenAreSmaller t = subtrees t
  -- case subtrees t of
  --   [] -> []
  --   (s:ss) -> subtreesChildrenAreSmaller s : concatMap subtreesChildrenAreSmaller ss

-- sumSizeList (subtrees t) < size t
-- ts:([Tree a]<{\t -> size t <= sumSizeList ts}>)

-- {-@ data [a]<p :: Int -> Bool> = KV { keyVals :: [(Int<p>, v)] } @-}
-- data Assoc v = KV [(Int, v)]


-- {-@ toList :: Ord a => Heap a -> [a] @-}
-- toList :: Heap a -> [a]
-- toList (Heap ts) = concatMap toList' ts

-- {-@ toList' :: t:Tree a -> [a] / [size t] @-}
-- toList' :: Tree a -> [a]
-- toList' (Node _ x [] _) = [x]
-- toList' (Node _ x ts _) = x : concatMap toList' ts

{-| Finding the minimum element. Worst-case: O(log N), amortized: O(log N) -}

{-@ minimum :: NEHeap a -> a @-}
minimum :: Ord a => Heap a -> a
minimum = root . fst . deleteMin' . unheapNonempty

{-| Deleting the minimum element. Worst-case: O(log N), amortized: O(log N) -}

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

{-@ deleteMin2 :: h:NEHeap a -> {v:(a, Heap {x:a | (fst v) <= x}) | 1 + heapSize (snd v) == heapSize h} @-}
deleteMin2 :: Ord a => Heap a -> (a, Heap a)
deleteMin2 h =
  let (Node _ minElt ts1 _, ts2) = deleteMin' (unheapNonempty h) in
  (minElt, Heap (merge' (reverseHeapList ts1) ts2))

{-@ deleteMin' :: {xs:[Tree a] | 0 < len xs} -> {v:(Tree a, [BoundedTree a (root (fst v))]) | size (fst v) + sumSizeList (snd v) == sumSizeList xs} @-}
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

-- {-@ valid :: Ord a => Heap a -> {v:Bool | v} @-}
-- valid :: Ord a => Heap a -> Bool
-- valid t = isOrdered (heapSort t)

-- TODO prove that the elements are the same
{-@ heapSort :: h:(Heap a) -> {v:IncrList a | len v == heapSize h} / [heapSize h] @-}
heapSort :: Ord a => Heap a -> [a]
heapSort (Heap []) = []
heapSort h@(Heap (_:_)) =
  let (minElt, h') = deleteMin2 h in
  minElt : heapSort h'

{-@ sortUsingHeap :: xs:[a] -> {v:IncrList a | len v == len xs} @-}
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
