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

import Prelude hiding (minimum, maximum, null, head)
import Language.Haskell.Liquid.Prelude
import qualified Data.List as List
import qualified Data.Set as S
import Data.Set (Set)

{-@ type AtLeast a X = {n:a | X <= n} @-}
{-@ type Pos = GeInt 1 @-}
{-@ type NEList a = {xs:[a] | 0 < len xs} @-}
{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

--{-@ type IncrRankList a = [Tree a]<{\ti tj -> rank ti + 1 = rank tj}> @-}

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
pow2 n = if n == 0 then 1 else let x = pow2 (n - 1) in x + x

{-@ pow2Inj :: x:Nat -> {y:Nat | x > y} -> {t:(Nat, Nat) | fst t = x && snd t = y && pow2 (fst t) > pow2 (snd t)} @-}
pow2Inj :: Int -> Int -> (Int, Int) 
pow2Inj x y =
  if y == 0 then
    if x == 0 then (0, 0) else
      assert (y == 0) $
      assert (x > 0) $
      assert (pow2 x > 1) $
      assert (pow2 0 == 1) $
      assert (pow2 x > pow2 y) $
      (x, 0)
  else
  assert (pow2 x == pow2 (x -1) + pow2 (x-1) && pow2 y == pow2 (y-1) + pow2 (y-1)) $
  let (x', y') = pow2Inj (x-1) (y-1) in (x' + 1, y' + 1)

{-@ pow2InjB :: x:Nat -> {y:Nat | x > y} -> {b : Bool | b <=> pow2 x > pow2 y} @-}
pow2InjB :: Int -> Int -> Bool
pow2InjB x y =
  let (x', y') = pow2Inj x y in
  assert (pow2 x' > pow2 y') $
  assert (x == x') $
  assert (y == y') $
  True

{-@ measure rankOfSubtrees @-}
{-@ rankOfSubtrees :: [Tree a] -> Int @-}
rankOfSubtrees :: [Tree a] -> Int
rankOfSubtrees [] = 0
rankOfSubtrees (x : xs) = 1 + rank x

{-@ measure head @-}
{-@ head :: {l:[a] | len l > 0} -> a @-}
head :: [a] -> a
head (x : _) = x

-- {-@ nth :: l:[a] -> {x: Nat | 0 <= x && x < len l} -> {v: a | elem v l = true} @-}
-- nth :: [a] -> Int -> a
-- nth (x : xs) n = if n == 0 then x else nth xs (n-1)

-- TODO We'd like to say rank :: {v:Nat | v = lubRank subtrees && v = len subtrees}
-- but we need more lemmas to make this go through in link
-- TODO We'd like to say that size = pow2 rank, but we need to strengthen some other things first
{-@ data Tree [size] a =
    Node
        { root :: a
        , subtrees :: Subtrees a
        , rank :: {v:Nat | v = len subtrees && (0 < len subtrees => v - 1 = rank' (head subtrees))}
        , size :: {v:Pos | v = 1 + treeListSize subtrees && v = pow2 rank}
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

{-@ measure rank' @-}
{-@ rank' :: t:Tree a -> {v:Nat | v = len (subtrees t)} @-}
rank' :: Tree a -> Int
rank' (Node _ _ r _) = r

{-@ type Subtrees a = [AtLeastTree a root]<{\ti tj -> rank' ti = rank' tj + 1}> @-}

-- want to show that ith element of subtree has rank r - i


-- | Trees with value at least X
{-@ type AtLeastTree a X = Tree (AtLeast a X) @-}
{-@ data Heap a = Heap { unheap :: [Tree a] } @-}
data Heap a = Heap { unheap :: [Tree a] }

{-@ type NEHeap a = {h:Heap a | 0 < len (unheap h)} @-}
{-@ type NESet a = {s:Set a | s != S.empty} @-}

{-@ predicate LEltsSize H X Y = (listElts H = X && len H = Y) @-}
{-@ predicate TEltsSize T X Y = (treeElts T = X && size T = Y )@-}
{-@ predicate TsEltsSize Ts X Y = (treeListElts Ts = X && treeListSize Ts = Y) @-}
{-@ predicate HEltsSize H X Y = (heapElts H = X && heapSize H = Y) @-}

-- {-@ predicate EqElts X Y = ((elts X) = (elts Y)) @-}
-- {-@ type HeapS a S = {v:[a] | elts v = S} @-}

-- instance (Eq a, Ord a) => Eq (Heap a) where
--   h1 == h2 = heapSort h1 == heapSort h2

-- TODO maybe use self-invariants to encode this
-- {-@ treeAtLeastRoot :: t:Tree a ->
--   {v:AtLeastTree a (root t) | TEltsSize v (treeElts t) (size t)
--                            && root v = root t && rank v = rank t} @-}
-- treeAtLeastRoot :: Tree a -> Tree a
-- treeAtLeastRoot (Node x ts r sz) = Node x ts r sz


-- need to know that if rank is r, first subtree has rank r-1 (try, if not, then replace pow2 with 1 + rank of head is rank)




-- {-@ treeListRankTrans :: x:Int -> {y : Int | x < y} -> ts:[Tree a]<{\z -> rank z < x}> -> r:[Tree a]<{\z -> rank z < y}> @-}
-- treeListRankTrans :: Int -> Int -> [Tree a] -> [Tree a]
-- treeListRankTrans x y ts = ts

-- {-@ subtreesSmallerRanks :: t:(Tree a)  -> {r: [Tree a]<{\y -> rank y < rank t}> | subtrees t = r} @-}
-- subtreesSmallerRanks :: Tree a ->  [Tree a]
-- subtreesSmallerRanks (Node x [] r sz) = []
-- subtreesSmallerRanks (Node x (t : ts) r sz) =
--   let remainder = Node x ts (r-1) (sz - size t) in
--     assert (size t < sz) $
--     assert (size t == pow2 (rank t)) $
--     assert (sz == pow2 (r)) $
--     assert (pow2 (rank t) < pow2 r) $
--     assert (rank t < r || rank t > r || rank t == r) $
--     --cannot happen
--     if (rank t == r) then
--       assert (pow2 (rank t) == pow2 r) $ 
--       []
--     -- cannot happen
--     else if ((rank t) > r) then
--       -- let (rt', r') = pow2Inj (rank t) r in
--       -- assert (rt' == rank t) $
--       -- assert (r' == r) $
--       -- assert (pow2 rt' > pow2 r') $
--       -- assert (pow2 (rank t) > pow2 (r)) $
--       []
--     else 
--       assert (rank t < r) $
--       t: ts
--       -- assert (rank ( remainder) < r) $
--       -- t : treeListRankTrans (rank remainder) r (subtreesSmallerRanks remainder)

{- Elements measures -}

-- {-@ measure heapElts @-}
-- {-@ heapElts :: h:Heap a -> {v:Set a | v = treeListElts (unheap h)} @-}
-- -- {-@ heapElts :: h:Heap a -> {v:Set a | v = S.empty <=> len (unheap h) = 0
-- --                                     && v = treeListElts (unheap h)} @-}
-- heapElts :: (Ord a) => Heap a -> Set a
-- -- heapElts (Heap []) = S.empty
-- heapElts (Heap ts) = treeListElts ts

--{-@ measure treeListElts @-}
{-@ treeListElts :: ts:[Tree a] -> Set a @-}
-- {-@ treeListElts :: ts:[Tree a] -> {v:Set a | v = S.empty <=> len ts = 0} @-}
treeListElts :: (Ord a) => [Tree a] -> Set a
treeListElts [] = S.empty
treeListElts (t:ts) = S.union (treeElts t) (treeListElts ts)

--{-@ measure treeElts @-}
{-@ treeElts :: t:Tree a -> v:NESet a @-}
treeElts :: Ord a => Tree a -> Set a
treeElts (Node x [] _ _) = S.singleton x
treeElts (Node x [t] _ _) = S.union (S.singleton x) (treeElts t)
treeElts (Node x (t:ts@(_:_)) r sz) =
  -- let remainder = Node x (t':ts) (r - 1) (sz - size t) in
  -- assert (size remainder == sz - size t) $
  -- assert (size remainder >= 1) $
  -- assert (size remainder == pow2 (rank (remainder))) $
  -- assert (size remainder == pow2 (rank (remainder))) $
  -- assert (size remainder == 1 + treeListSize (t':ts)) $


  -- assert (0 < length (t:ts)) $
  -- assert (r - 1 == rank' (head (t:ts))) $
  -- assert (rank t == r - 1) $
  -- assert (size t == pow2 (r-1)) $
  -- assert (pow2 r == pow2 (r-1) + pow2 (r-1)) $
  -- assert (sz - size t == pow2 (r-1)) $
  -- assert (size remainder == pow2 (rank (remainder))) $
  -- assert (size remainder == 1 + treeListSize ts) $
  assert (treeListSize (subtrees t) == treeListSize (subtrees t)) $ 
  assert (treeListSize (t:ts) == size t + treeListSize ts) $
  --assert (1 + treeListSize (subtrees t) == size t) $
  -- assert (size remainder > 0) $
  assert (sz > size t) $
  S.union (treeElts t) (treeElts (Node x ts (r - 1) (sz - size t)))

  -- from type signature
  -- | v = S.union (S.singleton (root t)) (treeListElts (subtrees t))

-- {-@ measure reverseSubtrees @-}
-- {-@ reverseSubtrees :: t:Tree a -> {v:Tree a | size v = size t} @-}
-- reverseSubtrees :: Tree a -> Tree a
-- reverseSubtrees (Node x ts r sz) = Node x (reverseHeapList ts) r sz

-- {-@ reverseList :: xs:[a] -> {v:[a] | LEltsSize v (listElts xs) (len xs)} @-}
-- reverseList :: [a] -> [a]
-- reverseList xs = reverseListAux xs []

-- {-@ reverseListAux :: xs:[a] -> acc:[a] ->
--   {v:[a] | LEltsSize v (S.union (listElts xs) (listElts acc)) (len xs + len acc)} @-}
-- reverseListAux :: [a] -> [a] -> [a]
-- reverseListAux [] acc = acc
-- reverseListAux (x:xs) acc = reverseListAux xs (x:acc)

{-@ measure listElts @-}
{-@ listElts :: [a] -> Set a @-}
listElts :: Ord a => [a] -> Set a
listElts [] = S.empty
listElts (x : xs) = S.union (S.singleton x) (listElts xs)


----------------------------------------------------------------

{-@ assert :: TT -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ assertAtLeastTree :: x:a -> AtLeastTree a x -> b -> b @-}
assertAtLeastTree :: a -> Tree a -> b -> b
assertAtLeastTree _ _ x = x

{-@ assertAtLeastTreeList :: x:a -> [AtLeastTree a x] -> b -> b @-}
assertAtLeastTreeList :: a -> [Tree a] -> b -> b
assertAtLeastTreeList _ _ x = x

{-@ assertAtLeastHeap :: x:a -> Heap (AtLeast a x) -> b -> b @-}
assertAtLeastHeap :: a -> Heap a -> b -> b
assertAtLeastHeap _ _ x = x

-- {-@ link :: t1:Tree a -> t2:{v:Tree a | rank t1 = rank t2} ->
--   {v:Tree a | TEltsSize v (S.union (treeElts t1) (treeElts t2)) (size t1 + size t2)}
-- @-}
-- link :: Ord a => Tree a -> Tree a -> Tree a
-- link t1@(Node x1 ts1 r1 sz1) t2@(Node x2 ts2 r2 sz2)
--   | x1 <= x2  = liquidAssert (sz1 + sz1 == pow2 (r1 + 1)) $
--                 Node x1 ((treeAtLeastRoot t2):ts1) (1 + r1) (sz1 + sz2)
--   | otherwise = liquidAssert (sz2 + sz2 == pow2 (r2 + 1)) $
--                 Node x2 ((treeAtLeastRoot t1):ts2) (1 + r2) (sz1 + sz2)

-- {-@ empty :: {v:Heap a | HEltsSize v S.empty 0} @-}
-- empty :: Heap a
-- empty = Heap []

-- -- {-@ null :: h:(Heap a) -> {v:Bool | v <=> heapElts h = S.empty} @-}
-- {-@ null :: h:(Heap a) -> {v:Bool | v <=> heapSize h == 0} @-}
-- null :: Heap a -> Bool
-- null h = heapSize h == 0

-- {-@ singleton :: x:a -> {v:Heap a | HEltsSize v (S.singleton x) 1} @-}
-- singleton :: Ord a => a -> Heap a
-- singleton x =
--   liquidAssert (pow2 0 == 1) $
--   Heap [Node x [] 0 1]

-- {-| Insertion. Worst-case: O(log N), amortized: O(1)

-- Properties we would like to verify:
--   1. well-formed
--   2. increases length by 1
--   3. elements we would expect
-- -}

-- -- {-@ insert :: x:a -> h:Heap a -> {v:Heap a | HEltsSize v (S.union (S.singleton x) (heapElts h)) (1 + heapSize h)} @-}
-- {-@ insert :: x:a -> h:Heap a ->
--   {v:Heap a | HEltsSize v (S.union (S.singleton x) (heapElts h)) (1 + heapSize h)} @-}
-- insert :: Ord a => a -> Heap a -> Heap a
-- insert x (Heap ts) = liquidAssert (pow2 0 == 1) $ Heap (insert' (Node x [] 0 1) ts)

-- {-@ insert' :: t:Tree a -> ts:[Tree a] ->
--   {v:[Tree a] | TsEltsSize v (S.union (treeElts t) (treeListElts ts)) (size t + treeListSize ts) }
-- @-}
-- insert' :: Ord a => Tree a -> [Tree a] -> [Tree a]
-- insert' t [] = [t]
-- insert' t ts@(t':ts')
--   | rank t < rank t' = t : ts
--   -- I don't believe the following case can ever since the rank of subtrees
--   -- should be strictly increasing but we need it to satisfy Liquid Haskell
--   | rank t > rank t' = t' : t : ts'
--   | otherwise        = insert' (link t t') ts'

-- {-@ fromList :: xs:[a] -> {v:Heap a | HEltsSize v (listElts xs) (len xs)} @-}
-- fromList :: Ord a => [a] -> Heap a
-- fromList [] = empty
-- fromList (x:xs) = insert x (fromList xs)

-- ----------------------------------------------------------------

-- {-| Creating a list from a heap. Worst-case: O(N) -}

-- {-@ toList :: h:Heap a -> {v:[a] | LEltsSize v (heapElts h) (heapSize h)} @-}
-- toList :: Heap a -> [a]
-- toList (Heap ts) = treeListToList ts

-- {-@ appendPreservingListElts :: xs:[a] -> ys:[a] -> {v:[a] | LEltsSize v (S.union (listElts xs) (listElts ys)) (len xs + len ys)} @-}
-- appendPreservingListElts :: [a] -> [a] -> [a]
-- appendPreservingListElts [] ys = ys
-- appendPreservingListElts (x:xs) ys = x : appendPreservingListElts xs ys

-- {-@ treeListToList :: ts:[Tree a] -> {v:[a] | LEltsSize v (treeListElts ts) (treeListSize ts)} @-}
-- treeListToList :: [Tree a] -> [a]
-- treeListToList [] = []
-- treeListToList (t:ts) = appendPreservingListElts (treeToList t) (treeListToList ts)

-- {-@ treeToList :: t:Tree a -> {v:[a] | LEltsSize v (treeElts t) (size t)} @-}
-- treeToList :: Tree a -> [a]
-- treeToList (Node x [] _ _) = [x]
-- treeToList (Node x (t:ts) r sz) =
--   let remainder = Node x ts (r - 1) (sz - size t) in
--   appendPreservingListElts (treeToList t) (treeToList remainder)


-- {-| Finding the minimum element. Worst-case: O(log N), amortized: O(log N) -}

-- {-@ minimum :: h:NEHeap a -> {v:a | S.member v (heapElts h)} @-}
-- minimum :: Ord a => Heap a -> a
-- minimum = fst . deleteMin2

-- {-| Deleting the minimum element. Worst-case: O(log N), amortized: O(log N) -}

-- {-@ reverseHeapList :: ts:[Tree a] -> {v:[Tree a] | TsEltsSize v (treeListElts ts) (treeListSize ts) && len v = len ts} @-}
-- reverseHeapList :: [Tree a] -> [Tree a]
-- reverseHeapList ts = reverseHeapListAux ts []

-- {-@ reverseHeapListAux :: ts:[Tree a] -> acc:[Tree a] ->
--   {v:[Tree a] | TsEltsSize v (
--                   S.union (treeListElts ts) (treeListElts acc))(
--                   treeListSize ts + treeListSize acc)
--              && len v = len ts + len acc}
-- @-}
-- reverseHeapListAux :: [Tree a] -> [Tree a] -> [Tree a]
-- reverseHeapListAux [] acc = acc
-- reverseHeapListAux (t:ts) acc = reverseHeapListAux ts (t:acc)

-- {-@ unheapNonempty :: h:NEHeap a -> {v:NEList (Tree a) | TsEltsSize v (heapElts h) (heapSize h)} @-}
-- unheapNonempty :: Heap a -> [Tree a]
-- unheapNonempty (Heap ts@(_:_)) = ts

-- {-@ deleteMin :: h:NEHeap a -> {v:Heap a | S.isSubsetOf (heapElts v) (heapElts h) && 1 + heapSize v = heapSize h} @-}
-- deleteMin :: Ord a => Heap a -> Heap a
-- deleteMin = snd . deleteMin2

-- {-@ deleteMin2 :: h:NEHeap a ->
--   {v:(a, Heap {x:a | (fst v) <= x}) |
--     S.union (S.singleton (fst v)) (heapElts (snd v)) = heapElts h &&
--     1 + heapSize (snd v) = heapSize h} @-}
-- deleteMin2 :: Ord a => Heap a -> (a, Heap a)
-- deleteMin2 h =
--   let (t, ts2) = deleteMin' (unheapNonempty h) in
--   let ts1 = subtreeEltsAreEltsOfTree (treeAtLeastRoot t) in
--   (root t, Heap (merge' (reverseHeapList ts1) ts2))

-- -- rootIsEltOfTree t

-- -- TODO self-invariant?
-- -- {-@ rootIsEltOfTree :: t:Tree a -> {v:a | v = root t && S.member v (treeElts t)} @-}
-- -- rootIsEltOfTree :: Tree a -> a
-- -- rootIsEltOfTree (Node x [] _ _) = x
-- -- rootIsEltOfTree (Node x (t:ts) r sz) =
-- --   let remainder = Node x ts (r - 1) (sz - size t) in
-- --   rootIsEltOfTree remainder

-- -- TODO self-invariant?
-- {-@ subtreeEltsAreEltsOfTree :: t:Tree a -> {v:[Tree a] | S.union (S.singleton (root t)) (treeListElts v) = treeElts t && 1 + treeListSize v = size t } @-}
-- subtreeEltsAreEltsOfTree :: Ord a => Tree a -> [Tree a]
-- subtreeEltsAreEltsOfTree t =
--   liquidAssert (S.union (S.singleton (root t)) (treeListElts (subtrees t)) == treeElts t) $
--   liquidAssert (1 + treeListSize (subtrees t) == size t) $
--    subtrees t
-- -- subtreeEltsAreEltsOfTree (Node x (t:ts) r sz) =
-- --   liquidAssert (subtrees )
-- --     let remainder = Node x ts (r - 1) (sz - size t) in
-- --     t : subtreeEltsAreEltsOfTree remainder

-- {-@ deleteMin' :: xs:(NEList (Tree a)) ->
--   {v:(Tree a, [AtLeastTree a (root (fst v))]) |
--     S.union (treeElts (fst v)) (treeListElts (snd v)) = treeListElts xs &&
--     size (fst v) + treeListSize (snd v) = treeListSize xs}
-- @-}
-- deleteMin' :: Ord a => [Tree a] -> (Tree a, [Tree a])
-- deleteMin' [t] = (t, [])
-- deleteMin' (t:ts) =
--   let (t', ts') = deleteMin' ts in
--   if root t < root t'
--   then (t, (treeAtLeastRoot t'):ts')
--   else (t', (treeAtLeastRoot t):ts')

-- {-| Merging two heaps. Worst-case: O(log N), amortized: O(log N)

-- Properties to verify
-- 1. well-formedness
-- 2. sum of counts of all elements from both should be in both
-- -}

-- {-@ merge :: h1:Heap a -> h2:Heap a ->
--   {v:Heap a | HEltsSize v (S.union (heapElts h1) (heapElts h2)) (heapSize h1 + heapSize h2)} @-}
-- merge :: Ord a => Heap a -> Heap a -> Heap a
-- merge (Heap ts1) (Heap ts2) = Heap (merge' ts1 ts2)

-- {-@ merge' :: ts1:[Tree a] -> ts2:[Tree a] ->
--   {v:[Tree a] | treeListElts v = S.union (treeListElts ts1) (treeListElts ts2)
--              && treeListSize v = treeListSize ts1 + treeListSize ts2} @-}
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

-- {-@ heapSort :: h:Heap a -> {v:IncrList a | LEltsSize v (heapElts h) (heapSize h)} / [heapSize h] @-}
-- heapSort :: Ord a => Heap a -> [a]
-- heapSort (Heap []) = []
-- heapSort h@(Heap (_:_)) =
--   let (minElt, h') = deleteMin2 h in
--   minElt : heapSort h'

-- {-@ sortUsingHeap :: xs:[a] -> {v:IncrList a | LEltsSize v (listElts xs) (len xs)} @-}
-- sortUsingHeap :: Ord a => [a] -> [a]
-- sortUsingHeap = heapSort . fromList

-- {-| Checking validity of a heap. -}
-- {-@ valid :: Heap a -> TT @-}
-- valid :: Ord a => Heap a -> Bool
-- valid t = isOrdered (heapSort t)

-- {-@ isOrdered :: IncrList a -> TT @-}
-- isOrdered :: Ord a => [a] -> Bool
-- isOrdered [] = True
-- isOrdered [_] = True
-- isOrdered (x:y:xys) = x <= y && isOrdered (y:xys)
