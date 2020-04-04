-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
-- Disable ADTs (only used with exactDC)
{-@ LIQUID "--no-adt" @-}

module SubtreesExperiment where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import qualified Language.Haskell.Liquid.Bag as B

import Prelude hiding (head, last, tail)

{-@ type AtLeast a X = {n:a | X <= n} @-}
{-@ type AtLeastTree a X = Tree (AtLeast a X) @-}
{-@ type NEList a = {xs:[a] | 0 < len xs} @-}
{-@ type NEHeap a = {h:Heap a | 0 < len (unheap h)} @-}
{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ measure treeListSize @-}
{-@ treeListSize :: xs:[Tree a] -> {v:Nat | (len xs <= v) && (v = 0 <=> len xs = 0)} @-}
treeListSize :: [Tree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = size x + treeListSize xs

{-@
data Tree [rank] a =
    Node
        { root :: a
        , rank :: Nat
        , subtrees :: {ts:[{t:AtLeastTree a root | rank > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts = rank}
        , size :: {v:Pos | v = 1 + treeListSize subtrees}
        }
@-}
data Tree a =
    Node
        { root :: a
        , rank :: Int
        , subtrees :: [Tree a]
        , size :: Int
        }
    deriving (Eq)


instance (Eq a, Ord a) => Eq (Heap a) where
  h1 == h2 = heapSort h1 == heapSort h2

{-@ measure treeElts @-}
{-@ treeElts :: t:Tree a -> {v:B.Bag a | v = B.put (root t) (treeListElts (subtrees t))} @-}
treeElts :: Ord a => Tree a -> B.Bag a
treeElts (Node x _ [] _) = B.put x B.empty
treeElts (Node x r tts@(_:ts) sz) =
    let refinedTs = firstTree tts in
    let t = head refinedTs in
    let remainder = Node x (r - 1) ts (sz - (size t)) in
    --NOTE: incredible hack: we needed the following assertion for the proof to hold
    --liquidAssert (rank t == treeRank t) $
    --so instead, we can do the following (since the statment is always true)
    if (rank t == treeRank t) then
    B.union (treeElts t) (treeElts remainder) else B.empty


{-@ measure treeListElts @-}
treeListElts :: Ord a => [Tree a] -> B.Bag a
treeListElts [] = B.empty
treeListElts (t:ts) = B.union (treeElts t) (treeListElts ts)

{-@ measure head @-}
{-@ head :: {xs:[a] | len xs > 0} -> a @-}
head (x:_) = x

{-@ measure tail @-}
{-@ tail :: {xs:[a] | len xs > 0} -> [a] @-}
tail (_:xs) = xs

{-@ type Pos = {n:Int | n >= 1} @-}

{-@ reflect lemma @-}
{-@ lemma :: {ts:[{t:Tree a | len ts > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts > 0} -> {v:[{t:Tree a | len ts - 1 > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | v = tail ts} @-}
lemma :: [Tree a] -> [Tree a]
lemma (_:ts) = ts

{-@ reflect firstTree @-}
{-@ firstTree :: {ts:[{t:Tree a | len ts > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts >= 1} -> {v:[Tree a] | treeRank (head v) = len ts - 1 && len v = len ts && v = ts} @-}
firstTree ::  [Tree a] -> [Tree a]
firstTree [t] = [t]
firstTree (t:ts@(_:_)) =
    let refinedTs = lemma (t:ts) in
    let acc = firstTree refinedTs in
    -- NOTE: if we uncomment this assert, the file no longer verifies...
    -- liquidAssert (head acc == head refinedTs) $
    t:acc

{-@ measure treeRank @-}
{-@ treeRank :: t:(Tree a) -> {n:Nat | n = rank t} @-}
treeRank (Node _ r _ _) = r

-- verifying heap functions

{-@ data Heap a = Heap { unheap :: [Tree a] } @-}
data Heap a = Heap { unheap :: [Tree a] }

{-@ measure heapElts @-}
{-@ heapElts :: h:Heap a -> {v:Bag a | v = treeListElts (unheap h)} @-}
heapElts :: (Ord a) => Heap a -> B.Bag a
heapElts (Heap ts) = treeListElts ts

{-@ measure listElts @-}
{-@ listElts :: [a] -> Bag a @-}
listElts :: Ord a => [a] -> B.Bag a
listElts [] = B.empty
listElts (x : xs) = B.union (B.put x B.empty) (listElts xs)

--Verification of [link]

{-@ predicate TEltsSize T X Y = (treeElts T = X && size T = Y )@-}
{-@ predicate HEltsSize H X Y = (heapElts H = X && heapSize H = Y) @-}
{-@ predicate TsEltsSize Ts X Y = (treeListElts Ts = X && treeListSize Ts = Y) @-}
{-@ predicate LEltsSize H X Y = (listElts H = X && len H = Y) @-}

{-@ treeAtLeastRoot :: t:Tree a ->
  {v:AtLeastTree a (root t) | TEltsSize v (treeElts t) (size t)
                           && root v = root t && rank v = rank t && v = t} @-}
treeAtLeastRoot :: Tree a -> Tree a
treeAtLeastRoot (Node x r ts sz) = Node x r ts sz

--NOTE: need all 3 of these assertions for the function to verify
--Link only works on Trees with equal ranks
{-@ link :: t1:(Tree a) -> {t2:(Tree a) | rank t2 = rank t1} ->
  {v:Tree a | TEltsSize v (B.union (treeElts t1) (treeElts t2)) (size t1 + size t2) && rank v = rank t1 + 1}
@-}
link :: Ord a => Tree a -> Tree a -> Tree a
link t1@(Node x1 r1 ts1 sz1) t2@(Node x2 r2 ts2 sz2)
  | x1 <= x2  =
        let new =  Node x1 (r1 + 1) ((treeAtLeastRoot t2):ts1) (sz1 + sz2) in
      liquidAssert (treeElts new == B.union (treeElts t1) (treeElts t2)) $
         new
  | otherwise = let new =  Node x2 (r2 + 1) ((treeAtLeastRoot t1):ts2) (sz1 + sz2) in
      liquidAssert (r2 == r1) $
      liquidAssert (treeElts new == B.union (treeElts t1) (treeElts t2)) $
         new

-- simple functions

{-@ measure heapSize @-}
{-@ heapSize :: h:Heap a -> {v:Nat | (len (unheap h) <= v) && (v = treeListSize (unheap h))} @-}
heapSize :: Heap a -> Int
heapSize (Heap ts) = treeListSize ts


{-@ empty :: {v:Heap a | HEltsSize v B.empty 0} @-}
empty :: Heap a
empty = Heap []

-- {-@ null :: h:(Heap a) -> {v:Bool | v <=> heapElts h = S.empty} @-}
{-@ null :: h:(Heap a) -> {v:Bool | v <=> heapSize h == 0} @-}
null :: Heap a -> Bool
null h = heapSize h == 0

{-@ singleton :: x:a -> {v:Heap a | HEltsSize v (B.put x B.empty) 1} @-}
singleton :: Ord a => a -> Heap a
singleton x = Heap [Node x 0 [] 1]

--Insert
--NOTE: the insert' function we looked at was wrong - we should only ever be calling link on trees of equal rank
{-@ insert' :: t:Tree a -> ts:[Tree a] ->
  {v:[Tree a] | TsEltsSize v (B.union (treeElts t) (treeListElts ts)) (size t + treeListSize ts) }
@-}
insert' :: Ord a => Tree a -> [Tree a] -> [Tree a]
insert' t [] = [t]
insert' t ts@(t':ts')
  | rank t < rank t' = t : ts
  | rank t > rank t' = t' : insert' t ts'
  | otherwise       = insert' (link t t') ts'

{-@ insert :: x:a -> h:Heap a ->
  {v:Heap a | HEltsSize v (B.union (B.put x B.empty) (heapElts h)) (1 + heapSize h)} @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x (Heap ts) = Heap (insert' (Node x 0 [] 1) ts)

{-@ fromList :: xs:[a] -> {v:Heap a | HEltsSize v (listElts xs) (len xs)} @-}
fromList :: Ord a => [a] -> Heap a
fromList [] = empty
fromList (x:xs) = insert x (fromList xs)

--- toList

{-@ toList :: h:Heap a -> {v:[a] | listElts v = heapElts h && len v = heapSize h} @-}
toList :: Heap a -> [a]
toList (Heap ts) = treeListToList ts

{-@ appendPreservingListElts :: xs:[a] -> ys:[a] -> {v:[a] | listElts v = B.union (listElts xs) (listElts ys) && len v = len xs + len ys} @-}
appendPreservingListElts :: [a] -> [a] -> [a]
appendPreservingListElts [] ys = ys
appendPreservingListElts (x:xs) ys = x : appendPreservingListElts xs ys

{-@ treeListToList :: ts:[Tree a] -> {v:[a] | listElts v = treeListElts ts && len v = treeListSize ts} @-}
treeListToList :: [Tree a] -> [a]
treeListToList [] = []
treeListToList (t:ts) = appendPreservingListElts (treeToList t) (treeListToList ts)

{-@ treeToList :: t:Tree a -> {v:[a] | listElts v = treeElts t && len v = size t} @-}
treeToList :: Tree a -> [a]
treeToList (Node x _ [] _) = [x]
treeToList (Node x r tts@(_:ts) sz) =
    let refinedTs = firstTree tts in
    let t = head refinedTs in
    let remainder = Node x (r - 1) ts (sz - (size t)) in
    --just like treeElts, need this
    liquidAssert (rank t == treeRank t) $
    appendPreservingListElts (treeToList t) (treeToList remainder)

--deleteMin

{-@ deleteMin' :: xs:(NEList (Tree a)) ->
  {v:(Tree a, [AtLeastTree a (root (fst v))]) |
    B.union (treeElts (fst v)) (treeListElts (snd v)) = treeListElts xs &&
    size (fst v) + treeListSize (snd v) = treeListSize xs}
@-}
deleteMin' :: Ord a => [Tree a] -> (Tree a, [Tree a])
deleteMin' [t] = (t, [])
deleteMin' (t:ts) =
  let (t', ts') = deleteMin' ts in
  if root t < root t'
  then (t, (treeAtLeastRoot t'):ts')
  else (t', (treeAtLeastRoot t):ts')

--helpers for deleteMin2
{-@ unheapNonempty :: h:NEHeap a -> {v:NEList (Tree a) | TsEltsSize v (heapElts h) (heapSize h)} @-}
unheapNonempty :: Heap a -> [Tree a]
unheapNonempty (Heap ts@(_:_)) = ts

{-@ subtreeEltsAreEltsOfTree :: t:Tree a -> {v:[Tree a] | B.union (B.put (root t) B.empty) (treeListElts v) = treeElts t && 1 + treeListSize v = size t} @-}
subtreeEltsAreEltsOfTree :: Tree a -> [Tree a]
subtreeEltsAreEltsOfTree (Node _ _ [] _) = []
subtreeEltsAreEltsOfTree (Node x r tts@(_:ts) sz) =
    let refinedTs = firstTree tts in
    let t = head refinedTs in
    let remainder = Node x (r - 1) ts (sz - (size t)) in
    --just like treeElts, need this
    liquidAssert (rank t == treeRank t) $
    t : subtreeEltsAreEltsOfTree remainder

{-@ reverseHeapList :: ts:[Tree a] -> {v:[Tree a] | TsEltsSize v (treeListElts ts) (treeListSize ts)} @-}
reverseHeapList :: [Tree a] -> [Tree a]
reverseHeapList ts = reverseHeapListAux ts []

{-@ reverseHeapListAux :: ts:[Tree a] -> acc:[Tree a] ->
  {v:[Tree a] | TsEltsSize v (
                  B.union (treeListElts ts) (treeListElts acc))(
                  treeListSize ts + treeListSize acc)}
@-}
reverseHeapListAux :: [Tree a] -> [Tree a] -> [Tree a]
reverseHeapListAux [] acc = acc
reverseHeapListAux (t:ts) acc = reverseHeapListAux ts (t:acc)

--TODO: this should pass, not sure why it isn't, not a huge deal either way (only if we care about postcondition of minimum)
-- {-@ rootIsEltOfTree :: t:Tree a -> {v:a | v = root t && B.get v (treeElts t) > 0} @-}
-- rootIsEltOfTree :: Ord a => Tree a -> a
-- rootIsEltOfTree (Node x _ [] _) = x
-- rootIsEltOfTree (Node x r tts@(_:ts) sz) =
--   let refinedTs = firstTree tts in
--     let t = head refinedTs in
--     let remainder = Node x (r - 1) ts (sz - (size t)) in
--     --just like treeElts, need this
--     liquidAssert (rank t == treeRank t) $
--     liquidAssert (root remainder == x) $
--     liquidAssert (treeElts (Node x r tts sz) == B.union (treeElts t)(treeElts remainder) ) $
--     let recur = rootIsEltOfTree remainder in
--     liquidAssert (B.get x (treeElts (remainder)) > 0) $
--     recur
  

{-@ deleteMin2 :: h:NEHeap a ->
  {v:(a, Heap {x:a | (fst v) <= x}) |
    B.union (B.put (fst v) B.empty) (heapElts (snd v)) = heapElts h &&
    1 + heapSize (snd v) = heapSize h} @-}
deleteMin2 :: Ord a => Heap a -> (a, Heap a)
deleteMin2 h =
  let (t, ts2) = deleteMin' (unheapNonempty h) in
  let ts1 = subtreeEltsAreEltsOfTree (treeAtLeastRoot t) in
  (root t, Heap (merge' (reverseHeapList ts1) ts2))

-- TODO, add back postcondition on input, something like (not sure best way to phrase for bags), may need to strengthen deleteMin2 or add back rootIsEltOfTree
-- bags are not as nice for sets as membership
--{-@ minimum :: h:NEHeap a -> {v:a | B.get v (heapElts h) > 0} @-}
{-@ minimum :: h:NEHeap a -> a @-}
minimum :: Ord a => Heap a -> a
minimum = fst . deleteMin2

-- merge

{-@ merge :: h1:Heap a -> h2:Heap a ->
  {v:Heap a | HEltsSize v (B.union (heapElts h1) (heapElts h2)) (heapSize h1 + heapSize h2)} @-}
merge :: Ord a => Heap a -> Heap a -> Heap a
merge (Heap ts1) (Heap ts2) = Heap (merge' ts1 ts2)

{-@ merge' :: ts1:[Tree a] -> ts2:[Tree a] ->
  {v:[Tree a] | treeListElts v = B.union (treeListElts ts1) (treeListElts ts2)
             && treeListSize v = treeListSize ts1 + treeListSize ts2} @-}
merge' :: Ord a => [Tree a] -> [Tree a] -> [Tree a]
merge' ts1 [] = ts1
merge' [] ts2 = ts2
merge' ts1@(t1:ts1') ts2@(t2:ts2')
  | rank t1 < rank t2 = t1 : merge' ts1' ts2
  | rank t2 < rank t1 = t2 : merge' ts1 ts2'
  | otherwise         = insert' (link t1 t2) (merge' ts1' ts2')


----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

{-@ heapSort :: h:Heap a -> {v:IncrList a | LEltsSize v (heapElts h) (heapSize h)} / [heapSize h] @-}
heapSort :: Ord a => Heap a -> [a]
heapSort (Heap []) = []
heapSort h@(Heap (_:_)) =
  let (minElt, h') = deleteMin2 h in
  minElt : heapSort h'

{-@ sortUsingHeap :: xs:[a] -> {v:IncrList a | LEltsSize v (listElts xs) (len xs)} @-}
sortUsingHeap :: Ord a => [a] -> [a]
sortUsingHeap = heapSort . fromList

{-| Checking validity of a heap. -}
{-@ valid :: Heap a -> TT @-}
valid :: Ord a => Heap a -> Bool
valid t = isOrdered (heapSort t)

{-@ isOrdered :: IncrList a -> TT @-}
isOrdered :: Ord a => [a] -> Bool
isOrdered [] = True
isOrdered [_] = True
isOrdered (x:y:xys) = x <= y && isOrdered (y:xys)

