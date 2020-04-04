-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
-- Disable ADTs (only used with exactDC)
{-@ LIQUID "--no-adt" @-}

module SubtreesExperiment where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import qualified Language.Haskell.Liquid.Bag as B

import Prelude hiding (head, last, tail)

{-@
data Tree [rank] a =
    Node
        { root :: a
        , rank :: Nat
        , subtrees :: {ts:[{t:Tree a | rank > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts = rank}
        }
@-}
data Tree a =
    Node
        { root :: a
        , rank :: Int
        , subtrees :: [Tree a]
        }
    deriving (Eq)

{-@ measure treeElts @-}
{-@ treeElts :: t:Tree a -> {v:B.Bag a | v = B.put (root t) (treeListElts (subtrees t))} @-}
treeElts :: Ord a => Tree a -> B.Bag a
treeElts (Node x _ []) = B.put x B.empty
treeElts (Node x r tts@(_:ts)) =
    let refinedTs = firstTree tts in
    let t = head refinedTs in
    let remainder = Node x (r - 1) ts in
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
firstTree :: Eq a => [Tree a] -> [Tree a]
firstTree [t] = [t]
firstTree (t:ts@(_:_)) =
    let refinedTs = lemma (t:ts) in
    let acc = firstTree refinedTs in
    -- NOTE: if we uncomment this assert, the file no longer verifies...
    -- liquidAssert (head acc == head refinedTs) $
    t:acc

{-@ measure treeRank @-}
{-@ treeRank :: t:(Tree a) -> {n:Nat | n = rank t} @-}
treeRank (Node _ r _) = r
