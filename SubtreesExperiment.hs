-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
-- Disable ADTs (only used with exactDC)
{-@ LIQUID "--no-adt" @-}

module SubtreesExperiment where

import Language.Haskell.Liquid.Prelude (liquidAssert)

import Prelude hiding (head, last)

{-@
data Tree a =
    Node
        { rank :: Nat
        , subtrees :: {ts:[{t:Tree a | rank > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts = rank}
        }
@-}
data Tree a =
    Node
        { rank :: Int
        , subtrees :: [Tree a]
        }
    deriving (Eq)

-- {-@ measure last @-}
-- {-@ last :: {xs:[a] | len xs > 0} -> a @-}
-- last [x] = x
-- last (x:xs) = last xs

-- {-@ firstSubtree :: {t:Tree a | len (subtrees t) > 0} -> {v:Tree a | treeRank v + 1 = treeRank t} @-}
-- firstSubtree (Node r (t:ts)) = t


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
{-@ firstTree :: {ts:[{t:Tree a | len ts > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts >= 1} -> {v:[Tree a] | treeRank (head v) = len ts - 1 && len v = len ts && head v = head ts} @-}
firstTree :: Eq a => [Tree a] -> [Tree a]
firstTree [t] = [t]
firstTree (t:ts@(_:_)) =
    let refinedTs = lemma (t:ts) in
    let acc = firstTree refinedTs in
    -- NOTE: if we uncomment this assert, the file no longer verifies...
    -- liquidAssert (head acc == head refinedTs) $
    t:acc

{-@ measure treeRank @-}
{-@ treeRank :: Tree a -> Nat @-}
treeRank (Node r _) = r
