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

{-@ lemma :: {n:Int | n >= 1} -> {ts:[{t:Tree a | n > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts > 0} -> {v:[{t:Tree a | n - 1 > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | v = tail ts} @-}
lemma :: Int -> [Tree a] -> [Tree a]
lemma n (_:ts) = ts

{-@ firstTree :: {n:Int | n >= 1} -> {ts:[{t:Tree a | n > treeRank t}]<{\ti tj -> treeRank ti > treeRank tj}> | len ts = n} -> {v:[Tree a] | treeRank (head v) = n - 1 && len v = len ts && head v = head ts} @-}
firstTree :: Eq a => Int -> [Tree a] -> [Tree a]
firstTree n (t:[]) =
    let v = (t:[]) in
    -- liquidAssert (n == 1) $
    -- liquidAssert (treeRank t == 0) $
    -- liquidAssert (treeRank (head v) == 0) $
    v
firstTree n (t:ts@(_:_)) =
    -- liquidAssert (length ts > 0) $
    let refinedTs = lemma n (t:ts) in
    -- liquidAssert (refinedTs == ts) $
    -- liquidAssert (treeRank (head refinedTs) < n - 1) $
    -- liquidAssert (treeRank t > treeRank (head refinedTs)) $
    -- liquidAssert (treeRank t < n) $
    let acc = firstTree (n - 1) refinedTs in
    -- liquidAssert (length refinedTs > 0) $
    -- liquidAssert (length acc == length refinedTs) $

    -- NOTE: if we uncomment this assert, the file no longer verifies...
    -- liquidAssert (head acc == head refinedTs) $
    -- liquidAssert (treeRank t == n - 1) $

    -- liquidAssert (treeRank (head acc) == (n - 1) - 1) $
    -- let v = t:acc in
    -- liquidAssert (treeRank (head v) == (n - 1)) $
    -- v
    t:acc

-- {v:[Tree a] | treeRank (head v) = n - 1 && len v = len ts}

-- {-@ lastSubtree :: {t:Tree a | len (subtrees t) > 0} -> {v:Tree a | treeRank v + 1 = treeRank t} @-}
-- lastSubtree (Node r (t:ts)) = lastSubtree t
-- lastSubtree

{-@ measure treeRank @-}
{-@ treeRank :: Tree a -> Nat @-}
treeRank (Node r _) = r
