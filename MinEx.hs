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


import Prelude hiding (minimum, maximum, null, head)
import Language.Haskell.Liquid.Prelude
import qualified Data.List as List

{-@ type AtLeast a X = {n:a | X <= n} @-}
{-@ type Pos = GeInt 1 @-}


--Binomial heap Invariants: if rank of heap is r, then subtrees have ranks (in order) 0, 1, ..., r-1 and if rank is 0, then heap has 1 elt
{-@ data Tree  a =
    Node
        { root :: a
        , subtrees :: Subtrees a
        , rank :: Nat
        , size :: Pos
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

{-@ type AtLeastTree a X = Tree (AtLeast a X) @-}
{-@ type Subtrees a = [AtLeastTree a root]<{\ti tj -> rank' ti = rank' tj + 1}> @-}

{-@ test:: Tree a -> a @-}
test :: Ord a => Tree a -> a
test (Node x [] _ _) = x
test (Node x (t:ts) r sz) =
    liquidAssert (length (subtrees t) == length (subtrees t)) $
    x






