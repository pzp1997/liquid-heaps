## Challenges

Coming up with lemmas: treeIsBoundedByItsRootLemma, boundedTreeTransitivityLemma

It was tricky to figure out how to make `sumSizeList` a measure. At first we had it written as `sum . map size` but that's not a valid measure in LH.

boundedSizeSubtreeLemma (for termination of elts)

termination of elts was so challenging we couldn't do it, we provided a lot of lemmas that should imply the correct measure is decreasing, but Liquid Haskell could not evaluate this, so we marked the function "lazy" to ignore termination checking

We needed some cleverness to express the rank property since the rank of a tree with no subtrees is 0 not 1. The trick was to create an intermediate measure `lubRank` to special case this

## Tips

Destruct and re-construct inputs to get the types to work out
Avoid partial functions
Specialize things you want to use as measures
Lift as much to the type level as possible
Don't worry about using parts of definitions before they're defined
Use `assert` to figure out what the SMT solver has already inferred
Don't use newtype ever
Sometimes explicit recursion is better than fold, e.g. fromList
Avoid indirection as much as possible
assert sometimes magically proves things (like in sublistSizeLemma)
abstract refinement types suck (are sometimes hard to deal with)

## Interesting things
Tail recursive version of `reverseHeapList` was easier to verify

## Examples of effective assertion usage

{-@ deleteMin' :: {xs:[Tree a] | 0 < len xs} -> {v:(Tree a, [BoundedTree a (root (fst v))]) | size (fst v) + sumSizeList (snd v) == sumSizeList xs} @-}
-- {-@ deleteMin' :: {xs:[Tree a] | 0 < len xs} -> {v:(Tree a, [Tree a]) | size (fst v) + sumSizeList (snd v) == sumSizeList xs} @-}
deleteMin' :: Ord a => [Tree a] -> (Tree a, [Tree a])
deleteMin' [t] = (t, [])
deleteMin' (t:ts) =
  let acc = deleteMin' ts in
  let t' = fst acc in
  let ts' = snd acc in
  let x' = root t' in
  let x = root t in
  let tBounded' = treeIsBoundedByItsRootLemma t' in
  if x < x'
  then (
    let tBoundedByX = boundedTreeTransitivityLemma x x' tBounded' in
    let tsBoundedByX = boundedTreeListTransitivityLemma x x' ts' in
    let vSnd = tBoundedByX : tsBoundedByX in
    -- assertBoundedTree x' tBounded' $
    -- assertBoundedTree x tBoundedByX $
    -- assertBoundedTreeList x' ts' $
    -- assertBoundedTreeList x tsBoundedByX $
    assertBoundedTreeList x vSnd $
    (t, vSnd)
  )
  else (t', t:ts')


# Strange Errors

**** RESULT: ERROR *************************************************************


 /home/josh/Documents/HW/CIS673/cis673-proj/BinomialHeap.hs:263:28-39: Error: Uh oh.
  
 263 |   assert (1 + treeListSize (subtrees t) == size t) $
                                  ^^^^^^^^^^^^
  
     (Another Broken Test!!!) splitc unexpected:
(RVar LIQUID$dummy)
  <:
(RApp Data.Heap.Binominal.Tree<[]>(RVar a))