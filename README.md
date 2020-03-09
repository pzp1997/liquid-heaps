## Challenges

Coming up with lemmas: treeIsBoundedByItsRootLemma, boundedTreeTransitivityLemma

{-@ measure sumSizeList @-}
{-@ sumSizeList :: [Tree a] -> Nat @-}
sumSizeList :: [Tree a] -> Int
sumSizeList

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
