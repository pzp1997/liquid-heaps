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


## Interesting things
Tail recursive version of `reverseHeapList` was easier to verify
