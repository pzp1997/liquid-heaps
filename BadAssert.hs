module BadAssert where

import Language.Haskell.Liquid.Prelude

{-@ firstTreeSimplified :: {xs:[a] | len xs > 0} -> {v:[a] | hd v = hd xs && len v = len xs} @-}
firstTreeSimplified :: Eq a => [a] -> [a]
firstTreeSimplified xs@[_] = xs
firstTreeSimplified (x:xs) =
  let v = firstTreeSimplified xs in
  liquidAssert (hd v == hd xs) $
  x:v

{-@ measure hd @-}
{-@ hd :: {xs:[a] | len xs > 0} -> a @-}
hd (x:_) = x


{-@ measure foo @-}
{-@ lazy foo @-}
foo :: Bool -> Bool
foo True = True
foo False = foo False

{-@ bar :: a -> {v:Bool | v = foo False} @-}
bar :: a -> Bool
bar _ = foo False
