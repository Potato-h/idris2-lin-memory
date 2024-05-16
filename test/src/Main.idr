module Main

import Profile
import Bench.Compare
import Tests.Simple
import Data.List
import Decidable.Equality
import TimeIt

sort : Ord a => List a -> List a
sort xs = if length xs < 2 
    then xs
    else let
        pivot = List.index (length xs `div` 2) xs @{believe_me ()}
        lhs = filter (< pivot) xs
        center = filter (== pivot) xs
        rhs = filter (> pivot) xs
        in Main.sort lhs ++ center ++ Main.sort rhs 

n : Nat
n = 500_000

xs : List Int
xs = genN n nxtR 5

main : IO ()
main = do
    -- runDefault (const True) Details absurd intBench
    runDefault (const True) Details absurd sortBench
    runDefault (const True) Details absurd partitionBench
