module Mem.Vector

import Mem.Array
import Mem.Slice
import Control.Relation
import Data.Nat
import Data.Bool
import Decidable.Equality

export
record Vector a where
    constructor MkVect
    len : Nat
    rest : Nat
    1 elems : Array a (prefixMap len rest)

initialCapacity : Nat
initialCapacity = 2

export
withVector : Trivial a => (1 f : (1 arr : Vector a) -> Ur b) -> b
withVector f = withArray initialCapacity (\arr => f $ MkVect 0 _ (transport arr (symmetric $ emptyPrefix _)))

export
vLenght : (1 arr : Vector a) -> CRes Nat (Vector a)
vLenght (MkVect len rest elems) = len # (MkVect len rest elems)

export
isEmpty : (1 arr : Vector a) -> CRes Bool (Vector a)
isEmpty arr = let (len # arr) = vLenght arr in len == 0 # arr

export
push : Trivial a => (1 this : Vector a) -> a -> Vector a
push (MkVect len 0 elems) x = let
    old # new = alloc (len + len) elems
    old = transport old (emptySuffix len)
    old # new = copy len old new
    MkUr () = Array.finish old ()
    in push (MkVect len len new) x
push (MkVect len (S k) elems) x = let
    elems' = write elems len (correctAccess len k) x
    in MkVect (S len) k (transport elems' (pushToPrefixPreservePrefix len k))
    where
    correctAccess : (n, k : Nat) -> (prefixMap n (S k)) n = Empty
    correctAccess n k = 
        rewrite n_less_n_is_absurd n in 
        rewrite n_less_n_plus_k n k in Refl

export
pop : Trivial a => (1 this : Vector a) -> CRes (Maybe a) (Vector a)
pop (MkVect 0 rest elems) = Nothing # MkVect 0 rest elems
pop (MkVect (S k) rest elems) = let
    x # elems' = read elems k (correctAccess k rest)
    elems' = Array.discard elems' k (correctAccess k rest)
    in Just x # MkVect k (S rest) (transport elems' (popFromPrefixPreservePrefix k rest))
    where
    correctAccess : (n, k : Nat) -> (prefixMap (S n) k) n = NonEmpty
    correctAccess n k = rewrite n_less_s_n n in Refl

export
extend : Trivial a => Foldable t => (1 this : Vector a) -> t a -> Vector a
extend this vals = go this (toList vals)
    where
    go : (1 _ : Vector a) -> List a -> Vector a
    go vec [] = vec
    go vec (x :: xs) = go (push vec x) xs

export
withVectorFromList : Trivial a => Foldable t => t a -> (1 f : (1 arr : Vector a) -> Ur b) -> b
withVectorFromList inits f = withVector $ \vec => f $ extend vec inits

export
foldl : Trivial a => (f : a -> acc -> acc) -> acc -> (1 this : Vector a) -> CRes acc (Vector a)
foldl f ac (MkVect len rest elems) = let
    res # elems = go 0 len f ac elems
    in res # (MkVect len rest elems)
    where
    go : (i, len : Nat) -> (f : a -> acc -> acc) -> acc -> (1 arr : Array a (prefixMap len cap)) -> CRes acc (Array a (prefixMap len cap))
    go i len f acc arr = case (i < len) `decEq` True of
        (Yes prf) => let
            elem # arr = read arr i (correctAccessForPrefix prf) 
            in go (S i) len f (f elem acc) arr
        (No _) => acc # arr

export
asSlice : 
    Trivial a => 
    (1 this : Vector a) -> 
    (1 f : (n : Nat) -> (1 sl : Slice n a) -> Ur b)
    -> CRes b (Vector a)
asSlice (MkVect len rest arr) f = let
    buff # arr = getBuffer arr
    MkUr v = f len (MkSlice 0 buff)
    in v # (MkVect len rest arr)

export
vFinish : (1 arr : Vector a) -> b -> Ur b
vFinish (MkVect len rest elems) v = Array.finish elems v

