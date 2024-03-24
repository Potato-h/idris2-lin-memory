module Mem.Vector

import Mem.Array
import Control.Relation
import Data.Nat

export
record Vector (a : Type) where
    constructor MkVect
    len : Nat
    rest : Nat
    1 elems : Array a (prefixMap len rest)

export
withVector : Trivial a => (1 f : (1 arr : Vector a) -> Ur b) -> b
withVector f = withArray initialCapacity (\arr => f $ MkVect 0 _ (transport arr (symmetric $ emptyPrefix _)))

export
vLenght : (1 arr : Vector a) -> CRes Nat (Vector a)
vLenght (MkVect len rest elems) = len # (MkVect len rest elems)

export
push : Trivial a => (1 this : Vector a) -> a -> Vector a
push (MkVect len 0 elems) x = let
    old # new = alloc (len + len) elems
    old = transport old (emptySuffix len)
    old # new = copy len old new
    MkUr () = finish old ()
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
    elems' = discard elems' k (correctAccess k rest)
    in Just x # MkVect k (S rest) (transport elems' (popFromPrefixPreservePrefix k rest))
    where
    correctAccess : (n, k : Nat) -> (prefixMap (S n) k) n = NonEmpty
    correctAccess n k = rewrite n_less_s_n n in Refl

export
vFinish : (1 arr : Vector a) -> b -> Ur b
vFinish (MkVect len rest elems) v = finish elems v

