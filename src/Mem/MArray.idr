module Mem.MArray

import Mem.Array
import Mem.Maps
import Data.Vect
import Decidable.Equality

export
record MArray n a where
    constructor MkMArray
    1 arr : Array a (allNonEmpty n)

withMArray : Trivial a => Vect n a -> (1 f : (1 arr : MArray n a) -> Ur b) -> b
withMArray vals f = ?impl_later

get : Trivial a => (1 arr : MArray n a) -> (idx : Nat) -> (0 prf : idx < n = True) -> CRes a (MArray n a)  
get (MkMArray arr) idx prf = let
    v # arr = Array.read arr idx (rewrite prf in Refl)
    in v # MkMArray arr

set : Trivial a => (1 arr : MArray n a) -> (idx : Nat) -> (0 prf : idx < n = True) -> a -> MArray n a  
set (MkMArray arr) idx prf v = MkMArray $ Array.updateAt arr idx (rewrite prf in Refl) (const v) 

swap : 
    Trivial a => 
    (1 arr : MArray n a) -> 
    (i, j : Nat) -> 
    (0 _ : i < n = True) -> 
    (0 _ : j < n = True) -> 
    MArray n a
swap arr i j p1 p2 = let
    vi # arr = get arr i p1
    vj # arr = get arr j p2
    arr = set arr i p1 vj
    arr = set arr j p2 vi 
    in arr
