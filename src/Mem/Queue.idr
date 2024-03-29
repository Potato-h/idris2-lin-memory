module Mem.Queue

import Mem.Vector
import Mem.Primitives
import Mem.Array

export
record Queue a where
    constructor MkQueue
    1 input : Vector a
    1 output : Vector a

export
withQueue : Trivial a => (1 f : (1 q : Queue a) -> Ur b) -> b
withQueue f = 
    withVector $ \vec1 =>
    withVector $ \vec2 => 
    let (MkUr res) = f (MkQueue vec1 vec2)
    in MkUr $ MkUr res

export
push : Trivial a => (1 q : Queue a) -> a -> Queue a
push (MkQueue input output) x = MkQueue (push input x) output

export
pop : Trivial a => (1 q : Queue a) -> CRes (Maybe a) (Queue a)
pop (MkQueue input output) = let (emp # output) = isEmpty output
    in if emp 
    then let 
        (input # output) = input `moveTo` output
        (v # output) = Mem.Vector.pop output 
        in v # MkQueue input output 
    else let
        (v # output) = Mem.Vector.pop output
        in v # MkQueue input output 
    where
    moveTo : (1 from : Vector a) -> (1 to : Vector a) -> LPair (Vector a) (Vector a)
    moveTo from to = case Mem.Vector.pop from of 
        ((Just x) # r) => r `moveTo` (push to x)
        (Nothing # r) => r # to

export
qFinish : (1 q : Queue a) -> b -> Ur b
qFinish (MkQueue input output) x = let
    MkUr () = vFinish input ()
    in vFinish output x