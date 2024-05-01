module Mem.Array

import public Mem.Maps
import public Mem.Primitives
import Control.Relation

public export
0 CRes : Type -> Type -> Type
CRes a b = Res a (const b)

public export
record Ur a where
    constructor MkUr
    inner : a

export
record Array (0 a : Type) (0 cm : CellMap) where
    constructor MkArray
    buffer : AnyPtr

-- FIXME: Does public API really need this?
export 
getBuffer : (1 arr : Array a cm) -> CRes AnyPtr (Array a cm)
getBuffer (MkArray buffer) = buffer # MkArray buffer

export
transport : (1 arr : Array a cm1) -> (0 _ : cm1 -=- cm2) -> Array a cm2
transport (MkArray buffer) _ = MkArray buffer

export
read : 
    Trivial a =>
    (1 arr : Array a cm) -> 
    (i : Nat) -> 
    (0 prf : cm i = NonEmpty) -> 
    CRes a (Array a cm)
read (MkArray buffer) i _ = let
    idx = cast i 
    val = unsafePerformIO $ primIO (readBy buffer idx)
    in val # MkArray buffer

export
write : 
    Trivial a =>
    (1 arr : Array a cm) -> 
    (i : Nat) -> 
    (0 prf : cm i = Empty) -> 
    a -> 
    Array a (setAt cm i NonEmpty)
write (MkArray buffer) i _ val = let
    idx = cast i
    in unsafePerformIO $ do
        primIO (writeBy buffer idx val)
        pure (MkArray buffer)

export
discard :
    Trivial a =>
    (1 arr : Array a cm) ->
    (i : Nat) ->
    (0 prf : cm i = NonEmpty) ->
    Array a (setAt cm i Empty)
discard (MkArray buffer) _ _ = MkArray buffer

export
updateAt : 
    Trivial a =>
    (1 arr : Array a cm) ->
    (i : Nat) ->
    (0 prf : cm i = NonEmpty) ->
    (f : a -> a) ->
    Array a cm
updateAt arr i prf f = let
    x # arr = read arr i prf
    arr = discard arr i prf
    arr = write arr i (setValueAt cm i) (f x)
    in transport arr (setCancel cm i `transitive` setKnown cm i prf)

export
withArray : Trivial a => (n : Nat) -> (1 f : (1 arr : Array a (allEmpty n)) -> Ur b) -> b
withArray n f = let
    buff = unsafePerformIO $ primIO $ malloc (sizeOf a * cast n)
    arr = MkArray buff
    MkUr w = f arr
    in w

export
finish : 
    (1 arr : Array a cm) ->
    b ->
    Ur b
finish (MkArray buffer) res = unsafePerformIO $ do
    primIO $ free buffer
    pure $ MkUr res


export
alloc : 
    Trivial a =>
    (m : Nat) ->
    (1 src : Array a cm) ->
    LPair (Array a cm) (Array a (allEmpty m))
alloc m src = src # MkArray (unsafePerformIO $ primIO $ malloc (sizeOf a * cast m)) 

export 
copy : 
    Trivial a =>
    (n : Nat) ->
    (1 src : Array a (allNonEmpty n)) ->
    (1 dst : Array a (allEmpty (n + m))) ->
    LPair (Array a (allEmpty n)) (Array a (prefixMap n m))
copy n (MkArray src) (MkArray dst) = (MkArray src) # (MkArray $ unsafePerformIO $ do
    primIO $ memcpy dst src (sizeOf a * cast n)
    pure dst
    ) 
