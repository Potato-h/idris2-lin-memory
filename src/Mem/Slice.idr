module Mem.Slice

import Debug.Trace
import Mem.Array
import Mem.Maps
import Data.Nat
import Data.Nat.Views
import Decidable.Equality

-- FIXME: constructor of Slice should be private
public export
record Slice (0 n : Nat) (0 a : Type) where
    constructor MkSlice
    offset : Nat
    -- 0 cm : CellMap
    -- 0 prf : (i : Nat) -> (0 _ : i `LT` n) -> cm (offset + i) = NonEmpty 
    -- 1 sl : Array a cm
    buffer : AnyPtr

export 
splitAt : (n : Nat) -> (1 sl : Slice (n + m) a) -> LPair (Slice n a) (Slice m a)
splitAt n (MkSlice offset buffer) = MkSlice offset buffer # MkSlice (offset + n) buffer 

unsafeDestroyWorld : (1 x : %World) -> a -> a
unsafeDestroyWorld %MkWorld x = x

export
discard : (1 sl : Slice n a) -> ()
discard (MkSlice _ _) = ()

export
splitAtCont : 
    (n : Nat) -> 
    (1 sl : Slice (n + m) a) -> 
    (1 f : (1 _ : Slice n a) -> (1 _ : Slice m a) -> (1 tok : %World) -> CRes b (LPair %World (LPair (Slice n a) (Slice m a)))) 
    -> CRes b (Slice (n + m) a)
splitAtCont n (MkSlice offset buffer) f = let
    v # (tok # (x # y)) = f (MkSlice offset buffer) (MkSlice (offset + n) buffer) %MkWorld
    () = Slice.discard x
    () = Slice.discard y
    in v # unsafeDestroyWorld tok (MkSlice offset buffer)

export
get : 
    Trivial a =>
    (1 sl : Slice n a) -> 
    (i : Nat) -> 
    (0 prf : i < n = True) -> 
    CRes a (Slice n a)
get (MkSlice offset buffer) i _ = let
    idx = cast (offset + i) 
    val = unsafePerformIO $ primIO (readBy buffer idx)
    in val # MkSlice offset buffer

export
set : 
    Trivial a =>
    (1 sl : Slice n a) -> 
    (i : Nat) -> 
    (0 prf : i < n = True) -> 
    a -> 
    Slice n a
set (MkSlice offset buffer) i _ val = let
    idx = cast (offset + i)
    in unsafePerformIO $ do
        primIO (writeBy buffer idx val)
        pure (MkSlice offset buffer)

export
updateAt : 
    Trivial a =>
    (1 sl : Slice n a) ->
    (i : Nat) ->
    (0 prf : i < n = True) ->
    (f : a -> a) ->
    Slice n a
updateAt sl i prf f = let
    x # sl = Slice.get sl i prf
    in Slice.set sl i prf (f x)

export
swap : 
    Trivial a => 
    (1 sl : Slice n a) -> 
    (i, j : Nat) -> 
    (0 _ : i < n = True) -> 
    (0 _ : j < n = True) -> 
    Slice n a
swap sl i j p1 p2 = let
    vi # sl = Slice.get sl i p1
    vj # sl = Slice.get sl j p2
    sl = Slice.set sl i p1 vj
    sl = Slice.set sl j p2 vi 
    in sl

export
finish : 
    (1 sl : Slice n a) ->
    b ->
    Ur b
finish (MkSlice _ _) res = MkUr res

find_if : Trivial a => (a -> Bool) -> (n : Nat) -> (1 sl : Slice n a) -> CRes (Maybe Nat) (Slice n a)
find_if p n sl = let
    go : Nat -> (1 sl : Slice n a) -> CRes (Maybe Nat) (Slice n a)
    go i sl = case decEq (i < n) True of
        (Yes prf) => let
            v # sl = get sl i prf 
            in if p v 
                then (Just i) # sl
                else go (S i) sl
        (No contra) => Nothing # sl
    in go 0 sl

||| Split array into two groups, where the first one forall x. p x = true and second one is forall x. p x = false
||| Returns first element of the second group
export
partition : Trivial a => (a -> Bool) -> (n : Nat) -> (1 sl : Slice n a) -> CRes Nat (Slice n a)
partition p n sl = let
    first_not # sl = find_if (not . p) n sl
    go : Nat -> Nat -> (1 sl : Slice n a) -> CRes Nat (Slice n a)
    go fst_not i sl = case decEq (i < n) True of 
        (Yes prf) => let
            v # sl = get sl i prf
            in if p v
                -- FIXME: should be implemented without believe_me
                then go (S fst_not) (S i) (swap sl fst_not i (believe_me ()) prf)
                else go fst_not (S i) sl
        (No contra) => fst_not # sl
    in case first_not of
        (Just fst_not) => go fst_not (S fst_not) sl
        Nothing => n # sl

partition' : Ord a => Trivial a => a -> (n : Nat) -> (1 sl : Slice n a) -> CRes Nat (Slice n a)
partition' v n sl = let
    go : Nat -> Nat -> (1 sl : Slice n a) -> CRes Nat (Slice n a)
    go l r sl = if l >= r 
        then r # sl
        else let
            lv # sl = Slice.get sl l (believe_me ())
            rv # sl = Slice.get sl r (believe_me ()) 
        in if lv < v
            then go (S l) r sl
            else if rv > v
                then go l (r `minus` 1) sl
                else go (S l) (r `minus` 1) (swap sl l r (believe_me ()) (believe_me ())) 
    in go 0 (n `minus` 1) sl


splitNat : (k, n : Nat) -> (m : Nat ** k + m = n)
splitNat k n = (n `minus` k ** believe_me ())

export
foldl : Trivial a => (f : a -> acc -> acc) -> acc -> (n : Nat) -> (1 this : Slice n a) -> CRes acc (Slice n a)
foldl f ac n sl = let 
    go : Nat -> acc -> (1 sl : Slice n a) -> CRes acc (Slice n a)
    go i ac sl = case decEq (i < n) True of 
        (Yes prf) => let
            x # sl = Slice.get sl i prf
            in go (S i) (f x ac) sl 
        (No contra) => ac # sl 
    in go 0 ac sl

export
quickSort : Ord a => Trivial a => (n : Nat) -> (1 sl : Slice n a) -> Slice n a
quickSort n sl = if n <= 1 
    then sl
    else let
        pivot # sl = get sl (n `div` 2) (believe_me ())
        border # sl = partition (< pivot) n sl
        correctBorder : Nat -> (1 sl : Slice n a) -> CRes Nat (Slice n a)
        correctBorder n sl = if border == 0
            then S border # Slice.swap sl 0 (n `div` 2) (believe_me ()) (believe_me ())
            else border # sl
        in let 
            border # sl = correctBorder n sl  
            (rest ** prf) = splitNat border n
            () # sl = splitAtCont {m = rest} border (rewrite prf in sl) $ \lhs, rhs, tok => let 
                lhs = quickSort border lhs
                rhs = quickSort rest rhs
                in () # (tok # (lhs # rhs))
        in rewrite (sym $ prf) in sl
           