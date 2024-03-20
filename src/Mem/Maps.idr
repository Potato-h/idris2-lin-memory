module Mem.Maps

import Data.Nat
import Data.Bool
import Decidable.Equality
import Mem.Represent
import public Mem.Extensionality

public export
data Cell = Empty | NonEmpty | NonExisted

public export
CellMap : Type
CellMap = Nat -> Cell

public export
setAt : CellMap -> Nat -> Cell -> CellMap
setAt mp idx v = \i => if i == idx then v else mp i

export
setSameAt : (mp : CellMap) -> (idx : Nat) -> (i : Nat) -> setAt mp idx (mp idx) i = mp i
setSameAt mp idx i with (i == idx) proof eq
    _ | False = Refl
    _ | True = cong mp (sym $ fRepresentP @{NatEq} {vs = [i, idx]} eq)
   
export
setSame : (mp : CellMap) -> (idx : Nat) -> setAt mp idx (mp idx) -=- mp 
setSame mp idx = Ext $ \i => setSameAt mp idx i

export
setKnown : (mp : CellMap) -> (idx : Nat) -> (prf : mp idx = v) -> setAt mp idx v -=- mp
setKnown mp idx prf = rewrite sym prf in setSame mp idx

export
setValueAt : (mp : CellMap) -> (i : Nat) -> {v : Cell} -> (setAt mp i v) i = v
setValueAt mp i {v} = rewrite pRepresentF @{NatEq} {vs = [i, i]} Refl in Refl

export
setCancelAt : (mp : CellMap) -> (i : Nat) -> (setAt (setAt mp i v1) i v2) i = v2
setCancelAt mp i = rewrite pRepresentF @{NatEq} {vs = [i, i]} Refl in Refl

export
setCancel : (mp : CellMap) -> (i : Nat) -> setAt (setAt mp i v1) i v2 -=- setAt mp i v2
setCancel mp i = Ext $ \idx => case (idx `decEq` i) of 
    (Yes prf) => rewrite prf in rewrite pRepresentF @{NatEq} {vs = [i, i]} Refl in Refl
    (No contra) =>  rewrite notPThenFalse @{NatEq} {vs = [idx,i]} contra in 
                    rewrite notPThenFalse @{NatEq} {vs = [idx,i]}contra in Refl

public export
allEmpty : Nat -> CellMap
allEmpty n = \i => if i < n then Empty else NonExisted

public export
allNonEmpty : Nat -> CellMap
allNonEmpty n = \i => if i < n then NonEmpty else NonExisted

export
n_less_zero_is_absurd : (n : Nat) -> n < 0 = False
n_less_zero_is_absurd 0 = Refl
n_less_zero_is_absurd (S j) = Refl

public export
prefixMap : (n, k : Nat) -> CellMap
prefixMap n k = \i =>   if i < n then NonEmpty else 
                        if i < n + k then Empty else 
                        NonExisted

export
emptySuffix : (n : Nat) -> prefixMap n 0 -=- allNonEmpty n
emptySuffix n = Ext $ \i => case (i < n `decEq` True) of
    (Yes prf) => rewrite prf in Refl 
    (No contra) => rewrite notTrueIsFalse contra in 
        rewrite plusZeroRightNeutral n in 
        rewrite notTrueIsFalse contra in Refl

export
emptyPrefix : (n : Nat) -> prefixMap 0 n -=- allEmpty n
emptyPrefix n = Ext $ \i => 
    rewrite n_less_zero_is_absurd i in 
    case (i < n `decEq` True) of 
        (Yes prf) => rewrite prf in Refl
        (No contra) => rewrite notTrueIsFalse contra in Refl

export
n_less_n_is_absurd : (n : Nat) -> n < n = False
n_less_n_is_absurd 0 = Refl
n_less_n_is_absurd (S k) = n_less_n_is_absurd k

export
i_more_n_then_i_less_s_n_is_absurd : (i, n : Nat) -> (i < n = False) -> (Not (i = n)) -> i < S n = False
i_more_n_then_i_less_s_n_is_absurd 0 0 _ i_not_n = absurd (i_not_n Refl)
i_more_n_then_i_less_s_n_is_absurd 0 (S j) i_less_n _ = i_less_n
i_more_n_then_i_less_s_n_is_absurd (S j) 0 _ _ = n_less_zero_is_absurd j
i_more_n_then_i_less_s_n_is_absurd (S j) (S i) prf1 prf2 = i_more_n_then_i_less_s_n_is_absurd j i prf1 (\p => prf2 $ cong S p)

export
n_less_n_plus_k : (n, k : Nat) -> n < n + (S k) = True
n_less_n_plus_k 0 0 = Refl 
n_less_n_plus_k (S j) 0 = n_less_n_plus_k j 0
n_less_n_plus_k 0 (S k) = Refl
n_less_n_plus_k (S j) (S k) = n_less_n_plus_k j (S k)

export
n_less_s_n : (n : Nat) -> n < S n = True
n_less_s_n 0 = Refl
n_less_s_n (S k) = n_less_s_n k

export
pushToPrefixPreservePrefix : (n, k : Nat) -> setAt (prefixMap n (S k)) n NonEmpty -=- prefixMap (S n) k
pushToPrefixPreservePrefix n k = Ext $ \i => lemma n k i
    where
    lemma : (n, k, i : Nat) -> setAt (prefixMap n (S k)) n NonEmpty i = prefixMap (S n) k i
    lemma n k i with (i < n) proof i_less_n | (i == n) proof i_eq_n
        _ | False | False = 
            rewrite i_less_n in
            rewrite i_more_n_then_i_less_s_n_is_absurd i n i_less_n (FalseThenNotP @{NatEq} {vs = [i, n]} i_eq_n) in
            rewrite plusSuccRightSucc n k in
            case (i < n + S k) `decEq` True of 
                (Yes prf) => rewrite prf in Refl 
                (No contra) => rewrite notTrueIsFalse contra in Refl
        _ | False | True = 
            rewrite fRepresentP @{NatEq} {vs = [i, n]} i_eq_n in let
            n_less_s_n : (n < S n = True) = pRepresentF @{NatLT} {vs = [n, S n]} reflexive
            in rewrite n_less_s_n in Refl
        _ | True | False =
            rewrite i_less_n in let
                factCheck : (i `LT` S n) = transitive (fRepresentP @{NatLT} {vs = [i, n]} i_less_n) (lteSuccRight reflexive)
                condCheck : (i < (S n) = True) = pRepresentF @{NatLT} {vs = [i, S n]} factCheck in 
            rewrite condCheck in
            Refl
        _ | True | True = let
                factCheck : (i `LT` S n) = transitive (fRepresentP @{NatLT} {vs = [i, n]} i_less_n) (lteSuccRight reflexive)
                condCheck : (i < (S n) = True) = pRepresentF @{NatLT} {vs = [i, S n]} factCheck in
            rewrite condCheck in
            Refl


export
popFromPrefixPreservePrefix : (n, k : Nat) -> setAt (prefixMap (S n) k) n Empty -=- prefixMap n (S k)
popFromPrefixPreservePrefix n k = Ext $ \i => lemma n k i
    where
    n_less_n_is_absurd : (n : Nat) -> Not (n < n = True)
    n_less_n_is_absurd 0 x = absurd x     
    n_less_n_is_absurd (S j) x = n_less_n_is_absurd j x
    
    lemma : (n, k, i : Nat) -> setAt (prefixMap (S n) k) n Empty i = prefixMap n (S k) i
    lemma n k i with (i < n) proof i_less_n | (i == n) proof i_eq_n
        _ | False | False = 
            rewrite i_more_n_then_i_less_s_n_is_absurd i n i_less_n (FalseThenNotP @{NatEq} {vs = [i, n]} i_eq_n) in
            rewrite plusSuccRightSucc n k in
            case (i < n + S k) `decEq` True of
                (Yes prf) => rewrite prf in Refl
                (No cont) => rewrite notTrueIsFalse cont in Refl
        _ | False | True = 
            rewrite fRepresentP @{NatEq} {vs = [i, n]} i_eq_n in
            rewrite n_less_n_plus_k n k in
            Refl
        _ | True | False = let 
            condCheck : (i < (S n) = True) = pRepresentF @{NatLT} {vs = [i, S n]} $ transitive (fRepresentP @{NatLT} {vs = [i, n]} i_less_n) (lteSuccRight reflexive) in 
            rewrite condCheck in
            Refl
        _ | True | True = absurd $ n_less_n_is_absurd n (replace {p = \h => h < n = True} (fRepresentP @{NatEq} {vs = [i, n]} i_eq_n) i_less_n)

