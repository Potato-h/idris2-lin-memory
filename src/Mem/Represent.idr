module Mem.Represent

import Data.Bool
import Data.Nat

-- TODO: Generilize for n-anry relations and functions
public export
interface Represent (a : Type) (f : a -> a -> Bool) (p : a -> a -> Type) where
    fRepresentP : {x, y : a} -> f x y = True -> p x y
    
    pRepresentF : {x, y : a} -> p x y -> f x y = True

    notPThenFalse : {x, y : a} -> Not (p x y) -> f x y = False
    notPThenFalse contra = notTrueIsFalse (\fIsTrue => contra $ fRepresentP {f=f} fIsTrue)

    FalseThenNotP : {x, y : a} -> f x y = False -> Not (p x y)
    FalseThenNotP {x} {y} fIsFalse = \pVal => let
        fIsTrue = pRepresentF {f=f} pVal
        trueIsFalse : (True = False) = rewrite sym $ fIsTrue in fIsFalse
        in absurd trueIsFalse

public export
[NatEq] Represent Nat (==) Equal where
    fRepresentP {x} {y} prf = natEqToEq prf
        where
        natEqToEq : {x, y : Nat} -> (x == y = True) -> x = y
        natEqToEq {x = 0} {y = 0} prf = Refl 
        natEqToEq {x = 0} {y = (S k)} prf = absurd prf
        natEqToEq {x = (S k)} {y = 0} prf = absurd prf
        natEqToEq {x = (S k)} {y = (S j)} prf = cong S $ natEqToEq prf

    pRepresentF {x} {y} prf = eqToNatEq prf
        where
        eqToNatEq : {x, y : Nat} -> (x = y) -> (x == y = True)
        eqToNatEq {x = 0} {y = 0} Refl = Refl
        eqToNatEq {x = (S k)} {y = (S k)} Refl = eqToNatEq Refl

public export
[NatLT] Represent Nat (<) LT where
    fRepresentP {x} {y} = helper x y
        where
        helper : (x, y : Nat) -> (x < y = True) -> x `LT` y
        helper 0 0 prf = absurd prf
        helper 0 (S k) prf = LTESucc LTEZero
        helper (S k) 0 prf = absurd prf
        helper (S k) (S j) prf = LTESucc (helper k j prf)

    pRepresentF {x} {y} = helper x y
        where
        helper : (x, y : Nat) -> x `LT` y -> x < y = True
        helper 0 (S right) (LTESucc z) = Refl
        helper (S k) (S right) (LTESucc z) = helper k right z