module Mem.Represent

import Data.Bool
import Data.Nat
import Data.Vect
import public Data.HVect
import Data.Fun
import public Data.Fun.Extra

public export
interface Represent (ts : Vect n Type) (f : Fun ts Bool) (p : Fun ts Type) where
    fRepresentP : {vs : HVect ts} -> uncurry f vs = True -> uncurry p vs
    
    pRepresentF : {vs : HVect ts} -> uncurry p vs -> uncurry f vs = True

    notPThenFalse : {vs : HVect ts} -> Not (uncurry p vs) -> uncurry f vs = False
    notPThenFalse contra = notTrueIsFalse (\fIsTrue => contra $ fRepresentP {f=f} fIsTrue)

    FalseThenNotP : {vs : HVect ts} -> uncurry f vs = False -> Not (uncurry p vs)
    FalseThenNotP {vs} fIsFalse = \pVal => let
        fIsTrue = pRepresentF {f=f} pVal
        trueIsFalse : (True = False) = rewrite sym $ fIsTrue in fIsFalse
        in absurd trueIsFalse


public export
[NatEq] Represent [Nat, Nat] (==) Equal where
    fRepresentP {vs = [x, y]} prf = natEqToEq prf
        where
        natEqToEq : {x, y : Nat} -> (x == y = True) -> x = y
        natEqToEq {x = 0} {y = 0} prf = Refl 
        natEqToEq {x = 0} {y = (S k)} prf = absurd prf
        natEqToEq {x = (S k)} {y = 0} prf = absurd prf
        natEqToEq {x = (S k)} {y = (S j)} prf = cong S $ natEqToEq prf

    pRepresentF {vs = [x, y]} prf = eqToNatEq prf
        where
        eqToNatEq : {x, y : Nat} -> (x = y) -> (x == y = True)
        eqToNatEq {x = 0} {y = 0} Refl = Refl
        eqToNatEq {x = (S k)} {y = (S k)} Refl = eqToNatEq Refl

public export
[NatLT] Represent [Nat, Nat] (<) LT where
    fRepresentP {vs = [x, y]} = helper x y
        where
        helper : (x, y : Nat) -> (x < y = True) -> x `LT` y
        helper 0 0 prf = absurd prf
        helper 0 (S k) prf = LTESucc LTEZero
        helper (S k) 0 prf = absurd prf
        helper (S k) (S j) prf = LTESucc (helper k j prf)

    pRepresentF {vs = [x, y]} = helper x y
        where
        helper : (x, y : Nat) -> x `LT` y -> x < y = True
        helper 0 (S right) (LTESucc z) = Refl
        helper (S k) (S right) (LTESucc z) = helper k right z
