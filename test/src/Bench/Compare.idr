module Bench.Compare

import Data.Stream
import Mem.Vector
import Mem.Array
import Data.List
import Profile
import Control.Monad.State.State
import Control.Monad.State.Interface
import Control.Monad.Identity
import Decidable.Equality
import Tests.Simple

data Op = Add | Sub | Mul | Div

data Expr : Type where
    EValue : Int -> Expr
    EBinary : Op -> Expr -> Expr -> Expr

evalOp : Op -> Int -> Int -> Maybe Int
evalOp Add x y = Just $ x + y
evalOp Sub x y = Just $ x - y
evalOp Mul x y = Just $ x * y
evalOp Div x y = if y /= 0 then Just $ x `div` y else Nothing

evalExpr : Expr -> Maybe Int
evalExpr (EValue i) = Just i
evalExpr (EBinary x i j) = do evalOp x !(evalExpr i) !(evalExpr j)

makeExpr : Nat -> Stream Int -> Expr
makeExpr 0 (x :: xs) = EValue x
makeExpr (S k) (x :: xs) = let
    op = case x `mod` 4 of
        0 => Add
        1 => Sub
        2 => Mul
        _ => Div
    in EBinary op (makeExpr k xs) (makeExpr k (drop 10 xs))

data Token : Type where
    TOp : Op -> Token
    Value : Int -> Token

exprToTokens : Expr -> List Token
exprToTokens (EValue i) = [Value i]
exprToTokens (EBinary x y z) = exprToTokens y ++ exprToTokens z ++ [TOp x]

eval : List Token -> Maybe Int
eval toks = withVector {a = Int} $ \st => let
    x # st = go st toks
    in vFinish st x
    where
    go : (1 st : Vector Int) -> List Token -> CRes (Maybe Int) (Vector Int)
    go st [] = let
        x # st = Vector.pop st
        isempty # st = Vector.isEmpty st
        in (if isempty then x else Nothing) # st
    go st ((TOp op) :: xs) = let
        x1 # st = Vector.pop st
        x2 # st = Vector.pop st
        res = do evalOp op !x1 !x2 
        in case res of 
            Nothing => Nothing # st
            (Just x) => go (Vector.push st x) xs
    go st ((Value v) :: xs) = go (Vector.push st v) xs

eval' : List Token -> Maybe Int
eval' toks = evalState [] (go toks)
    where
    go : List Token -> State (List Int) (Maybe Int)
    go [] = do
        [res] <- get | _ => pure Nothing
        pure $ Just res
    go ((TOp op) :: toks) = do
        (x1 :: x2 :: xs) <- get | _ => pure Nothing
        let (Just res) = evalOp op x1 x2 | _ => pure Nothing 
        put (res :: xs)
        go toks
    go ((Value i) :: toks) = do
        modify (i ::)
        go toks

tree : Nat -> List Token
tree n = exprToTokens $ makeExpr n (iterate (+1) 0)

export
nxtR : Int -> Int
nxtR x = (13 + x * 127) `mod` 1000

linearSum : Nat -> List Token
linearSum n = map Value (take (S n) (iterate nxtR 0)) ++ List.replicate n (TOp Add)

evalMemBench : Nat -> Benchmark Void
evalMemBench n = let toks = tree n in Single "length = \{show $ length toks}" (basic eval toks) 

evalMemBenchFold : Nat -> Benchmark Void
evalMemBenchFold n = let toks = linearSum n in Single "length = \{show n}" (basic eval toks)

evalMonadBench : Nat -> Benchmark Void
evalMonadBench n = let toks = tree n in Single "length = \{show $ length toks}" (basic eval' toks)

evalMonadBenchFold : Nat -> Benchmark Void
evalMonadBenchFold n = let toks = linearSum n in Single "length = \{show n}" (basic eval' toks)

export
bench : Benchmark Void
bench = Group "Benches"
    [ Group "eval"
        [ Group "mem" 
            [ evalMemBench 10
            , evalMemBench 15
            , evalMemBench 20
            , evalMemBenchFold 2_000_000
            ] 
        , Group "monad"
            [ evalMonadBench 10
            , evalMonadBench 15
            , evalMonadBench 20
            , evalMonadBenchFold 2_000_000
            ]
        ]
    ]

goUp : Nat -> Nat
goUp to = let
    go : Nat -> Nat -> Nat
    go i acc = case decEq (i < to) True of
        (Yes prf) => go (S i) (acc + i)
        (No contra) => acc
    in go 0 0

goUpCase : Nat -> Nat
goUpCase to = let
    go : Nat -> Nat -> Nat
    go i acc = case i < to of 
        True => go (S i) (acc + i) 
        False => acc
    in go 0 0

goUpIf : Nat -> Nat
goUpIf to = let
    go : Nat -> Nat -> Nat
    go i acc = if i < to then go (S i) (acc + i) else acc
    in go 0 0

-- CompilesInto
-- goUpInt
-- Can be dramaticly speed up with fx+ instead of bs+
-- (define BenchC-45Compare-n--6599-4082-u--go (lambda (arg-0 arg-1 arg-2) (let ((sc0 (PreludeC-45EqOrd-u--C-60_Ord_Int arg-1 arg-0))) (cond ((equal? sc0 1) (BenchC-45Compare-n--6599-4082-u--go arg-0 (bs+ arg-1 1 63) (bs+ arg-2 arg-1 63))) (else arg-2)))))
goUpInt : Int -> Int
goUpInt to = let
    go : Int -> Int -> Int
    go i acc = if i < to then go (i + 1) (acc + i) else acc
    in go 0 0

-- CompilesInto
-- goUpInteger
-- (define BenchC-45Compare-n--6653-4133-u--go (lambda (arg-0 arg-1 arg-2) (let ((sc0 (PreludeC-45EqOrd-u--C-60_Ord_Integer arg-1 arg-0))) (cond ((equal? sc0 1) (BenchC-45Compare-n--6653-4133-u--go arg-0 (+ arg-1 1) (+ arg-2 arg-1))) (else arg-2)))))
goUpInteger : Integer -> Integer
goUpInteger to = let
    go : Integer -> Integer -> Integer
    go i acc = if i < to then go (i + 1) (acc + i) else acc
    in go 0 0

goUpIntegerWithCast : Integer -> Integer
goUpIntegerWithCast to = let
    go : Integer -> Integer -> Integer
    go i acc = let
        acc : Int = cast acc
        acc : Integer = cast acc
        in if i < to then go (i + 1) (acc + i) else acc
    in go 0 0

goUpNatWithCast : Nat -> Nat
goUpNatWithCast to = let
    go : Nat -> Nat -> Nat
    go i acc = let
        acc : Int = cast acc
        acc : Nat = cast acc
        in if i < to then go (i + 1) (acc + i) else acc
    in go 0 0

goUpNatWithCastInteger : Nat -> Nat
goUpNatWithCastInteger to = let
    go : Nat -> Nat -> Nat
    go i acc = let
        acc : Integer = cast acc
        acc : Nat = cast acc
        in if i < to then go (i + 1) (acc + i) else acc
    in go 0 0

goUpDecWithCast : Nat -> Nat
goUpDecWithCast to = let
    go : Nat -> Nat -> Nat
    go i acc = case decEq (i < to) True of
        (Yes prf) => let 
            acc : Integer = cast acc
            acc : Nat = cast acc
            in go (S i) (acc + i)
        (No contra) => acc
    in go 0 0



export
intBench : Benchmark Void
intBench = let 
    nNat : Nat = 500_000
    nInt : Int = 500_000
    nInteger : Integer = 500_000
    in Group "GoUp"
    [ Single "NatDec" (basic goUp nNat)
    , Single "NatCase" (basic goUpCase nNat)
    , Single "NatIf" (basic goUpIf nNat)
    , Single "Int" (basic goUpInt nInt)
    , Single "Integer" (basic goUpInteger nInteger)
    , Single "IntegerCast" (basic goUpIntegerWithCast nInteger)
    , Single "NatCast" (basic goUpNatWithCast nNat)
    , Single "NatCastInteger" (basic goUpNatWithCastInteger nNat)
    , Single "DecWithCast" (basic goUpDecWithCast nNat)
    ]

partition' : (a -> Bool) -> List a -> List a
partition' p xs = let (l, r) = partition p xs in l ++ r

export
genN : Nat -> (a -> a) -> a -> List a
genN n f x = let
    go : Nat -> List a -> a -> List a
    go 0 xs acc = xs
    go (S k) xs acc = go k (acc :: xs) (f acc)  
    in go n [] x


export 
simpleInitPure : List a -> List a
simpleInitPure = Prelude.foldl (\acc, x => Basics.(::) x acc) []

-- ~ 17ns per push_back without allocations in idris
-- ~ 1.6ns per push_back without allocations in rust
export
partitionBench : Benchmark Void
partitionBench = let
    n = 500_000
    xs = genN n nxtR 5
    in Group "Partition" 
    [ Single "Pure" (basic (partition (< 400)) xs)
    , Single "Pure'" (basic (partition' (< 400)) xs)
    , Single "ListLength" (basic length xs)
    , Single "Gen" (basic (\n => genN n nxtR 5) n)
    , Single "Linear" (basic (partitionExample 400) xs)
    , Single "Linear'" (basic (partition'Example 400) xs)
    , Single "BuildList" (basic buildStuff xs)
    , Single "SimpleInit" (basic simpleInit xs)
    , Single "SimpleInitPure" (basic simpleInitPure xs)
    , Single "EmptyInit" (basic emptyInit ())
    , Single "SingleCon" (basic (\x => Basics.(::) 10 x) [1, 2, 3])
    , Single "SingleInit" (basic simpleInit [10])
    ]


quicksort : Ord a => List a -> List a
quicksort xs = if length xs < 2 
    then xs
    else let
        pivot = List.index (length xs `div` 2) xs @{believe_me ()}
        lhs = filter (< pivot) xs
        center = filter (== pivot) xs
        rhs = filter (> pivot) xs
        in quicksort lhs ++ center ++ quicksort rhs 

export
sortBench : Benchmark Void
sortBench = let
    n = 500_000
    xs = genN n nxtR 5
    in Group "Sort"
    [ Single "Linear" (basic sortExample xs)
    , Single "Pure" (basic quicksort xs)
    , Single "BuildList" (basic buildStuff xs)
    ]