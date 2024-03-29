module Bench.Compare

import Data.Stream
import Mem.Vector
import Mem.Array
import Profile
import Control.Monad.State.State
import Control.Monad.State.Interface
import Control.Monad.Identity

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

eval'' : List Token -> Maybe Int
eval'' toks = ?later
    where
    go : List Token -> (1 _ : List Int) -> CRes (Maybe Int) (List Int)
    go [] st = ?goal_0
    go ((TOp x) :: xs) st = ?goal_2
    go ((Value i) :: xs) st = go xs ?lllll


tree : Nat -> List Token
tree n = exprToTokens $ makeExpr n (iterate (+1) 0)

evalMemBench : Nat -> Benchmark Void
evalMemBench n = let toks = tree n in Single "length = \{show $ length toks}" (basic eval toks) 

evalMonadBench : Nat -> Benchmark Void
evalMonadBench n = let toks = tree n in Single "length = \{show $ length toks}" (basic eval' toks)

export
bench : Benchmark Void
bench = Group "Benches"
    [ Group "eval"
        [ Group "mem" 
            [ evalMemBench 10
            , evalMemBench 15
            , evalMemBench 20
            ] 
        , Group "monad"
            [ evalMonadBench 10
            , evalMonadBench 15
            , evalMonadBench 20
            ]
        ]
    ]