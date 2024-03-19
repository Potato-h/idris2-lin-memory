module Main

import Mem.Vector
import Mem.Array

data Fmt = FArg Fmt | FChar Char Fmt | FEnd

toFmt : (fmt : List Char) -> Fmt
toFmt ('{' :: '}' :: xs) = FArg (toFmt xs)
toFmt (  x :: xs) = FChar x (toFmt xs)
toFmt [] = FEnd

PrintfType : (fmt : Fmt) -> Type
PrintfType (FArg fmt) = ({ty : Type} -> Show ty => (obj : ty) -> PrintfType fmt)
PrintfType (FChar _ fmt) = PrintfType fmt
PrintfType FEnd = String

printf : (fmt : String) -> PrintfType (toFmt $ unpack fmt)
printf fmt = printfAux (toFmt $ unpack fmt) [] where
    printfAux : (fmt : Fmt) -> List Char -> PrintfType fmt
    printfAux (FArg fmt) acc = \obj => printfAux fmt (acc ++ unpack (show obj))
    printfAux (FChar c fmt) acc = printfAux fmt (acc ++ [c])
    printfAux FEnd acc = pack acc

example1 : (1 arr : Vector Int) -> Ur (Maybe Int) 
example1 v = let
    v = push v 10
    v = push v 20
    _ # v = pop v
    _ # v = pop v
    x # v = pop v
    in vFinish v x

example2 : (1 arr : Vector Int) -> Ur (List (Maybe Int))
example2 v = let
    v = push v 10
    v = push v 20
    x1 # v = pop v
    v = push v 30
    x2 # v = pop v
    x3 # v = pop v
    in vFinish v [x1, x2, x3]

main : IO ()
main = do
    putStrLn $ printf "example1 result: {}" (withVector example1)
    putStrLn $ printf "example2 result: {}" (withVector example2)
