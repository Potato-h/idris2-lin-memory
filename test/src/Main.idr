module Main

import Profile
import Bench.Compare

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

main : IO ()
main = do
    runDefault (const True) Details absurd bench