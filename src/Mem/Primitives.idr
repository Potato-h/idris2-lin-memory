module Mem.Primitives

import Generics.Derive
import Data.HVect
import Control.Monad.State.State
import Control.Monad.Identity

-- FIXME: Integer instead of Int is hardcoded (probably unsound) optimization

public export
interface Trivial a where
    sizeof : Integer

    shiftPtr : AnyPtr -> (offset : Integer) -> AnyPtr

    readBy : AnyPtr -> (offset : Integer) -> PrimIO a

    writeBy : AnyPtr -> (offset : Integer) -> (value : a) -> PrimIO ()

public export
sizeOf : (0 a : Type) -> {auto p : Trivial a} -> Integer
sizeOf _ = sizeof @{p}

export %foreign "scheme,chez:foreign-alloc"
malloc : (bytes : Integer) -> PrimIO AnyPtr

export %foreign "scheme,chez:foreign-free"
free : (ptr : AnyPtr) -> PrimIO ()

-- FIXME:
%foreign "scheme,chez:(foreign-sizeof 'int)"
sizeOfInt : Integer

%foreign "scheme,chez:(lambda (ptr offset) (fx+ ptr (fx* offset (foreign-sizeof 'int))))"
shiftIntPtr : AnyPtr -> (offset : Integer) -> AnyPtr

%foreign "scheme,chez:(lambda (ptr offset) (foreign-ref 'int ptr (fx* offset (foreign-sizeof 'int))))"
readInt : AnyPtr -> (offset : Integer) -> PrimIO Int

%foreign "scheme,chez:(lambda (ptr offset value) (foreign-set! 'int ptr (fx* offset (foreign-sizeof 'int)) value))"
writeInt : AnyPtr -> (offset : Integer) -> (value : Int) -> PrimIO ()

export %foreign "scheme,chez:(foreign-procedure \"memcpy\" (void* void* int) void)"
memcpy : (dest : AnyPtr) -> (src : AnyPtr) -> (bytes : Integer) -> PrimIO ()

public export
Trivial Int where
    sizeof = 4
    shiftPtr = shiftIntPtr
    readBy = readInt 
    writeBy = writeInt
