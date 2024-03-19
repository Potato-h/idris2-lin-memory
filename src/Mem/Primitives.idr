module Mem.Primitives

public export
interface Trivial (a : Type) where
    sizeof : Int

    readBy : AnyPtr -> (offset : Int) -> PrimIO a

    writeBy : AnyPtr -> (offset : Int) -> (value : a) -> PrimIO ()

public export
sizeOf : (a : Type) -> {auto p : Trivial a} -> Int
sizeOf _ = sizeof @{p}

%foreign "C:read_ptr,libsmall"
readInt : AnyPtr -> (offset : Int) -> PrimIO Int

%foreign "C:write_ptr,libsmall"
writeInt : AnyPtr -> (offset : Int) -> (value : Int) -> PrimIO ()

%foreign "C:my_memcpy,libsmall"
export memcpy : (dest : AnyPtr) -> (src : AnyPtr) -> (bytes : Int) -> PrimIO ()

public export
Trivial Int where
    sizeof = 4
    readBy = readInt 
    writeBy = writeInt