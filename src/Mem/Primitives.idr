module Mem.Primitives

public export
interface Trivial a where
    sizeof : Int

    readBy : AnyPtr -> (offset : Int) -> PrimIO a

    writeBy : AnyPtr -> (offset : Int) -> (value : a) -> PrimIO ()

public export
sizeOf : (0 a : Type) -> {auto p : Trivial a} -> Int
sizeOf _ = sizeof @{p}

%foreign "C:read_ptr,libprimitives"
readInt : AnyPtr -> (offset : Int) -> PrimIO Int

%foreign "C:write_ptr,libprimitives"
writeInt : AnyPtr -> (offset : Int) -> (value : Int) -> PrimIO ()

%foreign "C:my_memcpy,libprimitives"
export memcpy : (dest : AnyPtr) -> (src : AnyPtr) -> (bytes : Int) -> PrimIO ()

public export
Trivial Int where
    sizeof = 4
    readBy = readInt 
    writeBy = writeInt