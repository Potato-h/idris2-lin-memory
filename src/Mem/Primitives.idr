module Mem.Primitives

import Generics.Derive
import Data.HVect
import Control.Monad.State.State
import Control.Monad.Identity

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

public export
All Trivial ts => Trivial (HVect.HVect ts) where
  sizeof {ts = []} @{[]} = 0
  sizeof {ts = (x :: xs)} @{(t1 :: tr)} = sizeof @{t1} + sizeof {a = HVect.HVect xs}

  readBy ptr idx = toPrim $ do 
    ?adwj2

  writeBy = ?awdijawd2

public export
NP (Trivial . f) ks => Trivial (NP f ks) where
  sizeof {ks = []} @{[]} = 0
  sizeof {ks = (t :: ts)} @{(v :: vs)} = sizeof @{v} + ?later

  readBy ptr idx = toPrim $ do
    let reads = evalState 0 $ ?awd
    ?awodkawd

  writeBy ptr idx elems = toPrim $ do
    let writes = evalState 0 $ hctraverse (Trivial . f) (\x => ?awa) elems
    ?awdijawd

