module Tests.Simple

import Mem.Vector
import Mem.Array
import Mem.Queue

example1 : (1 arr : Vector Int) -> Ur (List (Maybe Int)) 
example1 v = let
    v = Vector.push v 10
    v = Vector.push v 20
    v = Vector.push v 30
    v = Vector.push v 40
    v = Vector.push v 50
    x1 # v = Vector.pop v
    x2 # v = Vector.pop v
    x3 # v = Vector.pop v
    x4 # v = Vector.pop v
    x5 # v = Vector.pop v
    x6 # v = Vector.pop v
    in vFinish v [x1, x2, x3, x4, x5, x6]

example2 : (1 arr : Vector Int) -> Ur (List (Maybe Int))
example2 v = let
    v = Vector.push v 10
    v = Vector.push v 20
    x1 # v = Vector.pop v
    v = Vector.push v 30
    x2 # v = Vector.pop v
    x3 # v = Vector.pop v
    in vFinish v [x1, x2, x3]

example3 : (1 q : Queue Int) -> Ur (List (Maybe Int))
example3 q = let
    q = Queue.push q 10
    q = Queue.push q 20
    x1 # q = Queue.pop q
    q = Queue.push q 30
    x2 # q = Queue.pop q
    x3 # q = Queue.pop q
    x4 # q = Queue.pop q
    in qFinish q [x1, x2, x3, x4]

withWithExample : Int
withWithExample = 
    withVector {a = Int} $ \vec1 =>
    withVector {a = Int} $ \vec2 => 
    let (MkUr ()) = vFinish vec1 ()
    in vFinish vec2 (MkUr 10)