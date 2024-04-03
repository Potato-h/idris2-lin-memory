# idris2-lin-memory

This library provides memory safe abstraction to build mutable data structures with low level memory access implementation.


## API overview

Building block of all data structures is `Array a cm`, where `a` is type of element in a array and `cm` is `Nat -> Cell` that represents current map of cell's states in the array. `Cell` can be `Empty`, `NonEmpty` and `NonExisted`. We can allocate memory by `withArray n` that gives `Array a (allEmpty n)` where 
`allEmpty = \i => i < n then Empty else NonExisted`. 

`read` and `write` operations demands `cm i = NonEmpty` and `cm i = Empty` respectively. So freshly allocated array have only access to write operations. After cell was written it's allowed to read from it.

This API guarantees correct access with memory within allocated array (bounds check and correct work with uninitialized memory).

For example, inner representation of `Vector` also known as `std::vector` in C++, `ArrayList` in Java and `Vec` in Rust has the following form:

```idris
record Vector a where
    constructor MkVect
    len : Nat
    rest : Nat
    1 elems : Array a (prefixMap len rest)
``` 

## Benchmarks


```
# 1: Benches/eval/mem/length = 2047
  time per run : 620.9 μs
  mean         : 331.9 μs
  r2           : 0.18566366582279845


# 2: Benches/eval/mem/length = 65535
  time per run : 13.81 ms
  mean         : 9.664 ms
  r2           : 0.35149041334244213


# 3: Benches/eval/mem/length = 2097151
  time per run : 344.5 ms
  mean         : 321.8 ms
  r2           : 0.8993165482782934


# 4: Benches/eval/mem/length = 8388607
  time per run : 1.323  s
  mean         : 1.324  s
  r2           : 0.9999788585591938


# 5: Benches/eval/monad/length = 2047
  time per run : 281.4 μs
  mean         : 172.3 μs
  r2           : 0.09003441865006584


# 6: Benches/eval/monad/length = 65535
  time per run : 8.212 ms
  mean         : 8.854 ms
  r2           : 0.10751230197739857


# 7: Benches/eval/monad/length = 2097151
  time per run : 388.9 ms
  mean         : 345.6 ms
  r2           : 0.9433885754520189


# 8: Benches/eval/monad/length = 8388607
  time per run : 1.414  s
  mean         : 1.335  s
  r2           : 0.9777658584504395

```

## TODO
- ~~Benchmarks~~
- Implement Deque
- ~~Examples of algorithms with Stack~~
- Example of algorithms with Queue
- Support derive for `Trivial`
- ~~Make `Trivial a` constraint erase `a`~~
