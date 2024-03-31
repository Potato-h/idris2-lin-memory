### TODO

- ~~Benchmarks~~
- Implement Deque
- ~~Examples of algorithms with Stack~~
- Example of algorithms with Queue
- Support derive for `Trivial`
- ~~Make `Trivial a` constraint erase `a`~~

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