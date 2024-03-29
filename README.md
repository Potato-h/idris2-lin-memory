### TODO

- Benchmarks
- Implement Deque
- Examples of algorithms with Stack and Queue
- Support derive for `Trivial`
- ~~Make `Trivial a` constraint erase `a`~~

```
# 1: Benches/eval/mem/length = 2047
  time per run : 5.880 ms
  mean         : 1.846 ms
  r2           : 0.1605322444618475


# 2: Benches/eval/mem/length = 65535
  time per run : 26.64 ms
  mean         : 34.70 ms
  r2           : 1.1392011307567034


# 3: Benches/eval/mem/length = 2097151
  time per run : 1.516  s
  mean         : 1.393  s
  r2           : 0.994776493368175


# 4: Benches/eval/mem/length = 16777215
  time per run : 11.06  s
  mean         : 11.02  s
  r2           : 0.9994881456572575


# 5: Benches/eval/monad/length = 2047
  time per run : 469.1 μs
  mean         : 563.1 μs
  r2           : 0.007963797582472947


# 6: Benches/eval/monad/length = 65535
  time per run : 26.63 ms
  mean         : 11.62 ms
  r2           : 0.2355293890606915


# 7: Benches/eval/monad/length = 2097151
  time per run : 461.0 ms
  mean         : 381.8 ms
  r2           : 0.6744108640866439


# 8: Benches/eval/monad/length = 16777215
  time per run : 3.719  s
  mean         : 3.856  s
  r2           : 0.9979632012102981
```