# Questions for supervisors after Christmas break

## General Questions
- Code visibility?
  - Black box? Grey box? White box?
  - To support multiple languages, more black box, less effective
  - To support C/C++ only, more info, how to utilize the info?
    -  FFI with coverage?
    -  RPC encode coverage?
      - How does wrapper API gets the coverage?

- Difference between property and libspec
  - Libspec going to be cumbersome?

- Gen and shrink property?
  - i.e. Feedback-directed random generation of monadic construct in Haskell
  - Papers?
  - Existing tools?

- Papers?
  - Cadar paper: Fuzzing: Challenges and Reflections
    - Foci presented in this paper, approach these?
      - Benchmarking (different handler in same semantics, more reliable comparison)
      - Usability (TTH-based DSL for writing spec)
      - Optimization (Efficiency of fuzzer matters, involve `seq` and stuff)
  - A lot of fuzzer papers focusing on fuzzing techniques and tools
  - Papers focusing on technique unifications
    - Quickcheck-monad

- Wrapper recover from segfault in C/C++/unsafe rust/...
  - Ditto to FFI

- FFI, http, grpc, all of them? Other options?
  - http/grpc: Both can be extended to other languages easily. Can remote fuzz. grpc more compact.
  - FFI: Better performance, no wrapper layer required, no network involved.

- Datatype diff
  - C has __int32_t, __int64_t, __uint32_t, etc.
  - Java has int, Integer, BigInteger, etc.
  - Unify data types brings
    - Reusability of property
    - Test language A lib against a trustworthy language B implementation
    - But what would be an elegant way?
      - Global "core" spec (int, char, bool, etc.)
      - Projection onto different languages' datatype


# Current Design

```
lib C ArithApi:
  fun add(int, int): int
  fun neg(int a): int
    where a <= 100000 and a >= -100;
  <function defs...>

  expect add(a, b)



```

### Effects
- LibSpec (maybe TH-based DSL): Describes the behaviour of a range of libraries.
  - `runGrpcWrapperGen <language-id>`: Generates lib wrapper binding for `language`.
  - `runGrpcFuzz <port>`: (after wrapper is running), start a Procedure session with api wrapper.
  - `runFFIFuzz`: run test in FFI style
  - `runHaskell`: If user provides haskell binding for the lib, we can invoke these apis in haskell directly
  - ...

- Property: Describes the property of the api (e.g. `do { somelist <- arbitrary @[Int]; reverse(reverse(somelist)) === somelist}`)
  - `runProcedureGen`


# To check
- FuzzCheck https://hackage.haskell.org/package/fuzzcheck
