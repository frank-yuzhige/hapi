# Questions for supervisors after Christmas break

## General Questions
- Code visibility?
  - Black box? Grey box? White box?
  - More general, more black box, less effective

- http, grpc, or FFI, or both? Other options?
  - http/grpc: Both can be extended to other languages easily. Can remote fuzz. grpc more compact.
  - FFI: Better performance, no wrapper layer required, no network involved.

- Difference between property and libspec
  - Libspec going to be cumbersome?

- Gen and shrink property?
  - Papers?
  - Existing tools?
  - Symbolic execution?

- Datatype diff
  - C has __int32_t, __int64_t, __uint32_t, etc.
  - Java has int, Integer, BigInteger, etc.
  - How to unify datatypes

- Wrapper recover from segfault in C/C++/unsafe rust/...
  - Ditto to FFI

- Papers?
  - A lot of fuzzer papers focusing on fuzzing techniques and tools
  - Cadar paper: Fuzzing: Challenges and Reflections
    -
  - Papers focusing on technique unifications (e.g. Someone used monad transformer to implement fuzzer with different fuzzing techniques)

## Haskell Questions
- How to implement `sized` in `GenA`?


# Current Design

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
