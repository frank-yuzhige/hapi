# Questions for supervisors after Christmas break

- http, grpc, or FFI, or both? Other options?
  - http/grpc: Both can be extended to other languages easily. Can remote fuzz. grpc more compact.
  - FFI: Better performance, no wrapper layer required, no network involved.

- Difference between property and libspec
  - Is libspec going to be cumbersome to write?

- Gen and shrink property?
  -

- Datatype diff
  - C has __int32_t, __int64_t, __uint32_t, etc.
  - Java has int, Integer, BigInteger, etc.
  - How to unify datatypes

- Wrapper recover from segfault in C/C++/unsafe rust/...
-

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
