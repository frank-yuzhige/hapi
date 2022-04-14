## AASTG Syntax Example
```
state start S1 = {}                               # State '[]
state S2 = S1[x -> int64, a -> int64, b -> int64] # State '["x" -> Attr Int64, ...]
state S3 = S2[x -> string]                        # State '["x" -> Attr String ...]
...

# AASTG type = AASTG '['[Symbol :-> Type]] '[]
# State type = '[Symbol :-> Attr Type]


add : (int64, int64) -> int64
show : (int64) -> string


# Edge contains: begin, end, [end_var_assignments := expr_todo_with_begin_state]+,
S1 -> S2: update x = add(a, b), a = 10, b = a + 10 expect x == 30
S2 -> S3: update x = show(x) expect x == "30"

S1 -> S2: x = add(a, b), a = any, b = 42 - a expect x == 42 # Should be invalid, how to solve this? Different expectations lead to "effectively different" states. Use shadow state. S1 -> S2S: x = add(a, b), a = any, b = 42 - a; S2S -> S2: expect x = 42


+------+     +------+
|  S1  | --> |  S2  |
+------+     +------+

```
### Edge
1. Var: `S1 -> S2: update i32 a = 10, char b = 'c', drop i64 c`
2. Assert: `S2 -> S3: expect a = 10`
3. ApiCall: `S2 -> S4: api(a, b) -> x`

### State
"name-to-value" mapping

Type of a state `S1{c : i64}`, `S2{a : i32, b : char}`

### API Declaration
`add1: (i32) -> i32`
`show: (i32) -> String`

### Example AASTG
```
add(i32, i32) -> i32
show(i32) -> String

S -> S1: update i32 a, i32 b
S1 -> S2: update string x
S2 -> S3: add1(b) -> a
S3 -> S4: expect a == 1
S4 -> S5: show(a) -> x
S5 -> S6: update x -> r
S6 -> S7: expect x == "1"

```

# Why we need to merge
Because we want to explore new paths
- New path: A path is said to be new if it is not in the original graph(s), and it does not violate dependencies.

## How to merge
Based on subnode relations
- Upper-sub node: n1 <_upper n2 iff inPath(n1) reduce-subsetof inPath(n2)
- Lower-sub node: n1 <_lower n2 iff outPath(n1) reduce-subsetof outPath(n2)

If n1 <_upper n2, we can merge n1 to n2, keeping both outPaths.
If n1 <_lower n2, we can merge n1 to n2, keeping both inPaths.
So we explore more paths.


## Reduce-subsetof


## How to check subnode relation

## Path-and-Dep
- PathDep of path p, PD(p) = dependencies at each node after traversing this path.
- PathApiDep of path p PDa(p) = RELEVANT dependencies at each node after traversing this path before each api call.
- alpha-effect-equivalence: p1 =α p2 iff they both start from the start node, and there's some substitution of variables such that their end node's dependencies are the same.

Paths that are alpha-effect-equivalent can interchange with each other. (No! f(a) -> g(a) problem)

- NEW alpha-effect-equivalence: p1 =α p2 iff they both start from the start node, and there's some substitution of variables such that their end node's dependencies [AND relevant dependencies before each api call] are the same.

Paths that are NEW alpha-effect-equivalent can interchange with each other.



## Dependency

- Attribute: normal attributes, indirect (Get)
- Dependency: Attribute, result of api call

