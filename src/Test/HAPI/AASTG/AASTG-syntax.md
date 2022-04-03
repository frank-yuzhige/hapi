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
