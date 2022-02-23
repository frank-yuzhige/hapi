## AASTG Syntax Example
```
state start S1 = {}                              # State '[]
state S2 = S1[x -> int64 a -> int64, b -> int64] # State '["x" -> Attr Int64, ...]
state S3 = S2[x -> string]                       # State '["x" -> Attr String ...]
...
# State type = PState '[Symbol :-> Attr Type]


add : (int64, int64) -> int64
show : (int64) -> string


# Edge contains: begin, end, [end_var_assignments := expr_todo_with_begin_state]+,
S1 -> S2: x = add(a, b), a = 10, b = a + 10 expect x == 30
S2 -> S3: x = show(x) expect x == "30"

S1 -> S2: x = add(a, b), a = any, b = 42 - a expect x == 42 # Should be invalid, how to solve this? Different expectations lead to "effectively different" states. Use shadow state. S1 -> S2S: x = add(a, b), a = any, b = 42 - a; S2S -> S2: expect x = 42


+------+     +------+
|  S1  | --> |  S2  |
+------+     +------+

```
