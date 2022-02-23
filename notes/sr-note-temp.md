# Spec: composition of properties
Are there research for a more "abstract" spec that generates properties when "evaluated"?

A^2DG

- Api1 --some_call_sequence-> Api2 --some_call_seq-> Api3
- State1 --some_api_call-> State2 --some_api_call-> State3

Which to pick?

First approach, follows A^2 DG directly (How to represent state in the first place?)

Second approach, easier to reason about states

Argument Value-set inference (Given by user) (e.g. do {  x <- callAPI1 42, callAPI2 x } )

Question: how to merge monads? Use Arrow


High level design:
    (State: []) ---(call, arg_pred, ret_expect)--> (State: [ref(ret-type) -> ret-type])
