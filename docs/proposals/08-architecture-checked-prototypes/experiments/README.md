# Experiment notes

## Final source identities

The three `lean/*.lean` files correspond to the final successful submissions.
The source-echo comparisons made in the remote calls trimmed only boundary
whitespace. The files are not reformatted copies of a different implementation.

## Initial failures retained as summaries

1. The first finite enumerator used natural-number recursion under a
   `List.range.flatMap` callback. Lean could not prove the callback index bound
   needed for termination. The final file instead uses structurally decreasing
   fuel in `exactSizeAux`. All dependent theorems were rechecked afterward.
2. The first certified-recursion declaration directly used `List.rec`, which
   caused a code-generator error even though its logical axiom inventory was
   empty. Structural equations fixed that executable path. The same attempt
   referenced `IsEmpty` under imports where it was unavailable; direct functions
   into `False` replaced those propositions in the final file.

The initial failed sources are not separately packaged; the failure summaries
state the actual errors and repairs. Only final source files are advertised as
passing. These experiments were interactive and are not randomized benchmarks.

## Trust and status

Remote results are not independent kernel replays. Axioms are explicitly
reported. The code implements small experiments, while the architecture proposes
many additional mechanisms. In particular, function-valued carrier discovery,
full proof-aware pruning, and the production acceptance service are not claimed
as implemented by these files.
