# Leant2: design for further improvements

`Leant2-next.tex` (compiled: `Leant2-next.pdf`, 36 pages) is the design
document for the work after the first implementation. It starts from
measurements of the engine at commit `33cec8b`, not from the earlier
proposals.

- **Part I, where the engine stands.** What passes (the six harnesses), what
  does not (thirteen stretch cases that Leant never solved either, and a
  sixteen-query probe just outside the corpus with seven failures), where the
  time goes, and a precise statement of what the search is. Then the
  constraints that stay and a table of all work items in three classes:
  engineering, adaptation, research.
- **Part II, work with known solutions.** Eight engineering items
  (compilable results, frontends, receipts and resumption, substrate cost,
  parallel lanes, a propositional decision procedure, a wider proof
  portfolio, benchmarks beyond Leant) and five adaptation items
  (conditionals and guard abduction, recursion on `Nat`, normal forms,
  parametricity-directed test inputs, rule indexing), each with its defect,
  design and closing test.
- **Part III, open problems.** Nine problems where we know of no optimal or
  clearly adequate algorithm: search control with coupled goals under a
  wall-clock budget; carriers, accumulators and auxiliary state; evaluation
  of programs with holes; indexed families and the motive problem; general
  recursion from incomplete examples; contracts beyond decidable
  observations; component retrieval at library scale; ranking and candidate
  equivalence; learned guidance under a kernel gate. Each section gives the
  problem, why it is hard here, what is known, the design to try first, how
  progress would be measured, and the questions for outside experts.
- **Part IV, plan.** Dependencies, seven phases with gates, risks, and a
  consolidated table of where outside expertise would help: the question,
  whom to ask, and what we would bring.

Literature is cited from memory of the published record; check titles,
venues and years before relying on them in print.

Build: `pdflatex Leant2-next.tex` three times (MiKTeX or TeX Live). The
preamble is shared in style with `10-unified-proposal/` and copied into
`preamble.tex`.
