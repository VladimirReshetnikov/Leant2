# Leant2 design proposals

Nine independently prepared design proposals for Leant2, followed by one
unified proposal that combines the strongest ideas from all nine.

Every proposal is a self-contained package: a LaTeX article (with its PDF),
one or more small Lean 4.34.0 prototypes that were compiled remotely through
the AXLE checking service, transcribed receipts of those checks, and Python or
Wolfram helper scripts. None of them is a complete Leant2 implementation.

## Directory map

The directories are numbered in the original alphabetical order of the
uploaded archives. Redundant wrapper directories (`Leant2/`) and download
suffixes (` (1)`) were removed; the contents of each package are unchanged.

| Dir | Original archive | Article title | Main article file |
| --- | --- | --- | --- |
| `01-lean-native-synthesis-architecture/` | `Leant2` | Leant2: a Lean-native synthesis architecture | `article/Leant2.tex` |
| `02-architecture-checked-experiments/` | `Leant2-Architecture` | Leant2: architecture, algorithms, and checked experiments | `article/leant2.tex` |
| `03-programs-and-contracts/` | `Leant2-design/Leant2` | Leant2: Lean-native synthesis of programs and their contracts | `article/Leant2.tex` |
| `04-native-dependent-synthesis/` | `Leant2_Architecture` | Leant2: Native Dependent Program Synthesis in Lean | `article/leant2.tex` |
| `05-dependent-behavioral-synthesis/` | `Leant2_Architecture (1)/Leant2` | Leant2: Native Dependent-Type and Behavioral Program Synthesis in Lean | `article/Leant2.tex` |
| `06-algorithms-checked-pilot/` | `Leant2_Architecture_Algorithms/Leant2` | Leant2: architecture, algorithms, and checked pilot | `article/leant2.tex` |
| `07-architecture-prototypes/` | `Leant2_Architecture_and_Prototypes/Leant2` | Leant2: Lean-native synthesis architecture (design proposal with checked feasibility experiments) | `article/leant2.tex` |
| `08-architecture-checked-prototypes/` | `Leant2_Architecture_and_Prototypes (1)/Leant2` | Leant2: architecture, algorithms, and checked prototypes | `Leant2_Architecture.tex` |
| `09-native-dependent-design/` | `Leant2_Design` | Leant2: Native Dependent Program Synthesis in Lean (detailed architecture and algorithm proposal) | `article/Leant2.tex` |
| `10-unified-proposal/` | (new) | Leant2: A Unified Architecture Proposal | `Leant2.tex` (sections under `sections/`) |

Each numbered directory keeps its own `README.md` with reproduction
instructions. Relative paths inside those READMEs refer to the package root,
which is now the numbered directory itself.

## The unified proposal

`10-unified-proposal/Leant2.tex` (compiled: `Leant2.pdf`) is a new article
that consolidates the nine proposals. It keeps the ideas that recur across
most proposals as the architectural core, selects the best-developed treatment
of each subsystem where the proposals differ, and records which proposal each
idea comes from so the original, more detailed discussion can be consulted
(Appendix A is the provenance ledger). It adds two owner requirements that the
nine proposals do not contain: a single adaptive engine with no engine
switches or settings, and a semantic acceptance baseline over Leant's
`:synth` golden corpus (30 transcripts, 278 queries). It also records what to
reuse from the sibling project Forge. It does not add new experimental
evidence; the evidence sections cite the receipts in the nine packages.
