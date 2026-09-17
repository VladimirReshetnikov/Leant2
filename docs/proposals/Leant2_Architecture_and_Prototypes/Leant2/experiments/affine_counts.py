#!/usr/bin/env python3
"""Independent count mirror of Behavior.lean; this is NOT a proof checker."""
from __future__ import annotations

from dataclasses import dataclass, asdict
import json

@dataclass(frozen=True)
class Affine:
    slope: int
    offset: int

    def evaluate(self, n: int) -> int:
        if n < 0:
            raise ValueError("The experiment uses natural-number inputs.")
        return self.slope * n + self.offset


def observed(candidate: Affine, observation: str) -> bool:
    if observation == "base":
        return candidate.evaluate(0) == 1
    if observation == "step0":
        return candidate.evaluate(1) == candidate.evaluate(0) + 2
    raise ValueError(f"Unknown observation: {observation}")


def main() -> None:
    grammar = [Affine(a, b) for a in range(5) for b in range(5)]
    # The equivalence between this equality check and the universal specification
    # is proved in Behavior.lean, not by this Python function.
    canonical = Affine(2, 1)
    bank: list[str] = []
    considered = certifier_calls = pruned = 0
    winner: Affine | None = None
    for candidate in grammar:
        considered += 1
        if not all(observed(candidate, observation) for observation in bank):
            pruned += 1
            continue
        certifier_calls += 1
        if candidate == canonical:
            winner = candidate
            break
        counterexample = next((o for o in ("base", "step0")
                               if not observed(candidate, o)), None)
        if counterexample is None:
            raise AssertionError("Unexpected inconclusive affine candidate")
        bank.append(counterexample)
    baseline_calls = next(i for i, c in enumerate(grammar, start=1) if c == canonical)
    assert winner == canonical
    assert (considered, certifier_calls, pruned, baseline_calls) == (12, 3, 9, 12)
    result = {
        "status": "independent enumeration-count mirror, not Lean certification",
        "grammar_size": len(grammar), "winner": asdict(winner),
        "considered": considered, "certifier_calls": certifier_calls,
        "pruned": pruned, "inconclusive": 0,
        "unfiltered_baseline_certifier_calls": baseline_calls, "bank": bank,
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
