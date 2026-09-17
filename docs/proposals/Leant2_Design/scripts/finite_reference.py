#!/usr/bin/env python3
"""Independent finite-grammar check for the Lean CEGIS experiment.

This is not a Lean checker. It verifies the enumeration sizes and proposal trace
using Python's Boolean semantics, and writes a small reproducibility report.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator


@dataclass(frozen=True)
class Expr:
    op: str
    left: Expr | None = None
    right: Expr | None = None

    def evaluate(self, x: bool, y: bool) -> bool:
        if self.op == "x":
            return x
        if self.op == "y":
            return y
        if self.left is None:
            raise ValueError(f"Missing child for {self.op}")
        a = self.left.evaluate(x, y)
        if self.op == "not":
            return not a
        if self.right is None:
            raise ValueError(f"Missing right child for {self.op}")
        b = self.right.evaluate(x, y)
        if self.op == "and":
            return a and b
        if self.op == "or":
            return a or b
        raise ValueError(f"Unknown operator {self.op}")

    def display(self) -> str:
        if self.op in ("x", "y"):
            return self.op
        assert self.left is not None
        if self.op == "not":
            return f"!({self.left.display()})"
        assert self.right is not None
        symbol = "&&" if self.op == "and" else "||"
        return f"({self.left.display()} {symbol} {self.right.display()})"


def enumerate_layers(bound: int) -> list[list[Expr]]:
    if not 1 <= bound <= 10:
        raise ValueError("Use a bound from 1 through 10 for this small reference.")
    table: list[list[Expr]] = [[]]
    for size in range(1, bound + 1):
        layer = [Expr("x"), Expr("y")] if size == 1 else []
        if size > 1:
            layer.extend(Expr("not", e) for e in table[size - 1])
            for left in range(1, size - 1):
                right = size - 1 - left
                for a in table[left]:
                    for b in table[right]:
                        layer.extend((Expr("and", a, b), Expr("or", a, b)))
        table.append(layer)
    return table


def run() -> dict:
    table = enumerate_layers(8)
    counts = list(map(len, table))
    assert counts == [0, 2, 2, 10, 26, 114, 402, 1722, 6890]
    for size in range(2, 9):
        assert counts[size] == counts[size - 1] + 2 * sum(
            counts[k] * counts[size - 1 - k] for k in range(1, size - 1)
        )
    inputs = [(False, False), (False, True), (True, False), (True, True)]
    expected = lambda p: p[0] != p[1]
    candidates = [e for layer in table for e in layer]
    samples: list[tuple[bool, bool]] = []
    proposals: list[dict] = []
    winner: Expr | None = None
    for _ in range(5):
        e = next(e for e in candidates if all(e.evaluate(*p) == expected(p) for p in samples))
        cex = next((p for p in inputs if e.evaluate(*p) != expected(p)), None)
        proposals.append({"expression": e.display(), "counterexample": cex})
        if cex is None:
            winner = e
            break
        assert cex not in samples
        samples.append(cex)
    assert winner is not None and len(proposals) == 5 and len(samples) == 4
    first_full_solution_size = next(
        size for size, layer in enumerate(table)
        if any(all(e.evaluate(*p) == expected(p) for p in inputs) for e in layer)
    )
    assert first_full_solution_size == 8
    # Irreversible sample-equivalence pruning loses a valid candidate.
    x, y = Expr("x"), Expr("y")
    assert x.evaluate(False, False) == y.evaluate(False, False)
    assert x.evaluate(True, False) != y.evaluate(True, False)
    assert not any(e.evaluate(True, False) is False for e in [x])
    assert y.evaluate(True, False) is False
    return {
        "kind": "independent Python computation, not a Lean proof",
        "layer_counts_including_zero": counts,
        "total_candidates": len(candidates),
        "proposals": proposals,
        "counterexamples": samples,
        "result": winner.display(),
        "truth_table": [winner.evaluate(*p) for p in inputs],
        "first_full_solution_size": first_full_solution_size,
        "observational_pruning_counterexample_checked": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run()
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
