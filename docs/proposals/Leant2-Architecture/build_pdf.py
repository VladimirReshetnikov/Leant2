#!/usr/bin/env python3
"""Build article/leant2.pdf with three XeLaTeX passes; no external Python packages."""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    engine = shutil.which('xelatex')
    if engine is None:
        print('XeLaTeX is not on PATH. Install it and the packages/fonts listed in README.md.',
              file=sys.stderr)
        return 2
    article = Path(__file__).resolve().parent / 'article'
    for number in range(1, 4):
        print(f'XeLaTeX pass {number}/3...', flush=True)
        try:
            completed = subprocess.run(
                [engine, '-interaction=nonstopmode', '-halt-on-error', 'leant2.tex'],
                cwd=article, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                encoding='utf-8', errors='replace', timeout=180, check=False)
        except (OSError, subprocess.TimeoutExpired) as exc:
            print(f'Build failed: {exc}', file=sys.stderr)
            return 2
        if completed.returncode:
            print(completed.stdout, file=sys.stderr)
            print(f'XeLaTeX failed. See {article / "leant2.log"}.', file=sys.stderr)
            return completed.returncode
    result = article / 'leant2.pdf'
    if not result.is_file():
        print('XeLaTeX returned success without an output PDF.', file=sys.stderr)
        return 2
    print(f'Built {result}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
