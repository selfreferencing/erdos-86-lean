"""Generate a small Lean file of `example` checks from JSONL Bradford certificates.

Usage:
  python3 scripts/gen_examples.py \
    --input ../esc_stage3/data/hard_primes_certificates.jsonl \
    --output ../esc_stage5/ErdosStraus/Examples.lean \
    --n 20

The generated Lean file uses `native_decide` to prove the numeric `EscEq` goal.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


HEADER = """import ErdosStraus.Basic
import Mathlib.Tactic

namespace ErdosStraus

-- Auto-generated examples from JSONL certificates.

"""

FOOTER = """
end ErdosStraus
"""


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--n", type=int, default=20)
    args = ap.parse_args()

    rows = []
    with args.input.open("r", encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            rows.append(json.loads(line))
            if len(rows) >= args.n:
                break

    out = [HEADER]
    for r in rows:
        p = int(r["p"])
        x = int(r["x"])
        y = int(r["y"])
        z = int(r["z"])
        out.append(f"example : Conjecture {p} := by\n")
        out.append(f"  refine ⟨{x}, {y}, {z}, by decide, by decide, by decide, ?_⟩\n")
        out.append("  -- purely numeric check\n")
        out.append("  native_decide\n\n")

    out.append(FOOTER)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(out), encoding="utf-8")


if __name__ == "__main__":
    main()
