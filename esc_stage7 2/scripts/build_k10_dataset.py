#!/usr/bin/env python3
"""Stage 6B: build a 10-k covering certificate table for Mordell-hard primes ≤ 10^7.

We assume we already have the Stage 3/4 dataset of *minimal* Bradford certificates
for all Mordell-hard primes p ≤ 10^7 at:
  data/hard_primes_minimal.jsonl

This script constructs a new certificate for each prime p using a fixed k from:
  K10 = {5,7,9,11,14,17,19,23,26,29}
by calling `bradford_fixed_k(p,k)` and taking the first k that works.

Outputs:
  data/hard_primes_k10_cover.jsonl
  ErdosStraus/CertificatesK10_10M.lean

The Lean file embeds (p,k,x,y,z) directly and proves, via `native_decide`, that:
- k ∈ K10
- x,y,z > 0
- ES p x y z holds.

NOTE: This environment does not include a Lean toolchain, so the Lean file is intended
to be compiled in a separate Lean+Mathlib setup.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Dict, List

import sys
sys.path.append(str(Path(__file__).resolve().parent))
from bradford_engine import bradford_fixed_k, sieve_primes_upto


KSET: List[int] = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]


def load_primes(minimal_path: Path) -> List[int]:
    primes: List[int] = []
    with minimal_path.open("r", encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            rec = json.loads(line)
            primes.append(int(rec["p"]))
    primes.sort()
    return primes


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    data_dir = root / "data"
    minimal_path = data_dir / "hard_primes_minimal.jsonl"
    out_jsonl = data_dir / "hard_primes_k10_cover.jsonl"
    out_lean = root / "ErdosStraus" / "CertificatesK10_10M.lean"

    primes = load_primes(minimal_path)
    if not primes:
        raise SystemExit("No primes loaded")

    maxp = max(primes)
    maxx = (maxp + 3) // 4 + max(KSET)
    primes_for_fact = sieve_primes_upto(int(math.isqrt(maxx)) + 1)

    certs: List[Dict] = []
    type_counts: Dict[str, int] = {}

    for p in primes:
        chosen = None
        for k in KSET:
            got = bradford_fixed_k(p, k, primes_for_fact)
            if got is not None:
                chosen = got
                break
        if chosen is None:
            raise RuntimeError(f"No k in KSET solved p={p}")

        type_counts[chosen.sol_type] = type_counts.get(chosen.sol_type, 0) + 1
        certs.append(
            {
                "p": p,
                "k": chosen.k,
                "x": chosen.x,
                "y": chosen.y,
                "z": chosen.z,
                "d": chosen.d,
                "m": chosen.m,
                "type": chosen.sol_type,
                "residue_840": chosen.residue_840,
            }
        )

    # JSONL
    with out_jsonl.open("w", encoding="utf-8") as f:
        for cert in certs:
            f.write(json.dumps(cert, separators=(",", ":")) + "\n")

    # Lean embedding
    lines: List[str] = []
    lines.append("import Mathlib")
    lines.append("import ErdosStraus.Basic")
    lines.append("")
    lines.append("namespace ErdosStraus")
    lines.append("")
    lines.append("/-- A direct certificate (p,k,x,y,z) for ES over naturals. -/")
    lines.append("structure K10Cert where")
    lines.append("  p : ℕ")
    lines.append("  k : ℕ")
    lines.append("  x : ℕ")
    lines.append("  y : ℕ")
    lines.append("  z : ℕ")
    lines.append("  deriving Repr, DecidableEq")
    lines.append("")
    lines.append("/-- The 10-k covering set used in Stage 6B. -/")
    lines.append("def K10 : Finset ℕ := {5,7,9,11,14,17,19,23,26,29}")
    lines.append("")
    lines.append("/-- Certificates for all Mordell-hard primes p ≤ 10^7 (20,513 entries). -/")
    lines.append("def certsK10 : Array K10Cert := #[")
    for cert in certs:
        lines.append(f"  ⟨{cert['p']}, {cert['k']}, {cert['x']}, {cert['y']}, {cert['z']}⟩,")
    lines.append("]")
    lines.append("")
    lines.append("/-- Certificate correctness predicate: k ∈ K10, positivity, and ES identity holds. -/")
    lines.append(
        "def CertOk (c : K10Cert) : Prop := c.k ∈ K10 ∧ c.x > 0 ∧ c.y > 0 ∧ c.z > 0 ∧ ES c.p c.x c.y c.z"
    )
    lines.append("")
    lines.append("/-- All embedded certificates satisfy `CertOk`. -/")
    lines.append(
        "theorem all_certsK10_ok : ∀ i : Fin certsK10.size, CertOk certsK10[i] := by\n  native_decide"
    )
    lines.append("")
    lines.append("end ErdosStraus")
    lines.append("")

    out_lean.write_text("\n".join(lines), encoding="utf-8")

    print(f"Wrote {len(certs)} certificates to {out_jsonl}")
    print(f"Type breakdown: {type_counts}")
    print(f"Lean file: {out_lean}")


if __name__ == "__main__":
    main()
