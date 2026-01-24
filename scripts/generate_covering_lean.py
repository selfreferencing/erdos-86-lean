#!/usr/bin/env python3
"""Generate ErdosStraus/CoveringData.lean from a JSONL certificate file.

Usage:
  python3 scripts/generate_covering_lean.py \
    --jsonl data/kset_certificates_10M.jsonl \
    --out   ErdosStraus/CoveringData.lean
"""

import argparse
import json
import os
from typing import Dict, List


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jsonl", required=True, help="Input JSONL with certificates.")
    ap.add_argument("--out", required=True, help="Output Lean file path.")
    args = ap.parse_args()

    certs: List[Dict] = []
    with open(args.jsonl, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            certs.append(json.loads(line))

    header = """import ErdosStraus.Basic

namespace ErdosStraus

/-- Certificate record for a Mordell-hard prime `p` (bounded dataset). -/
structure Cert where
  p : ℕ
  residue_840 : ℕ
  k : ℕ
  m : ℕ
  typ : Bool
  x : ℕ
  y : ℕ
  z : ℕ
  d : ℕ
deriving DecidableEq, Repr

/-- The list of dataset certificates. -/
def certs : List Cert :=
[
"""

    footer = """]

end ErdosStraus
"""

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as out:
        out.write(header)
        for c in certs:
            typ_bool = "true" if c.get("type") == "II" else "false"
            out.write(
                f"  {{ p := {c['p']}, residue_840 := {c['residue_840']}, k := {c['k']}, m := {c['m']}, typ := {typ_bool}, x := {c['x']}, y := {c['y']}, z := {c['z']}, d := {c['d']} }},\n"
            )
        out.write(footer)


if __name__ == "__main__":
    main()
