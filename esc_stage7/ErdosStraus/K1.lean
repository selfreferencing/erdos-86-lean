import Mathlib
import ErdosStraus.K0

namespace ErdosStraus

/-- The next Bradford candidate `x` (k=1). -/
def x1 (p : ℕ) : ℕ := x0 p + 1

/-- The k=1 modulus `m = 7`. -/
def m1 : ℕ := 7

/-- `k=1` works if there exists a divisor `d ∣ x1^2` with the Type II congruence mod 7. -/
def k1Works (p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (x1 p)^2 ∧ d ≤ x1 p ∧ Nat.ModEq 7 (d + x1 p) 0

/-- Convenience: the canonical `(-a) mod m` representative in `ℕ`. -/
def negMod (m a : ℕ) : ℕ := (m - (a % m)) % m

/-- Quadratic residues modulo 7 among units: {1,2,4}. -/
def QR7 (a : ℕ) : Prop := a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 4

/-- Quadratic nonresidues modulo 7 among units: {3,5,6}. -/
def NQR7 (a : ℕ) : Prop := a % 7 = 3 ∨ a % 7 = 5 ∨ a % 7 = 6

/-- A "prime factor is QR mod 7" predicate used in the obstruction statement. -/
def PrimeFactorQR7 (n : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ n → QR7 q

/--
**Stage 5 Theorem (k=1 characterization / QR subgroup obstruction).**

For Mordell-hard primes, the k=1 congruence search fails exactly when:

1. Every prime factor of `x1(p)` is a quadratic residue mod 7 (i.e. congruent to 1,2,4 mod 7), and
2. `-x1(p)` is a quadratic nonresidue mod 7.

In Stage 4 terms, this is the "QR obstruction" mechanism for `m=7`.
-/
theorem k1Fails_iff_QR_obstruction
    {p : ℕ} (hp : Nat.Prime p) (hMH : MordellHard p) :
    (¬ k1Works p) ↔ (PrimeFactorQR7 (x1 p) ∧ NQR7 (negMod 7 (x1 p))) := by
  -- Sketch:
  --
  -- (→) If k=1 fails, then no divisor of x1^2 hits the residue class -x1 mod 7.
  --     In particular, if x1 had a prime factor q which is a *nonresidue*, one can use {q,2q,4q}
  --     (available because x1 is even for Mordell-hard primes) to hit any nonresidue class, including -x1.
  --     Hence all prime factors must be residues. Also the target residue must be a nonresidue.
  --
  -- (←) If all prime factors are residues, then every divisor of x1^2 is a residue class (closure of QR subgroup).
  --     Therefore no divisor can be congruent to a nonresidue such as -x1.
  --
  -- A clean Mathlib proof can be written in `ZMod 7`, identifying residues via `IsSquare`.
  -- This file leaves the detailed closure lemma and the small finite-group calculation
  -- (that `{1,2,4}` is exactly the subgroup of squares in `(ZMod 7)ˣ`) to Stage 6.
  sorry

end ErdosStraus
