/-
  Type II Certificate Data Structures
  =====================================

  Defines the Type2Cert structure and Type2CertOK validity predicate
  for computational verification of sorry-region primes.
-/

import Mathlib.Tactic

namespace ED2

/-- Certificate for a sorry-region prime: (p, offset, b, c) satisfying
    offset % 4 = 3, b > 0, c > 0, (p+offset)(b+c) = 4*offset*b*c. -/
structure Type2Cert where
  p : ℕ
  offset : ℕ
  b : ℕ
  c : ℕ
deriving DecidableEq, Repr

/-- Validity predicate: all four conditions checkable in ℕ. -/
def Type2CertOK (cert : Type2Cert) : Prop :=
  cert.offset % 4 = 3 ∧
  cert.b > 0 ∧
  cert.c > 0 ∧
  (cert.p + cert.offset) * (cert.b + cert.c) = 4 * cert.offset * cert.b * cert.c

/-- Decidable instance for native_decide. -/
instance (cert : Type2Cert) : Decidable (Type2CertOK cert) := by
  unfold Type2CertOK
  infer_instance

end ED2
