import Mathlib

import ErdosStraus.Covering
import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

/-!
# Stage 8 key lemma: no simultaneous QR obstruction for all ten k

The Stage 8 strategy reduces the global cover lemma `ten_k_cover_complete` to ruling out
the possibility that *every* `k ∈ K10` is obstructed by the QR subgroup mechanism.

For a fixed `k`, the obstruction is the conjunction:

* `PrimeFactorQR (mOfK k) (xOfK p k)` : every prime factor of `x_k` is a quadratic residue
  modulo `m_k = 4k+3`;
* `TargetNQR (mOfK k) (xOfK p k)` : the target `(-x_k mod m_k)` is a quadratic non-residue.

The empirical data (all Mordell-hard primes `p ≤ 10^7`) shows that for every such prime,
at least one `k ∈ K10` avoids this obstruction.

To turn that into an *unbounded* theorem, one needs a number-theoretic argument showing that
the tenfold obstruction cannot hold for any Mordell-hard prime.

This file isolates exactly that missing statement.
-/

namespace ErdosStraus

open scoped BigOperators

/-- The ten k-values used in the Stage 6B/7 cover. -/
def K10List : List ℕ := [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

/-- The tenfold QR obstruction predicate for a given prime `p`. -/
def TenfoldObstruction (p : ℕ) : Prop :=
  (PrimeFactorQR (mOfK 5) (xOfK p 5) ∧ TargetNQR (mOfK 5) (xOfK p 5)) ∧
  (PrimeFactorQR (mOfK 7) (xOfK p 7) ∧ TargetNQR (mOfK 7) (xOfK p 7)) ∧
  (PrimeFactorQR (mOfK 9) (xOfK p 9) ∧ TargetNQR (mOfK 9) (xOfK p 9)) ∧
  (PrimeFactorQR (mOfK 11) (xOfK p 11) ∧ TargetNQR (mOfK 11) (xOfK p 11)) ∧
  (PrimeFactorQR (mOfK 14) (xOfK p 14) ∧ TargetNQR (mOfK 14) (xOfK p 14)) ∧
  (PrimeFactorQR (mOfK 17) (xOfK p 17) ∧ TargetNQR (mOfK 17) (xOfK p 17)) ∧
  (PrimeFactorQR (mOfK 19) (xOfK p 19) ∧ TargetNQR (mOfK 19) (xOfK p 19)) ∧
  (PrimeFactorQR (mOfK 23) (xOfK p 23) ∧ TargetNQR (mOfK 23) (xOfK p 23)) ∧
  (PrimeFactorQR (mOfK 26) (xOfK p 26) ∧ TargetNQR (mOfK 26) (xOfK p 26)) ∧
  (PrimeFactorQR (mOfK 29) (xOfK p 29) ∧ TargetNQR (mOfK 29) (xOfK p 29))

/-!
## Key Discovery: k=9 alone breaks the tenfold obstruction

For k=9, m = 39 = 3 × 13.

**Theorem**: For ALL Mordell-hard primes p, the k=9 obstruction is FALSE.

**Proof**:
1. All Mordell-hard residues mod 840 are ≡ 1 (mod 8)
   - {1, 121, 169, 289, 361, 529} all satisfy r % 8 = 1
2. For k=9, x = (p + 39) / 4
   - Since p ≡ 1 (mod 8), write p = 8j + 1
   - Then x = (8j + 40) / 4 = 2j + 10, which is ALWAYS EVEN
3. 2 is NQR mod 39 (since 2 is NQR mod 3, and 39 = 3 × 13)
4. Therefore x has prime factor 2, which is NQR mod 39
5. Therefore ¬ PrimeFactorQR 39 x
6. Therefore the k=9 obstruction (PrimeFactorQR ∧ TargetNQR) is FALSE

Since TenfoldObstruction is a 10-way conjunction that includes the k=9 obstruction,
and that component is always false, TenfoldObstruction is always false!
-/

/-- All Mordell-hard residues mod 840 are ≡ 1 (mod 8). -/
lemma mordell_hard_mod_8 (p : ℕ) (hMH : MordellHard840 p) : p % 8 = 1 := by
  unfold MordellHard840 at hMH
  rcases hMH with h | h | h | h | h | h <;> omega

/-- For Mordell-hard primes, x = (p + 39) / 4 is always even. -/
lemma x_even_for_mordell_hard (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    2 ∣ xOfK p 9 := by
  have h8 := mordell_hard_mod_8 p hMH
  unfold xOfK mOfK
  have hdiv4 : 4 ∣ (p + 39) := by omega
  have hdiv8 : 8 ∣ (p + 39) := by omega
  -- Since 8 | (p + 39), write p + 39 = 8k, then (p + 39) / 4 = 2k is even
  obtain ⟨k, hk⟩ := hdiv8
  have h : (p + 39) / 4 = 2 * k := by
    rw [hk]
    -- 8 * k / 4 = 2 * k
    have : 8 * k / 4 = 2 * k := by omega
    exact this
  rw [h]
  exact Nat.dvd_mul_right 2 _

/-- 2 is NQR mod 39 (since 2 is NQR mod 3, and 39 = 3 × 13). -/
lemma two_nqr_mod_39 : ¬ IsQR 39 2 := by
  unfold IsQR
  -- Check that (2 : ZMod 39) is not a square by native_decide
  -- This is decidable since ZMod 39 is finite
  decide

/-- The k=9 obstruction is always FALSE for Mordell-hard primes.

This is because x is always even, and 2 is NQR mod 39.
-/
lemma k9_obstruction_false (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    ¬ (PrimeFactorQR (mOfK 9) (xOfK p 9) ∧ TargetNQR (mOfK 9) (xOfK p 9)) := by
  intro ⟨hpfqr, _⟩
  -- hpfqr : PrimeFactorQR 39 (xOfK p 9)
  -- means: ∀ q, Prime q → q ∣ x → IsQR 39 q
  have heven := x_even_for_mordell_hard p hp hMH
  -- 2 divides x, 2 is prime, so by hpfqr, 2 should be QR mod 39
  have h2_qr : IsQR (mOfK 9) 2 := hpfqr 2 Nat.prime_two heven
  -- But 2 is NQR mod 39!
  have h2_nqr : ¬ IsQR 39 2 := two_nqr_mod_39
  -- mOfK 9 = 39
  have hm9 : mOfK 9 = 39 := by unfold mOfK; norm_num
  rw [hm9] at h2_qr
  exact h2_nqr h2_qr

/-- **Stage 8 target lemma**: no Mordell-hard prime satisfies the tenfold QR obstruction.

**PROVED** using the k=9 discovery: the k=9 component of the tenfold conjunction
is ALWAYS FALSE for Mordell-hard primes (because x is always even and 2 is NQR mod 39).

Since TenfoldObstruction is a conjunction, if any component is false, the whole thing is false.
-/
theorem no_tenfold_obstruction
    (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    ¬ TenfoldObstruction p := by
  intro hten
  -- TenfoldObstruction is: ob5 ∧ ob7 ∧ ob9 ∧ ob11 ∧ ...
  -- Extract the k=9 obstruction (third component)
  have hob9 : PrimeFactorQR (mOfK 9) (xOfK p 9) ∧ TargetNQR (mOfK 9) (xOfK p 9) := by
    exact hten.2.2.1
  -- But we proved the k=9 obstruction is always false!
  exact k9_obstruction_false p hp hMH hob9

end ErdosStraus
