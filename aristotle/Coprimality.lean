import Mathlib

/-!
# Coprimality and Complementary Divisor Lemmas

Two lemmas needed for the ED2 Dyachenko bridge:

1. `coprime_A_delta`: gcd(A, 4A-p) = 1 when 0 < A < p and p is prime.
   Route: gcd(A, 4A-p) = gcd(A, p) (since 4A ≡ 0 mod A), and gcd(A, p) = 1
   since p is prime and A < p implies p ∤ A.

2. `complementary_divisor_cong`: If d*e = A*A, δ ∣ (d+A), and gcd(A,δ) = 1,
   then δ ∣ (e+A).
   Route: From d ≡ -A (mod δ) and d*e = A², get -A*e ≡ A² (mod δ),
   so A*(e+A) ≡ 0 (mod δ). Coprimality gives δ ∣ (e+A).
-/

theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) :
    Nat.Coprime A (4 * A - p) := by
  sorry

theorem complementary_divisor_cong (A d e δ : ℕ)
    (hde : d * e = A * A)
    (hmod : δ ∣ (d + A))
    (hcop : Nat.Coprime A δ) :
    δ ∣ (e + A) := by
  sorry
