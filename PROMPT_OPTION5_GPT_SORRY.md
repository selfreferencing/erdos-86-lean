# Prompt: Fill the Sorry for p ≡ 1 (mod 24) in Erdős-Straus Lean 4 Proof

## Task

Fill in ONE `sorry` in a Lean 4 proof of the Erdős-Straus Conjecture for primes p ≡ 1 (mod 4).

The sorry is at line 193 of `Existence.lean`. It handles the case p ≡ 1 (mod 24). The other two cases (p ≡ 5 or 17 mod 24, and p ≡ 13 mod 24) are already proven.

## What the sorry must produce

The sorry sits inside:
```lean
obtain ⟨offset, b, c, hoff, hbpos, hcpos, hTypeII⟩ :
    ∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
```

So the sorry must produce:
```
∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
  (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

**In the sorry's context, these hypotheses are available:**
- `p : ℕ`
- `hp : Nat.Prime p`
- `hp4 : p % 4 = 1`
- `hp_ge : p ≥ 5`
- `hp3_ne : p % 3 ≠ 0`
- `hp3 : ¬(p % 3 = 2)` (so p % 3 = 1)
- `hp3_1 : p % 3 = 1`
- `hp8 : ¬(p % 8 = 5)` (so p % 8 = 1, since p % 4 = 1 forces p % 8 ∈ {1, 5})

**Combined: p ≡ 1 (mod 24), p prime, p ≥ 5.**

## Mathematical Background

### The Type II Equation
We need: `(p + offset)(b + c) = 4 * offset * b * c` where offset ≡ 3 (mod 4).

### BC = A² Reformulation
Setting A = (p + offset)/4, B = offset·b - A, C = offset·c - A:
- The equation becomes B·C = A²
- B ≡ -A (mod offset), C ≡ -A (mod offset)
- A solution exists iff A² has a positive divisor d ≡ -A (mod offset)

### Why offset = 3 fails
For p ≡ 1 (mod 24), A = (p+3)/4 ≡ 1 (mod 3). When A is prime and ≡ 1 (mod 3), all divisors of A² are ≡ 1 (mod 3), but we need one ≡ 2 (mod 3).

**Counterexample: p = 73.** A = 19 (prime, ≡ 1 mod 3). Divisors of 361: {1, 19, 361}, all ≡ 1 (mod 3). No solution with offset = 3.

### Multi-offset solutions exist
Every prime p ≡ 1 (mod 24) up to 100,000 has a solution with SOME offset ≡ 3 (mod 4).

Examples of primes needing offset ≠ 3:
- p=73: offset=7, A=20, b=3, c=60
- p=193: offset=7, A=50, b=10, c=25
- p=241: offset=7, A=62, b=9, c=558
- p=313: offset=7, A=80, b=12, c=240

Offset distribution (primes up to 50,000):
- offset=3: 87%
- offset=7: 10%
- offset=11: 1.7%
- offset=15,19,23,31: rare

Max offset needed up to 100,000: 63 (for p = 87481).

### The A-window
For any offset δ ≡ 3 (mod 4), A = (p + δ)/4 must satisfy:
- A > 0 (automatic since p ≥ 5, δ ≥ 3)
- The window for A is [(p+3)/4, (3p-3)/4], giving δ ∈ [3, 2p-3]

### Sufficient condition for offset δ to work
A = (p + δ)/4 needs A² to have a divisor d ≡ -A (mod δ).

Simplest sufficient condition: δ | (A + 1), i.e., δ | (p + 4)/4 + 1... this gets complicated. The key point is that as δ varies, A varies, and we need ONE (δ, A) pair that works.

### Proven cases for reference

**Case 1 (p ≡ 2 mod 3):** offset=3, A=(p+3)/4, c₀=(p+7)/12, b=A·c₀
Key algebraic identities: p+3=4A, A+1=3c₀

**Case 2 (p ≡ 13 mod 24):** offset=3, A=(p+3)/4, c₀=(p+11)/12, b=(A/2)·c₀
Key algebraic identities: p+3=4A, A+2=3c₀, 2(A/2)=A (A even since 8|p+3)

## Lean 4 Environment

- Lean 4 version: v4.27.0-rc1
- Mathlib: recent master
- Available imports: `Mathlib.Data.Nat.Prime.Basic`, `Mathlib.Data.Int.ModEq`, `Mathlib.Tactic`
- Useful tactics: `omega`, `norm_num`, `native_decide`, `linear_combination`, `push_cast`, `exact_mod_cast`, `zify`, `positivity`

## Strategies You Might Consider

### Strategy A: Further modular cascade
Split p ≡ 1 (mod 24) into sub-cases by p mod 120 or p mod 840 and handle each. This works for most sub-cases but may not close all of them.

### Strategy B: native_decide for small primes + density for large
For p ≤ B (some bound), verify computationally using `Decidable` instances. For p > B, prove existence via a density/counting argument. Note: `native_decide` can handle quite large checks.

### Strategy C: Variable offset construction
Find an explicit formula: given p ≡ 1 (mod 24), choose offset based on factorization of p+4, p+8, etc. For example, if p+4 has a factor ≡ 3 (mod 4), use that as offset.

### Strategy D: Lattice/window argument
Use the ED2 window lemma (proven in WindowLattice.lean) which shows rectangles of size ≥ d' × d' contain lattice points. The challenge is connecting this linear lattice condition to the quadratic BC = A² equation.

### Strategy E: Combination
Use native_decide up to some bound, then a simpler argument for large primes.

## Constraints

1. The proof must handle ALL primes p ≡ 1 (mod 24) with p ≥ 5. No exceptions.
2. The proof must produce the existential witness: `∃ offset b c : ℕ, ...`
3. The proof must compile with the given imports (no additional imports beyond what's listed).
4. The `linear_combination` tactic is available and powerful for ℤ polynomial identities.
5. `native_decide` works for finite decidable checks.

## Complete File for Context

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace ED2

def A_lower (p : ℕ) : ℚ := p / 4 + 3 / 4
def A_upper (p : ℕ) : ℚ := 3 * p / 4 - 3 / 4

theorem A_window_width (p : ℕ) (hp4 : p % 4 = 1) (hp_ge : p ≥ 5) :
    A_upper p - A_lower p = (p - 3) / 2 := by
  unfold A_upper A_lower; field_simp; ring

theorem A_window_nonempty (p : ℕ) (hp4 : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ A : ℕ, A_lower p ≤ A ∧ (A : ℚ) ≤ A_upper p := by
  use (p + 3) / 4
  have h4 : 4 ∣ (p + 3) := by omega
  have hcast : (↑((p + 3) / 4) : ℚ) = (↑(p + 3) : ℚ) / 4 := Nat.cast_div_charZero h4
  constructor
  · unfold A_lower; rw [hcast]; push_cast; exact le_of_eq (by ring)
  · unfold A_upper; rw [hcast]; push_cast
    have : (p : ℚ) ≥ 5 := by exact_mod_cast hp_ge; linarith

theorem A_window_nonempty_nat (p : ℕ) (hp4 : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ A : ℕ, A > 0 ∧ p < 4 * A ∧ 4 * A ≤ 3 * p + 3 := by
  use (p + 3) / 4
  have h4 : 4 ∣ (p + 3) := by omega
  have heq : (p + 3) / 4 * 4 = p + 3 := Nat.div_mul_cancel h4
  omega

theorem offset_mod4 (p A : ℕ) (hp4 : p % 4 = 1) :
    (4 * A - p) % 4 = 3 ∨ 4 * A ≤ p := by
  by_cases h : 4 * A > p
  · left; omega
  · right; omega

theorem ed2_exists (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ offset c : ℕ, offset % 4 = 3 ∧ c > 0 ∧
    let d := (4 * c - 1) * offset - p
    d > 0 ∧ d ∣ (p + offset) * c * p := by
  obtain ⟨offset, b, c, hoff, hbpos, hcpos, hTypeII⟩ :
      ∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
        (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
    have hp3_ne : p % 3 ≠ 0 := by
      intro h
      have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      have := hp.eq_one_or_self_of_dvd 3 h3; omega
    by_cases hp3 : p % 3 = 2
    · -- CASE 1: p ≡ 2 (mod 3) [PROVEN, omitted for brevity]
      have h4 : 4 ∣ (p + 3) := by omega
      have h12 : 12 ∣ (p + 7) := by omega
      refine ⟨3, (p + 3) / 4 * ((p + 7) / 12), (p + 7) / 12, by norm_num, ?_, ?_, ?_⟩
      · exact Nat.mul_pos (by omega) (by omega)
      · omega
      · set A := (p + 3) / 4 with hA_def
        set c₀ := (p + 7) / 12 with hc₀_def
        have hA_mul : A * 4 = p + 3 := Nat.div_mul_cancel h4
        have hc₀_mul : c₀ * 12 = p + 7 := Nat.div_mul_cancel h12
        have hkey : A + 1 = 3 * c₀ := by omega
        have hA_nat : p + 3 = 4 * A := by omega
        have hkey_nat : A + 1 = 3 * c₀ := hkey
        have hA_int : (↑p : ℤ) + 3 = 4 * (↑A : ℤ) := by exact_mod_cast hA_nat
        have hkey_int : (↑A : ℤ) + 1 = 3 * (↑c₀ : ℤ) := by exact_mod_cast hkey_nat
        push_cast
        linear_combination
          (↑c₀ : ℤ) * ((↑A : ℤ) + 1) * hA_int +
          4 * (↑A : ℤ) * (↑c₀ : ℤ) * hkey_int
    · have hp3_1 : p % 3 = 1 := by omega
      by_cases hp8 : p % 8 = 5
      · -- CASE 2: p ≡ 13 (mod 24) [PROVEN, omitted for brevity]
        have h4 : 4 ∣ (p + 3) := by omega
        have h8 : 8 ∣ (p + 3) := by omega
        have h12 : 12 ∣ (p + 11) := by omega
        set A := (p + 3) / 4 with hA_def
        set A' := (p + 3) / 8 with hA'_def
        set c₀ := (p + 11) / 12 with hc₀_def
        have hA_mul : A * 4 = p + 3 := Nat.div_mul_cancel h4
        have hA'_mul : A' * 8 = p + 3 := Nat.div_mul_cancel h8
        have hc₀_mul : c₀ * 12 = p + 11 := Nat.div_mul_cancel h12
        have hA'A : 2 * A' = A := by omega
        have hkey : A + 2 = 3 * c₀ := by omega
        refine ⟨3, A' * c₀, c₀, by norm_num, ?_, ?_, ?_⟩
        · exact Nat.mul_pos (by omega) (by omega)
        · omega
        · have hA_nat : p + 3 = 4 * A := by omega
          have hkey_nat : A + 2 = 3 * c₀ := hkey
          have hA'_nat : 2 * A' = A := hA'A
          have hA_int : (↑p : ℤ) + 3 = 4 * (↑A : ℤ) := by exact_mod_cast hA_nat
          have hkey_int : (↑A : ℤ) + 2 = 3 * (↑c₀ : ℤ) := by exact_mod_cast hkey_nat
          have hA'_int : 2 * (↑A' : ℤ) = (↑A : ℤ) := by exact_mod_cast hA'_nat
          push_cast
          linear_combination
            (↑c₀ : ℤ) * ((↑A' : ℤ) + 1) * hA_int +
            4 * (↑A' : ℤ) * (↑c₀ : ℤ) * hkey_int -
            4 * (↑c₀ : ℤ) * hA'_int
      · /- CASE 3: p ≡ 1 (mod 24) — the deep case.
           No fixed offset works for all primes in this class.
           Counterexample: p = 73, offset = 3 fails (A = 19 prime, 19 ≡ 1 mod 3).
           Requires variable offset depending on factorization of A = (p + offset)/4.
           Full proof needs Dyachenko's lattice density argument
           (arXiv:2511.07465, Theorems 9.21/10.21). -/
        sorry -- YOUR PROOF GOES HERE
  have hoff_pos : 0 < offset := by omega
  refine ⟨offset, c, hoff, hcpos, ?_⟩
  have hfactor : (↑p + ↑offset : ℤ) * ↑c = ↑b * ((4 * ↑c - 1) * ↑offset - ↑p) := by
    linear_combination hTypeII
  have hd_pos_int : (4 * (↑c : ℤ) - 1) * ↑offset - ↑p > 0 := by
    have hlhs : (↑p + ↑offset : ℤ) * ↑c > 0 := by positivity
    by_contra hle; push_neg at hle
    have : ↑b * ((4 * (↑c : ℤ) - 1) * ↑offset - ↑p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  have hc_ge : 1 ≤ 4 * c := by omega
  have hd_ge : p < (4 * c - 1) * offset := by zify [hc_ge]; linarith
  have hd_pos : (4 * c - 1) * offset - p > 0 := by omega
  have hd_dvd : (4 * c - 1) * offset - p ∣ (p + offset) * c := by
    exact ⟨b, by zify [hc_ge, le_of_lt hd_ge]; linear_combination hfactor⟩
  exact ⟨hd_pos, dvd_mul_of_dvd_left hd_dvd p⟩

end ED2
```

## Output Format

Please provide the complete Lean 4 proof that replaces the `sorry` at line 193 (inside the `· /- CASE 3 ...` branch). The proof should:

1. Have the goal: `∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧ (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c`
2. Use hypotheses: `hp : Nat.Prime p`, `hp4 : p % 4 = 1`, `hp_ge : p ≥ 5`, `hp3_1 : p % 3 = 1`, and the fact that p % 8 = 1 (derivable from hp4 and ¬hp8)
3. Compile with the imports listed above
4. Handle ALL primes p ≡ 1 (mod 24), not just specific cases

Thank you!
