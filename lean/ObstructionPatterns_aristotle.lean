/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 36454779-68c4-462a-a6b0-7161145f4728

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Application type mismatch: The argument
  x.divisors
has type
  Finset ℕ
but is expected to have type
  Finset (ZMod m)
in the application
  Finset.image (fun (d : ZMod m) => d) x.divisors
don't know how to synthesize implicit argument `m`
  @ErdosStraus.hasWitness' (?m.4 x) x
context:
m : ℕ
inst✝ : NeZero m
x : ℕ
⊢ ℕ
Invalid argument name `m` for function `ErdosStraus.fails'`

Hint: Perhaps you meant one of the following parameter names:
  • `x`: m̵x̲
Invalid argument name `m` for function `ErdosStraus.fails'`

Hint: Perhaps you meant one of the following parameter names:
  • `x`: m̵x̲-/
namespace ErdosStraus

/-!
# Minimal Obstruction Patterns

## Key Lemma: Downward Closure

If `y ∣ x` and `k` fails for `x` (meaning `D_m(x) ∩ (-D_m(x)) = ∅`),
then `k` fails for `y` as well.

Reason: Every divisor of `y` is also a divisor of `x`, so `D_m(y) ⊆ D_m(x)`.
If `D_m(y)` contained a pair `{a, -a}`, then `D_m(x)` would too.

## Corollary: Minimal Patterns are Singletons

Any obstruction pattern (residue multiset of prime factors) has all
sub-multisets obstructing. Hence the only nonempty "minimal" obstruction
patterns (minimal under sub-multiset inclusion) are size-1 patterns.

For each modulus `m`, the minimal obstruction patterns are exactly the
single residue classes `a ∈ (ℤ/mℤ)*` with `a ≠ -1 (mod m)`.

(If the only prime factor residue is `-1`, then `D_m(x)` contains `1` and `-1`,
giving an immediate witness.)
-/

variable {m : ℕ} [NeZero m]

/-- The divisor residue set: residues mod m of all divisors of x. -/
def divisorResidueSet' (x : ℕ) : Finset (ZMod m) :=
  (Nat.divisors x).image (fun d => (d : ZMod m))

/-- x has a witness iff D_m(x) ∩ (-D_m(x)) ≠ ∅ -/
def hasWitness' (x : ℕ) : Prop :=
  ∃ a : ZMod m, a ∈ divisorResidueSet' x ∧ -a ∈ divisorResidueSet' x

/-- k fails for x iff x has no witness. -/
def fails' (x : ℕ) : Prop := ¬hasWitness' x

/-- Downward closure: if y ∣ x then D_m(y) ⊆ D_m(x). -/
lemma divisorResidueSet_subset_of_dvd {x y : ℕ} (hy : y ∣ x) :
    divisorResidueSet' y ⊆ divisorResidueSet' (m := m) x := by
  intro a ha
  simp only [divisorResidueSet', Finset.mem_image] at ha ⊢
  obtain ⟨d, hd_dvd, hd_eq⟩ := ha
  use d
  constructor
  · exact Nat.dvd_trans hd_dvd hy |> Nat.mem_divisors.mpr ⟨·, by
      intro hx; simp [hx] at hy; exact Nat.not_lt.mpr (Nat.zero_le _) (Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd_dvd, by simp⟩))⟩
  · exact hd_eq

/-- Key lemma: If y ∣ x and x fails, then y fails. -/
lemma fails_of_dvd_of_fails {x y : ℕ} (hy : y ∣ x) (hx : fails' (m := m) x) :
    fails' y := by
  unfold fails' hasWitness' at *
  intro ⟨a, ha_in, hna_in⟩
  apply hx
  use a
  exact ⟨divisorResidueSet_subset_of_dvd hy ha_in,
         divisorResidueSet_subset_of_dvd hy hna_in⟩

/-- For a prime power p^e with p ≡ a (mod m), the divisor residue set is
    {1, a, a², ..., a^e}. -/
lemma divisorResidueSet_prime_power (p : ℕ) (e : ℕ) (hp : Nat.Prime p) (he : 0 < e) :
    divisorResidueSet' (m := m) (p ^ e) =
      (Finset.range (e + 1)).image (fun i => (p : ZMod m) ^ i) := by
  classical
  ext a
  simp only [divisorResidueSet', Finset.mem_image, Nat.mem_divisors]
  constructor
  · intro ⟨d, ⟨hd_dvd, hne⟩, hd_eq⟩
    -- d | p^e means d = p^j for some j ≤ e
    rcases Nat.dvd_prime_pow hp hd_dvd with ⟨j, hj_le, rfl⟩
    refine ⟨j, Nat.lt_succ_of_le hj_le, ?_⟩
    simpa [Nat.cast_pow] using hd_eq
  · intro ⟨j, hj_lt, hj_eq⟩
    refine ⟨p ^ j, ⟨Nat.pow_dvd_pow p (Nat.lt_succ_iff.mp hj_lt), pow_ne_zero e hp.ne_zero⟩, ?_⟩
    simpa [Nat.cast_pow] using hj_eq

/-- If p ≡ -1 (mod m), then {1, -1} ⊆ D_m(p), so p has a witness. -/
lemma hasWitness_of_neg_one_residue (p : ℕ) (hp : Nat.Prime p) (hres : (p : ZMod m) = -1) :
    hasWitness' (m := m) p := by
  use 1
  constructor
  · -- 1 ∈ D_m(p) since 1 | p
    simp only [divisorResidueSet', Finset.mem_image]
    use 1
    exact ⟨Nat.mem_divisors.mpr ⟨one_dvd p, hp.ne_zero⟩, by simp⟩
  · -- -1 ∈ D_m(p) since p | p and p ≡ -1
    simp only [divisorResidueSet', Finset.mem_image]
    use p
    exact ⟨Nat.mem_divisors.mpr ⟨dvd_refl p, hp.ne_zero⟩, by simp [hres]⟩

/-- Minimal obstruction patterns are singletons [a] with a ≠ -1.

    A pattern [a] with a ≠ -1 gives D_m = {1, a} which has no
    {b, -b} pair (since a ≠ -1 means a ≠ -1 and 1 ≠ -a).

    NOTE: This requires additional hypotheses: m > 2 (so 1 ≠ -1) and m ∤ 2p (so p ≠ -p). -/
lemma singleton_pattern_fails_of_two_lt (p : ℕ) (hp : Nat.Prime p)
    (hm : 2 < m) (h2p : ¬ m ∣ (2 * p))
    (hres : (p : ZMod m) ≠ -1) (hres' : (p : ZMod m) ≠ 1) :
    fails' (m := m) p := by
  classical
  unfold fails' hasWitness'
  intro ⟨a, ha_in, hna_in⟩

  rcases (by
    simpa [divisorResidueSet', Finset.mem_image] using ha_in
  ) with ⟨d₁, hd₁_mem, hd₁_eq⟩

  rcases (by
    simpa [divisorResidueSet', Finset.mem_image] using hna_in
  ) with ⟨d₂, hd₂_mem, hd₂_eq⟩

  have hd₁ : d₁ = 1 ∨ d₁ = p := by
    have : d₁ ∣ p := Nat.dvd_of_mem_divisors hd₁_mem
    exact hp.eq_one_or_self_of_dvd d₁ this
  have hd₂ : d₂ = 1 ∨ d₂ = p := by
    have : d₂ ∣ p := Nat.dvd_of_mem_divisors hd₂_mem
    exact hp.eq_one_or_self_of_dvd d₂ this

  rcases hd₁ with rfl | rfl <;> rcases hd₂ with rfl | rfl
  · -- d₁ = 1, d₂ = 1
    have ha : a = (1 : ZMod m) := by simpa using hd₁_eq.symm
    have hna : -a = (1 : ZMod m) := by simpa using hd₂_eq.symm
    have h1 : (1 : ZMod m) = (-1 : ZMod m) := by
      have : (- (1 : ZMod m)) = (1 : ZMod m) := by simpa [ha] using hna
      simpa using this.symm
    have h1ne : (1 : ZMod m) ≠ (-1 : ZMod m) := by
      intro h
      have h2 : (2 : ZMod m) = 0 := by
        calc (2 : ZMod m) = (1 : ZMod m) + 1 := by norm_num
        _ = (1 : ZMod m) + (-1) := by simpa [h]
        _ = 0 := by ring
      have hm2 : m ∣ 2 := by
        simpa [ZMod.natCast_zmod_eq_zero_iff_dvd] using h2
      exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hm) hm2
    exact h1ne h1

  · -- d₁ = 1, d₂ = p  ⇒ p = -1
    have ha : a = (1 : ZMod m) := by simpa using hd₁_eq.symm
    have : (p : ZMod m) = -1 := by
      simpa [ha] using hd₂_eq
    exact hres this

  · -- d₁ = p, d₂ = 1  ⇒ p = -1
    have hna : -a = (1 : ZMod m) := by simpa using hd₂_eq.symm
    have ha : a = (p : ZMod m) := by simpa using hd₁_eq.symm
    have : (p : ZMod m) = -1 := by
      have : (- (p : ZMod m)) = (1 : ZMod m) := by simpa [ha] using hna
      simpa using congrArg Neg.neg this
    exact hres this

  · -- d₁ = p, d₂ = p  ⇒ 2p = 0
    have ha : a = (p : ZMod m) := by simpa using hd₁_eq.symm
    have hna : -a = (p : ZMod m) := by simpa using hd₂_eq.symm
    have hpneg : (p : ZMod m) = -(p : ZMod m) := by
      simpa [ha] using hna.symm

    have hmul0 : (2 : ZMod m) * (p : ZMod m) = 0 := by
      calc (2 : ZMod m) * (p : ZMod m) = (p : ZMod m) + p := by simpa [two_mul]
      _ = (p : ZMod m) + (-p) := by simpa [hpneg]
      _ = 0 := by ring

    have hcast0 : (2 * p : ZMod m) = 0 := by
      simpa [Nat.cast_mul] using hmul0

    have h2pne : (2 * p : ZMod m) ≠ 0 := by
      intro h
      have : m ∣ 2 * p := by
        simpa [ZMod.natCast_zmod_eq_zero_iff_dvd] using h
      exact h2p this

    exact h2pne hcast0

/-- The set B_k of minimal obstruction residues for modulus m.
    B_m = {a ∈ (ℤ/mℤ)* : a ≠ -1}. -/
def minimalObstructionSet (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  (Finset.univ : Finset (ZMod m)).filter (fun a => IsUnit a ∧ a ≠ -1)

/-- Size of B_m for prime m is m - 2. -/
lemma minimalObstructionSet_card_prime (p : ℕ) [Fact (Nat.Prime p)] :
    (minimalObstructionSet p).card = p - 2 := by
  classical
  have hp : Nat.Prime p := (Fact.out : Nat.Prime p)
  letI : NeZero p := ⟨hp.ne_zero⟩

  have hset :
      minimalObstructionSet p =
        ((Finset.univ : Finset (ZMod p)).erase 0).erase (-1) := by
    ext a
    -- In a field (ZMod p for prime p), IsUnit a ↔ a ≠ 0
    simp [minimalObstructionSet, isUnit_iff_ne_zero, Finset.mem_erase,
      and_left_comm, and_assoc, and_comm]

  have hcard_univ : (Finset.univ : Finset (ZMod p)).card = p := by
    calc
      (Finset.univ : Finset (ZMod p)).card = Fintype.card (ZMod p) := by
        simpa using (Finset.card_univ : (Finset.univ : Finset (ZMod p)).card = Fintype.card (ZMod p))
      _ = p := by simpa using (ZMod.card p)

  have hneg1_ne0 : (-1 : ZMod p) ≠ 0 := by
    intro h
    have : (1 : ZMod p) = 0 := by
      calc (1 : ZMod p) = (-1 : ZMod p) * (-1 : ZMod p) := by ring
      _ = (-1 : ZMod p) * 0 := by simpa [h]
      _ = 0 := by ring
    exact one_ne_zero this

  have hcard_erase0 : ((Finset.univ : Finset (ZMod p)).erase 0).card = p - 1 := by
    have hmem : (0 : ZMod p) ∈ (Finset.univ : Finset (ZMod p)) := by simp
    calc
      ((Finset.univ : Finset (ZMod p)).erase 0).card
          = (Finset.univ : Finset (ZMod p)).card - 1 := by
              simpa using (Finset.card_erase_of_mem hmem)
      _ = p - 1 := by simpa [hcard_univ]

  have hcard_erase0_neg1 :
      (((Finset.univ : Finset (ZMod p)).erase 0).erase (-1)).card = p - 2 := by
    have hmem : (-1 : ZMod p) ∈ ((Finset.univ : Finset (ZMod p)).erase 0) := by
      simp [Finset.mem_erase, hneg1_ne0]
    calc
      (((Finset.univ : Finset (ZMod p)).erase 0).erase (-1)).card
          = ((Finset.univ : Finset (ZMod p)).erase 0).card - 1 := by
              simpa using (Finset.card_erase_of_mem hmem)
      _ = (p - 1) - 1 := by simpa [hcard_erase0]
      _ = p - 2 := by simp [Nat.sub_sub]

  simpa [hset] using hcard_erase0_neg1

end ErdosStraus