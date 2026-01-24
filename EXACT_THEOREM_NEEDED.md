# The Exact Theorem Needed

## Context

Via Gemini's quadratic reciprocity insight, we have reduced `ten_k_cover_exists` to:

## Main Theorem to Prove

**Theorem (Covering Property)**: For every prime p ≥ 5, define:
```
n = (p + 23) / 4
S = {n, n+2, n+4, n+6, n+9, n+12, n+14, n+18, n+21, n+24}
```

Then at least one element of S has an odd prime factor q with `(p/q) = -1`.

## Equivalent Formulations

### Formulation A (Contrapositive)
If p is a prime with `(p/q) = 1` for every odd prime q that divides any element of S, then p is not a prime (contradiction).

### Formulation B (Set-theoretic)
Let B(p) = {q prime : (p/q) = -1}. Then:
```
∪_{s ∈ S} {prime factors of s} ∩ B(p) ≠ ∅
```

### Formulation C (Divisibility)
For every prime p ≥ 5, there exist:
- An integer s ∈ S
- An odd prime q dividing s
such that p is a quadratic non-residue mod q.

## What We Know

1. **Computational verification**: True for all Mordell-hard primes up to 50,000
2. **Density argument**: The x_k values have ~12-16 distinct odd prime factors; roughly half have (p/q) = -1
3. **Minimum witness count**: Always ≥ 3 "bad" factors in tested cases

## Possible Proof Approaches

### Approach 1: Sieve Theory
Use a covering sieve to show that S contains elements divisible by primes from any set of positive lower density.

**Key lemma needed**: For any set P of primes with lower density δ > 0, the set S = {n, n+2, ..., n+24} has at least one element divisible by some p ∈ P, for sufficiently large n.

### Approach 2: Structure of Pseudo-Squares
A number that is a QR mod all small primes is called a "pseudo-square." Show that:
- If p is a prime and (p/q) = 1 for all q dividing any s ∈ S, then p must actually be a square
- But primes > 4 are not squares

### Approach 3: Chebotarev + Large Sieve
The Chebotarev density theorem says primes with (p/q) = -1 have density 1/2.
Combined with a large sieve inequality, show that S must contain a factor from this set.

### Approach 4: Finite Verification + Asymptotic
1. Verify computationally for all primes p ≤ N (done for N = 50,000)
2. For p > N, the x_k values are large enough that they must have "bad" factors

The asymptotic part could use: if n > N₀, then the product ∏_{s∈S} s has at least k distinct prime factors, and by equidistribution, at least k/2 - o(1) are "bad."

## The Lean Formalization

Once the theorem is proved mathematically, the Lean proof would be:

```lean
theorem covering_property (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    ∃ k ∈ K10, ∃ q : ℕ, Nat.Prime q ∧ q ∣ xK p k ∧ legendreSymbol p q = -1 := by
  sorry

theorem ten_k_cover_exists (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    ∃ k ∈ K10, kSufficient k p := by
  -- Use covering_property to get k, q with (p/q) = -1
  -- By Gemini's reciprocity: (q/m_k) = (p/q) = -1
  -- So q breaks the QR obstruction for k
  -- Therefore QRSufficient k p holds
  sorry
```

## Call to Action

**PROVE THE COVERING PROPERTY THEOREM.**

This is the final step to complete the Erdős-Straus formalization for Mordell-hard primes.
