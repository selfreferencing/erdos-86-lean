# GPT Prompt 8: Prove Case 3 for Large Primes (p >= 1,000,001)

## Task

Prove a Lean 4 theorem that for every prime p with p % 24 = 1 and p >= 1,000,001, there exist natural numbers A and d such that:

```lean
theorem case3_large_primes (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (hp24 : p % 24 = 1) (hp_large : p ≥ 1000001) :
    ∃ A d : ℕ,
      (p + 3) / 4 ≤ A ∧
      A ≤ (3 * p - 3) / 4 ∧
      0 < d ∧
      d ∣ A ^ 2 ∧
      (4 * A - p) ∣ (d + A)
```

This is the LAST sorry in the Erdos-Straus formalization. Small primes (p < 1,000,001) are already handled by a `native_decide` certificate.

## What Claude Opus tried and why it failed

Claude Opus spent the equivalent of 6+ hours exploring approaches. Here is a detailed account of every approach tried and the specific mathematical obstruction encountered.

### Approach 1: d = 1 at various offsets

**Idea:** d = 1 always divides A^2. Need delta | (1 + A), i.e., (4A - p) | (A + 1). Set A = lo + k where lo = (p+3)/4, giving delta = 3 + 4k. Need (3 + 4k) | (lo + k + 1). Since lo = (p+3)/4, this means (3+4k) | ((p+7)/4 + k). Simplifying: (3+4k) | (p + 4k + 7)/4 ... which reduces to (3+4k) | (p+4) after algebra.

So d=1 works at offset k iff (3+4k) | (p+4). This means some odd divisor of (p+4) that is congruent to 3 (mod 4) must exist.

**Obstruction:** p+4 can be 2 times a prime congruent to 1 (mod 4). For example, if p+4 = 2q where q is prime and q % 4 = 1, then the only odd divisors of p+4 are {1, q}, both congruent to 1 (mod 4). No delta works.

**Coverage:** ~46% of primes p === 1 (mod 24).

### Approach 2: Multi-d covering system {1, 2, 3, 4, 6, 9}

**Idea:** For each offset k, try d in {1, 2, 3, 4, 6, 9, ...}. Each d works if d | A^2 AND delta | (d + A). The d | A^2 condition depends on A's factorization. For A even (k odd since lo is odd for p === 1 mod 24), d=2 works if delta | (A+2).

**Detailed analysis for k=3 (delta = 15, A = lo+3):**
- A is even (since lo is odd for p === 1 mod 24, lo+3 is even)
- Need d | A^2 with d === -A (mod 15)
- Since A is even, d=2 works if -A === 2 (mod 15), i.e., A === 13 (mod 15), i.e., A === 3 (mod 5). Only covers A === 3 (mod 5).
- For A === 0 (mod 5): need d === 0 (mod 5) and d | A^2. d=5 works iff 5|A. But 5|A iff A === 0 (mod 5) (already assumed), AND gcd(A, delta)=1 so 5 cannot divide delta=15. Contradiction: gcd(A, 15) must be 1, but 5|A means gcd(A,15) >= 5.

  Wait - actually gcd(A, delta) = gcd(A, 4A-p) = gcd(A, p) = 1 (since p is prime and A < p). So gcd(A, 15) is constrained by A mod 3 and A mod 5. Since gcd(A, delta)=1 and delta=15, we need gcd(A, 15)=1, which means A !== 0 (mod 3) AND A !== 0 (mod 5). So A mod 15 is in {1, 2, 4, 7, 8, 11, 13, 14}.

  For each value, -A mod 15 gives the target residue. The available divisors of A^2 that we can guarantee (A is even): {1, 2, 4, ...}. The residues mod 15 of {1, 2, 4} are {1, 2, 4}. This only covers A mod 15 in {14, 13, 11} (corresponding to -A mod 15 in {1, 2, 4}).

For the remaining residues (A mod 15 in {1, 7, 8}), we need larger divisors of A^2 with specific residues mod 15, which depends on A's prime factorization.

**Obstruction:** Cannot guarantee A^2 has a divisor in a prescribed residue class mod delta without knowing A's factorization.

**Coverage:** ~96.4% when combining d in {1,2,3,4,6,9} across k=0..15, but the remaining 3.6% cannot be covered without factorization-dependent arguments.

### Approach 3: q=A trick (d = A * (delta - 1))

**Idea:** If (delta-1) | A, then d = A*(delta-1) divides A^2 (since d = A*(delta-1) and A divides A^2). Also d + A = A*delta, so delta | (d+A) automatically.

Need (delta-1) | A, i.e., (2+4k) | A where delta = 3+4k. At k=0: need 2 | A. At k=1: need 6 | A. Etc.

For k=0: need 2 | lo. lo = (p+3)/4. For p === 1 (mod 24), lo is odd. So 2 does NOT divide lo.
For k=1: need 6 | (lo+1). This holds sometimes.

**Obstruction:** No universal k where (2+4k) | (lo+k).

### Approach 4: Fermat two-squares

**Idea:** p = a^2 + b^2 with a > b > 0 (from Mathlib). Set A = a*b. Then A^2 has divisors including {a^2, b^2, ab, a^2*b, ab^2, ...}. Delta = 4ab - a^2 - b^2 = 4ab - p. Need some divisor d with delta | (d + ab).

**Analysis:** d = a^2 gives d + A = a^2 + ab = a(a+b). Need delta | a(a+b). Since gcd(A, delta) = 1 and gcd(a, b) divides gcd(A, delta), this means gcd(a, delta) divides 1... no, gcd(ab, delta)=1 so gcd(a, delta)=1 and gcd(b, delta)=1. So need delta | (a+b).

delta | (a+b) iff (4ab - a^2 - b^2) | (a+b). Since (a+b)^2 = a^2 + 2ab + b^2 = 4ab - delta + 2ab = 6ab - delta, we get (a+b)^2 + delta = 6ab. If delta | (a+b) then delta | (a+b)^2, so delta | 6ab. Since gcd(ab, delta)=1, delta | 6. Since delta >= 3 and delta is odd, delta = 3. So this approach only works when 4ab - p = 3, i.e., p = 4ab - 3 for a specific Fermat decomposition.

**Also:** A = ab must be in the window [(p+3)/4, (3p-3)/4]. Since p = a^2+b^2 and A = ab: need a^2+b^2 < 4ab, i.e., (a-b)^2 < 2ab, i.e., a/b < 1+sqrt(2). So a/b must be in approximately [1, 2.414]. For a/b > 2.414, A falls below the window.

**Obstruction:** A=ab falls outside the window for many Fermat decompositions (about 16% of primes). And even when in-window, delta | (a+b) rarely holds.

### Approach 5: Multiples of primorial

**Idea:** Choose A as a multiple of 6 (or 30, or 210) within the window. Then A^2 has many divisors, increasing the chance of hitting the right residue class.

For A = 6m: A^2 = 36m^2 has divisors including {1,2,3,4,6,9,12,18,36} times divisors of m^2. With delta = 4A-p, we need a divisor of A^2 in residue class -A (mod delta). The number of guaranteed small divisors is at most tau(36) = 9. But delta can be as large as 4*6-3 = 21 (at the bottom of the window) or much larger. For delta > 9, having only 9 guaranteed residues is insufficient.

For A = 30m: tau(900) = 27 divisors. Delta at this offset is 4*30*k + ... which grows, but having 27 residues out of delta possible residues is not enough when delta > 27.

**Obstruction:** The ratio tau(primorial(k)^2) / delta_at_offset is always < 1 for large enough offsets. The divisor count grows polynomially in the primorial, but delta grows linearly with the offset, and the primorial-offset grows faster.

### Approach 6: Multiplicative structure of divisor residues

**Idea:** Divisors of A^2 mod delta form a multiplicative subgroup of (Z/delta*Z). If this subgroup is large enough to contain -A mod delta, we win.

**Analysis:** The subgroup generated by {p_i^2 mod delta : p_i | A} has order depending on the multiplicative structure of (Z/deltaZ)*. For delta prime q, the subgroup of squares in (Z/qZ)* has index 2. So if -A is a quadratic non-residue mod delta, no divisor of A^2 can be congruent to -A (mod delta) -- since all such divisors are products of squares of A's prime factors, hence always quadratic residues.

**Key insight:** For any fixed A, the set {d mod delta : d | A^2} is contained in the subgroup of quadratic residues mod delta (when delta is prime). The target -A mod delta can be a QNR, in which case NO divisor of A^2 works.

**Obstruction:** This is the fundamental mathematical reason why no single A universally works. You MUST search across multiple A values, and the proof that SOME A works requires understanding which deltas make -A a QR. This is precisely Dyachenko's lattice density argument.

## What IS proven and available in Lean

All of the following compile and are ready to import:

### WindowLattice.lean (269 lines, ALL proven)
```lean
-- Kernel lattice: L = {(u,v) : g | u*b' + v*c'}
def ED2KernelLattice (g : ℕ) (b' c' : ℤ) : AddSubgroup (ℤ × ℤ)

-- Window lemma: any g x g rectangle contains a lattice point
-- (when gcd(g, |b'|) = 1 and gcd(g, |c'|) = 1)
theorem ed2_window_lemma {g : ℕ} (hg : 0 < g) {b' c' : ℤ}
    (_hb : Nat.Coprime g (Int.natAbs b')) (hc : Nat.Coprime g (Int.natAbs c')) :
    ∀ {x0 y0 : ℤ} {H W : ℕ}, g ≤ H → g ≤ W →
      ∃ p : ℤ × ℤ, p ∈ ED2KernelLattice g b' c' ∧ p ∈ rect x0 y0 H W

-- The lattice has index g in Z^2
theorem kernel_lattice_index (g : ℕ) (hg : 0 < g) (b' c' : ℤ)
    (hb : Nat.Coprime g (Int.natAbs b')) :
    (ED2KernelLattice g b' c').index = g
```

### ExistsGoodDivisor.lean (proven lemmas)
```lean
-- gcd(A, 4A-p) = 1 for A in window
theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) (hA_win : p < 4 * A) :
    Nat.Coprime A (4 * A - p)

-- Complementary divisor also satisfies the congruence
theorem complementary_divisor_cong (A d e δ : ℕ)
    (hde : d * e = A * A) (hmod : δ ∣ (d + A)) (hcop : Nat.Coprime A δ) :
    δ ∣ (e + A)
```

### Phase3.lean (proven lemmas)
```lean
-- Converts factorization data into ED2 Type II solution
theorem ed2_of_good_divisor (p δ : ℕ) (hδ_pos : 0 < δ)
    (A : ℤ) (hA : (↑p : ℤ) + ↑δ = 4 * A)
    (d e : ℤ) (hd_pos : 0 < d) (he_pos : 0 < e)
    (hde : d * e = A ^ 2)
    (b_val c_val : ℤ)
    (hb_def : (↑δ : ℤ) * b_val = d + A)
    (hc_def : (↑δ : ℤ) * c_val = e + A) :
    ∃ b c : ℕ, b > 0 ∧ c > 0 ∧
      (↑p + ↑δ : ℤ) * (↑b + ↑c) = 4 * ↑δ * ↑b * ↑c

-- Dyachenko bridge: (α, d', b', c') -> factorization data
theorem ed2_dyachenko_bridge (p : ℕ) (hp4 : p % 4 = 1)
    (α d' b' c' : ℕ) (hα : 0 < α) (hd' : 0 < d') (hb' : 0 < b') (hc' : 0 < c')
    (hbound : p < 4 * α * b' * c') (hsum : b' + c' = (4 * α * b' * c' - p) * d') :
    ∃ (δ : ℕ) (A d e b_val c_val : ℤ), ... -- full factorization data
```

### ThueLemma.lean
```lean
-- Thue's lemma: small solution to linear congruence
theorem thue_lemma {p : ℕ} (hp : Nat.Prime p) {r : ZMod p} (hr : r ≠ 0) :
    ∃ x y : ℤ, 0 < x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ (2 * (p - 1) : ℤ) ∧
      (p : ℤ) ∣ (y - (r.val : ℤ) * x)
```

### Mathlib (SumTwoSquares)
```lean
-- Fermat's two squares theorem
theorem Nat.Prime.sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p
```

### CertificateGoodDivisor.lean (just created)
```lean
-- Computational verification for all primes p === 1 (mod 24) below 1,000,001
-- Uses native_decide with search over k=0..23 offsets and 161 AP steps
theorem exists_good_A_and_divisor_below_certBound
    {p : ℕ} (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (hp24 : p % 24 = 1) (hlt : p < certBound) :
    ∃ A d : ℕ, (p + 3) / 4 ≤ A ∧ A ≤ (3 * p - 3) / 4 ∧
      0 < d ∧ d ∣ A ^ 2 ∧ (4 * A - p) ∣ (d + A)
```

## The mathematical question

**For every prime p >= 1,000,001 with p === 1 (mod 24), prove there exist A, d in N with:**
1. (p+3)/4 <= A <= (3p-3)/4
2. d > 0
3. d | A^2
4. (4A - p) | (d + A)

Equivalently (setting delta = 4A - p): among the ~ p/2 values of A in the window, at least one A has the property that A^2 has a divisor congruent to -A modulo delta.

## Why the lattice density argument is the right approach

The fundamental obstruction to all direct approaches is:

> For any FIXED A, the set of divisors of A^2 modulo delta = 4A - p is contained in the subgroup of quadratic residues mod delta. The target residue -A mod delta can be a quadratic non-residue, making no divisor work.

But as A varies across the window (width ~ p/2), delta varies, and the target -A mod delta changes. Dyachenko's argument shows that the UNION of feasible (A, delta, target) triples across all A in the window must contain a valid pair.

The paper's Theorem 9.21 proves this via:
1. Fix alpha = 1 and parametrize the solutions as A = b'*c', d, such that the ED2 identity b'+c' = (4b'c' - p)*d' holds
2. The kernel lattice L = {(u,v) : g | u*b' + v*c'} has index g
3. The window lemma (PROVEN) guarantees a lattice point in any g x g box
4. Lemma D.33: for a lattice point (u,v), the discriminant (b'+c')^2 - 4b'c' is automatically a perfect square (it equals (b'-c')^2 = v^2)

The key gap is: **connecting the window lemma's lattice point to the existence of valid A, d in the (A, d) format**.

## Specific sub-question for GPT

Here is the precise mathematical bridge that needs to be formalized:

**Given:** p is prime, p === 1 (mod 4), p >= 1,000,001.

**The Dyachenko setup (Theorem 9.21 / Appendix D):**
- Set alpha = 1
- For b', c' > 0 with A := b'*c' in window [(p+3)/4, (3p-3)/4]:
  - Set m = 4*b'*c' - p (= 4A - p = delta)
  - The ED2 identity is: b' + c' = m * d' for some d' >= 1
  - Equivalently: m | (b' + c')
  - The kernel lattice L = {(u,v) in Z^2 : m | (u*b' + v*c')} has index m
  - Setting b' = (u+v)/2, c' = (u-v)/2 gives a bijection to lattice points with u === v (mod 2)

**What D.33 says:** If (u,v) is a lattice point with u*b' + v*c' === 0 (mod m), and we reconstruct b' = (u+v)/2, c' = (u-v)/2, then b'*c' = (u^2 - v^2)/4 = A, so A is determined by (u,v). The discriminant S^2 - 4M where S = b'+c' = u and M = b'*c' = (u^2-v^2)/4 is v^2, automatically a perfect square.

**The gap:** We need to show that for some choice of initial b', c' > 0 (with gcd(m, b') = gcd(m, c') = 1), the window lemma produces a lattice point (u, v) such that:
- u > v > 0 (so b' > 0 and c' > 0)
- b'*c' = (u^2 - v^2)/4 is in the window
- m = 4*b'*c' - p > 0

But there's a circularity: b', c' are both the input to the lattice (defining the congruence) AND the output (reconstructed from the lattice point). The paper resolves this by working in a different coordinate system.

**Alternative formulation (bypassing the circularity):**

Perhaps a cleaner approach: prove the theorem directly in the (A, d) format by showing that for p >= 1,000,001, among the ~ p/2 values of A in the window, at least one has A^2 possessing a divisor in the right residue class.

**A concrete sufficient condition:** If A has k distinct prime factors, then A^2 has at least 2^k divisors. The divisors of A^2 modulo delta cover at least 2^k / phi(delta) fraction of residues (by a combinatorial argument). We need to hit one specific residue out of delta possible. So it suffices to have tau(A^2) >= delta, i.e., the number of divisors exceeds delta.

For A = lo + k (k-th offset), delta = 3 + 4k. If we choose A to be a multiple of the k-th primorial, then tau(A^2) >= 3^(number of prime factors). For k = 5 (so delta = 23), choosing A divisible by 2*3*5*7*11*13 = 30030 gives tau(A^2) >= 3^6 = 729 >> 23. Such A exists in the window since 30030 << p/2 for p >= 1,000,001.

**But:** the issue is that tau(A^2) > delta doesn't guarantee hitting -A mod delta because divisors aren't uniformly distributed mod delta. The divisors of A^2 generate a multiplicative subgroup of (Z/deltaZ)*, and this subgroup might not contain -A. The subgroup has order at most tau(A^2), but it could be a proper subgroup that misses the target.

**However:** if delta has many small prime factors, the multiplicative group (Z/deltaZ)* is a product of cyclic groups, and squares generate a subgroup of index at most 2^(omega(delta)) where omega(delta) is the number of distinct prime factors. Since A is divisible by the same small primes, the squares of A's factors generate the full square subgroup, which has index 2^omega(delta). So we need -A to be a quadratic residue mod each prime factor of delta.

For delta = 3 + 4k: when k=0, delta=3; when k=1, delta=7; when k=2, delta=11; etc. These are often prime. When delta is prime q, -A is a QR mod q iff (-A)^((q-1)/2) === 1 (mod q). Since A is determined by p and k, this is a condition on p mod q.

**The real question:** Is there a proof that for p >= 1,000,001, SOME k in {0, 1, ..., 23} has the property that either delta_k = 3+4k is composite (making QR easier to satisfy) or -A_k is a QR mod delta_k?

## Two possible proof strategies for GPT

### Strategy A: Pigeonhole on quadratic residues

For k = 0, ..., 5, the deltas are 3, 7, 11, 15, 19, 23. For each odd prime q dividing some delta, -A mod q being a QR is a condition on p mod q (since A = (p+3)/4 + k). The fraction of primes p for which ALL of these fail simultaneously is bounded by the product of the "bad" fractions, which shrinks exponentially.

More precisely: for delta = 3, -A is a QR mod 3 iff A !== 0 (mod 3), which already excludes nothing (coprimality). Actually for delta = 3: -A === 2 (mod 3) is needed (target), and QR mod 3 = {0, 1}. So -A = 2 is a QNR mod 3. This fails for A === 1 (mod 3).

So for k=0: fails iff A === 1 (mod 3), i.e., p === 1 (mod 3), which is TRUE for p === 1 (mod 24).

For k=1, delta=7: -A mod 7. QR mod 7 = {0, 1, 2, 4}. Need -(lo+1) to be in {0,1,2,4} mod 7. This is a condition on p mod 28.

The key: show that for p === 1 (mod 24) and p >= 1,000,001, the conditions "k=0 fails AND k=1 fails AND ... AND k=23 fails" is impossible by a covering/CRT argument.

This is a finite case split on p modulo lcm(24, 28, 44, 60, 76, 92, ...) = lcm(24, 7, 11, 15, 19, 23, ...). The lcm grows fast, but the "bad set" shrinks faster.

### Strategy B: Use Chebotarev/Dirichlet density (non-constructive)

Show that the density of primes for which all k in {0,...,23} fail is 0, and that for p >= 1,000,001, no such prime exists (verified computationally for p < 1,000,001).

This is essentially the Dyachenko paper's strategy but restated: the density argument shows failures are asymptotically rare, and the certificate handles all concrete cases.

**The gap:** We have the certificate for p < 1,000,001, but need a theoretical argument for p >= 1,000,001. The theoretical argument must either:
(a) Be a pure CRT/covering argument showing the "all-fail" set modulo some modulus is empty, or
(b) Use Dyachenko's lattice/density machinery.

### Strategy C: Direct construction using Fermat + offset selection

For p = a^2 + b^2 with a > b > 0:
- The window [(p+3)/4, (3p-3)/4] has width ~ p/2
- The multiples of ab in this window are spaced ab apart
- For p >= 1,000,001, there are ~ p/(2ab) multiples of ab in the window
- Among these multiples, consider A = t*ab for various t
  - A^2 = t^2 * a^2 * b^2
  - delta = 4*t*ab - a^2 - b^2 = 4tab - p
  - d = t*a^2 gives d | A^2 and d + A = ta^2 + tab = ta(a+b)
  - Need delta | ta(a+b)
  - Since gcd(A, delta) = 1 and A = tab, gcd(tab, delta)=1
  - So need delta | (a+b) (since gcd(ta, delta) | gcd(tab, delta) = 1... wait, a | A = tab, so gcd(a, delta) | gcd(A, delta) = 1. Similarly gcd(t, delta) = 1. So gcd(ta, delta) = 1.)
  - delta | (a+b): delta = 4tab - p = 4tab - a^2 - b^2. And (a+b)^2 = p + 2ab. So for t >= 2: delta = 4tab - p >= 8ab - p = 8ab - a^2 - b^2 > (a+b)^2 for a,b large enough. So delta > a+b, making delta | (a+b) impossible for t >= 2.
  - For t = 1: delta = 4ab - p and delta | (a+b) iff delta <= a+b iff 4ab - p <= a + b iff p >= 4ab - a - b. Since p = a^2+b^2, need a^2+b^2 >= 4ab - a - b, i.e., (a-b)^2 >= 2ab - a - b. For a = b+1: 1 >= 2b(b+1) - (2b+1) = 2b^2 + 2b - 2b - 1 = 2b^2 - 1. So b <= 1. Only works for tiny cases.

**Obstruction:** This approach only works for specific small Fermat decompositions.

## What I recommend GPT focus on

The most promising direction is **Strategy A: CRT/covering on quadratic residues**.

The concrete question: for k = 0, 1, ..., 23, let delta_k = 3 + 4k and A_k = (p+3)/4 + k. For each k, the condition "d | A_k^2 with d === -A_k (mod delta_k)" fails iff -A_k is NOT representable as a product of squares of prime factors of A_k modulo delta_k. A sufficient (but not necessary) condition for failure is: -A_k is a quadratic non-residue modulo some prime factor of delta_k.

For p === 1 (mod 24) and each k:
- k=0: delta = 3. Fails iff A === 1 (mod 3), i.e., -A === 2 (mod 3) is QNR.
- k=1: delta = 7. Fails iff -A_1 is QNR mod 7.
- k=2: delta = 11. Fails iff -A_2 is QNR mod 11.
- k=3: delta = 15 = 3*5. More complex (CRT).
- k=4: delta = 19. Fails iff -A_4 is QNR mod 19.
- k=5: delta = 23. Fails iff -A_5 is QNR mod 23.
- etc.

Each condition constrains p to a subset of residues modulo lcm(24, delta_k's prime factors). The "all fail" set is the intersection of these subsets. If this intersection is EMPTY (modulo some manageable modulus), the theorem is proved by a finite case split.

**Computational evidence:** the `native_decide` certificate confirms no prime p < 1,000,001 fails with k in {0,...,23}. This strongly suggests the "all fail" set is empty modulo a manageable modulus.

**Deliverable requested:** A Lean 4 proof (or proof sketch with specific lemmas identified) that proves `case3_large_primes` above. If a pure QR/CRT argument works, it could be a finite (but large) case split on p modulo some modulus M, where each case is discharged by exhibiting a specific (k, d) that works.

Alternatively: if the lattice density approach from the paper can be formalized cleanly, that would also work. The key infrastructure (window lemma, lattice index, coprimality) is already proven.

## Lean 4 / Mathlib notes

Same as in the existing GPT prompt file (`GPT_PROMPT_exists_good_A_and_divisor.md`). Key points:
- Lean 4 (leanprover--lean4---v4.27.0-rc1) with current Mathlib
- `import Mathlib.Tactic` provides omega, linarith, nlinarith, ring, norm_cast, etc.
- `import Mathlib.NumberTheory.SumTwoSquares` for Fermat two-squares
- `import ErdosStraus.ED2.WindowLattice` for lattice infrastructure
- Use `haveI : Fact (Nat.Prime p) := ⟨hp⟩` to bridge Nat.Prime and Fact
- omega handles linear arithmetic over N and Z
- nlinarith handles nonlinear arithmetic with explicit witness hints
- ZMod and Int.ModEq for modular arithmetic

## File to edit

`ErdosStraus/ED2/ExistsGoodDivisor.lean`, replacing the sorry at approximately line 206:

```lean
      · -- Large primes: p ≥ 1,000,001 with p ≡ 1 (mod 24)
        -- This requires Dyachenko's lattice density argument.
        sorry
```

The proof may use helper lemmas defined earlier in the file or in a new file.
