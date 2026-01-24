# B7 Fleet Prompts: Bradford's Conjecture 1 and Complementarity Proof

## Context Summary (From B6 Fleet)

**The precise target is now identified**: Bradford's Conjecture 1

> **For every prime p**, ∃x with ⌈p/4⌉ ≤ x ≤ ⌈p/2⌉ and d | x² such that:
> - **Type I**: d ≡ -px (mod 4x-p), OR
> - **Type II**: d ≤ x and d ≡ -x (mod 4x-p)

**What we know**:
- Type I fails ONLY for p=2521 among primes < 500,000
- Type II fails for 247 primes < 500,000 (but all have Type I solutions)
- p=2521: Type I fails completely, Type II succeeds at k=13 (m=55, x=644)
- "Both fail" = ESC counterexample (verified to 10^18: none found)
- 2521 ≡ 1 (mod 840) - Mordell's hardest residue class
- López's duality: Type A/B targets are multiplicative inverses mod (4dn-1)
- Quadratic form duality: Type I = definite, Type II = indefinite

---

## B7-Character: Character-Theoretic Analysis (GPT Pro Extended × 3)

```
**ESC Research: B7-Character - Dirichlet Characters and Type I/II Complementarity**

**Background**:
Type I F(k,m): Need divisor m | (kp+1) with m ≡ -p (mod 4k)
Type II 7B: Need coprime (a,b) | x_k with a+b ≡ 0 (mod m_k)

From B5 analysis: 7B fails for k IFF -1 ∉ ⟨q mod m_k : q | x_k⟩
Equivalently: ∃ odd Dirichlet character χ (mod m_k) with χ(q)=1 for all primes q | x_k

**The character-theoretic question**:
For primes in Mordell's 6 hard classes {1, 121, 169, 289, 361, 529} (mod 840):

1. What Legendre/Jacobi symbols distinguish Type I failures from Type I successes?
2. For Type-I-resistant primes like 2521, what character χ blocks Type I?
3. Why doesn't this same χ (or a related one) block Type II?

**Specific tasks**:

(a) For p=2521 and s=1,2,...,20, compute:
   - (p | q) Legendre symbols for small primes q | (p² + 4s)
   - The group G_s = ⟨d mod 4s : d | (p² + 4s)⟩
   - Whether -p (mod 4s) lies in G_s

(b) For the 247 Type-II-fail primes < 500,000:
   - What common character obstruction do they share?
   - How does Type I bypass this obstruction?

(c) **The key question**: Is there a character-theoretic reason why:
   - Type I failure (p misses all covering classes) ⟹
   - Type II success (factor pair with sum ≡ 0 exists)?

(d) Can you express Bradford's Conjecture 1 in character-sum language?

**Deliverable**: A character-theoretic obstruction analysis explaining why Type I and Type II have complementary failure modes.
```

---

## B7-Bradford: Explicit Translation (GPT Pro Extended × 2)

```
**ESC Research: B7-Bradford - Map (k,m) to Bradford's (x,d) Framework**

**The two formulations**:

OURS (F(k,m)):
- Constraint: m | (kp+1) AND m ≡ -p (mod 4k)
- Solution: X = (p+m)/4, Y = (p+m)(kp+1)/(4km), Z = kpY

BRADFORD (Integers 2024):
- Find x ∈ [⌈p/4⌉, ⌈p/2⌉] and d | x²
- Type I: d ≡ -px (mod 4x-p)
- Type II: d ≤ x AND d ≡ -x (mod 4x-p)

**Tasks**:

(a) **Explicit bijection**: Given (k,m) satisfying our Type I constraint, what is the corresponding (x,d)?
   - Hypothesis: x = (p+m)/4, but what is d?
   - Check: m = 4x - p, so m ≡ -p (mod 4k) becomes what in Bradford's language?

(b) **Reverse translation**: Given Bradford's (x,d) Type I, recover (k,m).
   - If d ≡ -px (mod 4x-p), what is the corresponding m and k?

(c) **For p=2521**:
   - List the (x,d) pairs that Bradford's algorithm would check
   - Verify NONE satisfy Type I condition (d ≡ -px mod m)
   - Verify k=13 (x=644, m=55) satisfies Type II condition

(d) **The unified view**:
   - Is Bradford's m = 4x - p always equal to our m_k?
   - What's the relationship between Bradford's d and our coprime pair (a,b)?

(e) **Computational test**: For gap primes {97, 113, 229, 233, 1201}:
   - Find Bradford's (x,d) Type I solutions
   - Compare to our F(k,m) solutions (F(5,3), F(1,3), etc.)

**Deliverable**: A dictionary translating between our framework and Bradford's, with worked examples.
```

---

## B7-Sieve: Effective Density Bounds (GPT Thinking Extended × 2)

```
**ESC Research: B7-Sieve - "Both Targets Missed" Has Density Zero**

**Setup**:
For prime p, modulus m = 4x - p, two targets:
- Type I target: -px (mod m)
- Type II target: -x (mod m) (with d ≤ x constraint)

Type I succeeds if SOME d | x² hits Type I target.
Type II succeeds if SOME d | x² with d ≤ x hits Type II target.

**Questions**:

(a) **Independence**: Are Type I and Type II targets hitting "independent" in the sieve sense?
   - What's the correlation between hitting one target vs the other?
   - Note: -px and -x have ratio p, so they're "far apart" in (ℤ/mℤ)×

(b) **Sieve for divisor residues**: Given n = x², what's the probability that:
   - NO d | n lands in a specific residue class r (mod m)?
   - NO d | n with d ≤ √n lands in class r?
   This depends on #divisors, their distribution, etc.

(c) **Effective bounds**: Using Bombieri-Vinogradov or Barban-Davenport-Halberstam:
   - Can we bound the number of primes p < X where both targets are missed?
   - What form does the error term take?
   - Is it O(X / (log X)^A) for any A?

(d) **The sieve viewpoint**: Think of (d | x², d hits target) as "sieving" the divisors.
   - Two sieves: Type I sieve (target -px) and Type II sieve (target -x, d small)
   - "Both fail" means both sieves come up empty
   - What sieve density arguments apply?

(e) **López's probability heuristic**:
   Expected hits ~ (1/2)(log B)² for budget B.
   Probability of NO hit ~ exp(-c(log B)²).
   Can this be made rigorous?

**Deliverable**: A sieve-theoretic framework for proving "both fail" has density 0, ideally with effective constants.
```

---

## B7-Quadratic: Indefinite Form Representations (GPT Pro Extended × 2)

```
**ESC Research: B7-Quadratic - Representations by Definite vs Indefinite Forms**

**The duality discovered in B6**:
- Type I corresponds to DEFINITE quadratic: p² + 4s = uv, norm in ℤ[√(-s)]
- Type II corresponds to INDEFINITE quadratic: 4M = u² - v² with constraints

**The transform**:
For Type II, write ab = M with a + b ≡ 0 (mod m).
Set u = a + b, v = b - a. Then 4M = u² - v² with u ≡ 0 (mod m).

**Questions**:

(a) **Representation theory**: What's known about which integers are represented by x² - y² with linear constraints on x, y?
   - Fact: n = x² - y² = (x-y)(x+y) iff n ≢ 2 (mod 4)
   - How does adding u ≡ 0 (mod m) constrain things?

(b) **Class field theory angle**:
   - Type I uses norms in imaginary quadratic fields ℤ[√(-s)]
   - Type II uses norms in real quadratic fields (difference of squares)
   - Is there a class field theory framework unifying both?

(c) **Representation densities**:
   - What fraction of n are represented by x² + 4y² with congruence constraints?
   - What fraction by x² - y² with congruence constraints?
   - Are these complementary in some sense?

(d) **Genus theory**:
   - Do Type I and Type II correspond to different genera of binary quadratic forms?
   - Could complementarity be a statement about genera covering all integers?

(e) **For p=2521**:
   - Why does p² + 4s fail to have "good" factorizations for all s ≤ 1260?
   - What indefinite form condition does the Type II solution (k=13, m=55) satisfy?
   - Can we see the failure/success in terms of form discriminants?

**Deliverable**: A quadratic-form-theoretic perspective on why Type I and Type II complement each other.
```

---

## B7-Verify: Mordell Classes Exhaustive Check (GPT Pro Extended × 2)

```
**ESC Research: B7-Verify - Computational Verification for Mordell's 6 Hard Classes**

**The 6 hardest residue classes mod 840**: {1, 121, 169, 289, 361, 529}

These are the quadratic residues mod 840 that survive all modular identity coverage.
p=2521 ≡ 1 (mod 840) is the ONLY known Type-I-resistant prime.

**Tasks**:

(a) For each class c ∈ {1, 121, 169, 289, 361, 529}:
   - List primes p ≡ c (mod 840) with p < 50,000
   - For each, determine: Type I success (at which k)? Or Type II success (at which k)?
   - Tabulate results

(b) **Type I failures**: Among primes in these 6 classes up to 100,000:
   - How many fail Type I for k ≤ 20?
   - How many fail Type I for k ≤ 100?
   - Is p=2521 truly unique, or are there others?

(c) **Class-specific patterns**: Does Type I failure correlate with specific sub-residue classes?
   - Within class 1 (mod 840), are Type-I-hard primes ≡ 1 (mod 2520)?
   - What about 2521 = 2520 + 1 with 2520 = lcm(1,...,10)?

(d) **Cross-check Bradford**: For 10 primes in each of the 6 classes:
   - Compute Bradford's (x, d) solution
   - Verify it matches our F(k,m) or 7B solution
   - Flag any discrepancies

(e) **Density estimate**: What fraction of primes in each class are "Type II primary" (Type I fails, Type II succeeds)?
   - Class 1: ?/?
   - Class 121: ?/?
   - etc.

**Deliverable**: Exhaustive verification tables for Mordell's 6 hard classes, confirming complementarity and characterizing where each method succeeds.
```

---

## B7-Unify: The Torsor and Covering Perspective (Gemini Deep Think × 2)

```
**ESC Research: B7-Unify - Universal Torsor and Covering System Perspectives**

**From Tao/Elsholtz**: ESC solutions parameterized by a universal torsor variety.
**From López**: Type A and Type B are "boundary faces" of the same parameter space.

**The geometric intuition**:
Complementarity might be GEOMETRIC: the torsor always meets at least one boundary face.

**Questions for deep exploration**:

(a) **Torsor geometry**: What is the universal torsor for the ESC variety?
   - Parameterize 4n = xyz by coordinates (a, b, c, ...)
   - What are the "boundary faces" corresponding to Type I and Type II?
   - Why must every prime hit at least one face?

(b) **Covering system analogy**:
   - Each (k, m) Type I rule covers one residue class mod 4km
   - Each (k, m_k) Type II rule covers primes where x_k has appropriate factorization
   - Is there a finite covering system combining both that covers all primes?

(c) **The M/m duality**:
   - Type I: m | (kp+1), varies over divisors of kp+1
   - Type II: m_k = 4k+3, varies over moduli from k-index
   - These are "dual" searches: one searches modulus space, one searches multiplier space

(d) **Why complementarity might be inevitable**:
   - Type I is blocked when p avoids infinitely many covering classes
   - But avoiding these classes forces p into a "highly structured" position
   - That structure might GUARANTEE Type II success
   - Can you make this precise?

(e) **Boldest conjecture**: What's the SIMPLEST statement that implies complementarity?
   - "For every prime p, either p+4 has a factor ≡ 3 (mod 4), or..."
   - Can we identify the minimal structural condition?

**Deliverable**: A conceptual framework explaining WHY complementarity should hold, ideally pointing to a proof strategy.
```

---

## Deployment Summary

| Prompt | Instances | Model | Focus |
|--------|-----------|-------|-------|
| B7-Character | 3 | GPT Pro Extended | Dirichlet character obstructions |
| B7-Bradford | 2 | GPT Pro Extended | Framework translation |
| B7-Sieve | 2 | GPT Thinking Extended | Effective density bounds |
| B7-Quadratic | 2 | GPT Pro Extended | Definite/indefinite duality |
| B7-Verify | 2 | GPT Pro Extended | Mordell class verification |
| B7-Unify | 2 | Gemini Deep Think | Geometric/covering perspective |

**Total**: 13 instances

---

## Key Data Points for Reference

**p=2521 specifics**:
- 2521 = 2520 + 1, where 2520 = lcm(1,...,10)
- 2521 ≡ 1 (mod 840) - Mordell's hardest class
- Type I: FAILS for ALL s ≤ 1260 (exhaustively verified)
- Type II: Succeeds at k=13, m=55, x=644=4×161, (a,b)=(4,161)
- 4 + 161 = 165 = 3×55 ≡ 0 (mod 55) ✓

**Bradford's formulation**:
- x ∈ [⌈p/4⌉, ⌈p/2⌉], d | x², m = 4x - p
- Type I: d ≡ -px (mod m)
- Type II: d ≤ x AND d ≡ -x (mod m)

**López's formulation**:
- Type A: p ≡ -4d (mod 4dn-1)
- Type B: p ≡ -n (mod 4dn-1)
- Duality: -4d and -n are multiplicative inverses mod (4dn-1)

**Mordell's 6 classes**: {1, 121, 169, 289, 361, 529} (mod 840)

**Type II failures to 500k**: 247 primes (all have Type I solutions)

**Type I failures to 500k**: ONLY p=2521
