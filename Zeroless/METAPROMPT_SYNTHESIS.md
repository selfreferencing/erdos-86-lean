# Metaprompt Synthesis: The 86 Conjecture
## Findings from 46 AI responses: 16 metaprompt + 10 A-series + 8 B-series + 6 C-series + 11 computational experiments
### January 27, 2026

---

## 1. The Problem

**The Erdos Zeroless Powers Problem**: Prove that the set E = {n in N : 2^n has no digit 0 in base 10} is finite.

**The 86 Conjecture** (stronger): 2^86 is the largest such power. Computationally verified for n = 87..10,000.

**Current formalization status**: Proved in Lean 4 conditional on one axiom (`no_zeroless_k_ge_91`), which is equivalent to the open problem itself.

---

## 2. The Unified Obstruction

All 14 killed proof directions and all 8 metaprompt responses converge on a single diagnosis. The six named barriers are NOT independent. They decompose into two orthogonal axes of a single mountain range:

### Axis A: No Compression (Target-Side)

The zeroless digit-cylinder set has effective complexity exponential in k. No method can reduce it to a small number of algebraic, analytic, or automaton conditions.

| Barrier | What It Means |
|---------|---------------|
| **4.5^k barrier** | Survivor counts grow (not shrink) under digit-by-digit lifting; branching factor 5 * (9/10) = 4.5 > 1 |
| **Clopen encoding impossibility** | The zeroless set is a union of ~4.5^k clopen balls in Z_5; no bounded-degree p-adic analytic function can encode it |
| **High-entropy / variable-count wall** | The digit condition has k degrees of freedom (k grows with n), blocking all Diophantine tools built for O(1) variables |
| **Wiener norm catastrophe** | The L1 Fourier norm of the zeroless indicator is ~(9/2)^{k/2}, exponentially larger than the target probability (9/10)^k |

### Axis B: No Averaging (Orbit-Side)

The orbit 2^n is a rank-1 deterministic sequence in a zero-entropy dynamical system, sampled at logarithmic time scale. No method can manufacture enough mixing/cancellation to overcome exponentially small targets.

| Barrier | What It Means |
|---------|---------------|
| **Log-time regime** | At digit level k, orbit length N ~ k while modulus ~ 5^k; so N ~ log(modulus), exponentially below where exponential sum methods work |
| **Zero-entropy wall** | The coupled system (irrational rotation + periodic 5-adic orbit) is Kronecker: rank-1, zero entropy, no mixing |
| **Permanent Fourier obstruction** | Max normalized Fourier coefficient of the zeroless set is ~1/9, not decaying with k |

### The One-Sentence Diagnosis

**A high-complexity shrinking target (digit cylinders) confronting a low-entropy deterministic orbit in a log-time sampling regime -- so neither compression nor averaging can be made exponentially effective.**

---

## 3. The 14 Killed Directions Compressed

The 14 directions collapse to 6 paradigms, then to 2 super-paradigms:

### 6 Paradigms

| Paradigm | Killed Directions | Core Mechanism | Death By |
|----------|------------------|----------------|----------|
| **P1: Local digit/carry dynamics** | 1, 8, 9 | Build constraints digit-by-digit, prune survivors | 4.5^k barrier (supercritical branching) |
| **P2: Decoupling/projection** | 2, 3, 4 | Analyze mod 2^k and mod 5^k separately | CRT invisibility (density 1.0 in each factor) |
| **P3: Pseudorandomness from averaging** | 10, 11, 13 | Convert small density into zero hits via cancellation | Log-time + Wiener + permanent Fourier obstruction |
| **P4: Ergodic rigidity** | 12 | Use entropy/joinings to force randomness | Zero entropy / Kronecker system |
| **P5: Diophantine compression** | 5, 6, 7 | Rewrite as bounded-complexity Diophantine equation | High entropy / too many variables |
| **P6: p-adic analytic** | 14 | Encode forbidden set as zeros of analytic function | Clopen encoding impossibility |

### 2 Super-Paradigms

1. **"Average your way out"** (P3, P4): The target is tiny; show the orbit behaves randomly enough to miss it. Dies because no mixing resource exists at the needed scale.

2. **"Compress your way out"** (P1, P5, P6): The constraint is structured; reduce to finitely many checkable conditions. Dies because the digit condition has exponential complexity.

P2 is a precondition failure (the constraint is invisible to the natural factorization).

---

## 4. "Outside" Paradigms Examined

Six paradigms from outside the killed list were examined. All reduce to needing either compression or mixing:

| Paradigm | Verdict | Reduces To |
|----------|---------|------------|
| **Algebraic geometry / cohomology** | Dead unless uniform-complexity encoding found | P3 (exponential sums) or P6 (encoding) |
| **Topology / homotopy / K-theory** | No foothold; any translation goes through automata | P1 (digit dynamics) |
| **Category / topos / model theory** | Could diagnose hardness, won't prove finiteness directly | Restates the problem |
| **Probability (LLL, entropy)** | Requires proving independence/mixing first | P3/P4 (the same core gap) |
| **Information theory / Kolmogorov** | Proving incompressibility is as hard as normality | Same gap as normality |
| **Statistical mechanics / transfer matrices** | The 4.5 eigenvalue IS the partition function | P1, unless a new multiscale invariant is found |

---

## 5. The Problem's Neighborhood

The problem lives in a "missing corner" of the mathematical landscape:

| Regime | Example | Why Solvable | Our Problem |
|--------|---------|-------------|-------------|
| **Low entropy + thin orbit** | Repunit, Catalan, perfect powers | Constraint collapses to O(1) algebraic conditions | Constraint has 9^k possibilities (high entropy) |
| **High entropy + massive averaging** | Maynard (primes with restricted digits) | ~X^{log9/log10} candidates to sieve over | Only ~3 candidates per digit length |
| **High entropy + thin orbit** | **Erdos zeroless powers** | ??? | **This is us** |

**Closest solved neighbor**: Maynard's primes with restricted digits (similarity 7/10).
**Bridge tool needed**: Log-time cancellation for the orbit 2^n mod 5^k.

**Three clean reductions to named problems**:

1. **Log-time exponential sum cancellation**: Prove nontrivial cancellation for sum_{n <= ck} e(h * 2^n / 5^k). This is the cleanest single-statement reduction.

2. **Fractal intersection / shrinking targets**: Prove a dimension-drop theorem for multiplicative orbits intersecting digit Cantor sets (Lagarias-style).

3. **Skolem membership for regular sets**: Develop a decision/finiteness theory for linear recurrences intersecting regular-language (automatic) sets at growing precision.

---

## 6. The Minimal New Tool

The weakest theorem that would suffice (two equivalent formulations):

### Formulation A: Digit-Cylinder Discrepancy

Let S_k be the set of zeroless residues mod 10^k. There exist constants C > 0, epsilon > 0, and k_0 such that for every k >= k_0:

    |#{1 <= n <= Ck : 2^n mod 10^k in S_k} - Ck * |S_k| / 10^k| <= 10^{-epsilon * k}

Since |S_k|/10^k = (9/10)^k, the main term Ck * (9/10)^k < 1 for large k, and the error 10^{-epsilon*k} < 1, so the integer count must be 0.

### Formulation B: Log-Time Cancellation

There exist c > 0, eta > 0, and k_0 such that for all k >= k_0 and all h with 5 does not divide h:

    |sum_{n=0}^{floor(ck)} exp(2*pi*i * h * 2^n / 5^k)| <= ck * 5^{-eta*k}

This is the exponential-sum version: nontrivial cancellation for sums of length ~k with modulus 5^k.

**Both are strictly weaker than normality** but exactly strong enough to convert the heuristic (expected ~0.0025 zeroless powers beyond 91 digits) into a proof of zero hits.

---

## 7. Alive Directions (Ranked)

Three candidate approaches survive the kill analysis, each appearing independently across multiple responses:

### Direction 1: Automata / Logic Rigidity

**Idea**: Prove the set E = {n : 2^n is zeroless} is definable in a tame class (automatic, Presburger, semilinear), then apply rigidity theorems (Cobham-type) to conclude eventual periodicity, reducing to finite verification.

**Specific formulation**: An "exponential Cobham" theorem -- if S is a base-b regular set and a >= 2 is not a power of b, then {n : a^n in S} is finite or eventually periodic. Applied with a=2, b=10, S = zeroless integers.

**Key obstacle**: Current automata/Presburger rigidity breaks when you introduce irrational Beatty maps (k = floor(alpha * n) with alpha = log_10(2)). Need new theory connecting finite-automata predicates with irrational-slope sampling.

**Why it's alive**: Entirely bypasses the analytic gap. Does not use Fourier, averaging, or compression. Inherently pointwise. The digit constraint IS a regular language. Both M2-A responses rank this highest.

**Convergence**: 4/4 responses that discuss it rank it as top or co-top.

---

### Direction 2: Non-Abelian Spectral Gap + Transference

**Idea**: Embed the problem into the affine group Aff(Z/5^kZ) = (Z/5^kZ) semidirect (Z/5^kZ)*, which is the minimal non-abelian object coupling additive (digit) and multiplicative (orbit) structure. Establish uniform spectral gap for Cayley graphs, achieving mixing in O(k) time. Then use transference to convert ~3 deterministic samples into averaged bias that spectral gap contradicts.

**Three-step argument**:
1. Replace pure multiplication by affine action (sees both digits and orbit)
2. Prove uniform expansion over prime power tower (mixing in O(k) steps)
3. Transference: deterministic hits --> approximate invariance --> contradiction via spectral gap against W_k of measure (9/10)^k

**Key obstacles**: (i) Proving uniform expansion over prime power towers for generators interacting with digit cylinders; (ii) Building a transference lemma from ~3 deterministic samples to approximate invariance.

**Why it's alive**: Leaves the Kronecker/rank-1/zero-entropy world that killed all ergodic approaches. Non-abelian expansion can sometimes produce exponential-scale estimates. Does not require encoding W_k analytically (only needs it as a measurable set).

**Convergence**: Both M2-B responses independently converge on this as the most promising "interface" synthesis.

---

### Direction 3: Direct Log-Time Cancellation

**Idea**: Prove the log-time cancellation theorem directly -- nontrivial cancellation for sums of length ~ck with modulus 5^k. This would be the analytic bridge from Maynard's world (primes with restricted digits) to ours.

**Why it's alive**: It's the most direct path. If proved, it would immediately combine with existing digit-set Fourier machinery (Maynard-type) to yield finiteness.

**Key obstacle**: This IS the core gap. Every existing exponential-sum method requires sum length N >> q^delta for some delta > 0. We need N ~ log(q). No current technique achieves any cancellation in this regime. Standard Korobov technology gives nothing.

**Convergence**: All 8 responses identify this as the irreducible mathematical gap, whether they approach from analytic, dynamical, or structural angles.

**Relationship to Direction 2**: Direction 2 is arguably an attempt to prove Direction 3 by changing the dynamical/algebraic setting where mixing happens. If the spectral gap approach works, it would deliver the needed cancellation through a non-abelian mechanism rather than through direct exponential-sum bounds.

---

## 8. Cross-Cutting Themes

### The "3 samples" enrichment idea

Multiple responses suggest not treating the ~3 exponents per digit level as independent samples, but as a single rigid object. The values (2^n, 2^{n+1}, 2^{n+2}) are linked by multiplication-by-2 with carry. A viable strategy might prove:

> "No x exists such that x, 2x, 4x are all zeroless once len(x) is large."

This is a genuinely pointwise combinatorial/dynamical statement that avoids per-level averaging entirely.

### The "orbit-specific" requirement

Any approach through carry dynamics or symbolic dynamics must exploit something specific to the orbit starting from 1 (powers of 2), not just count admissible paths in the carry automaton. The automaton has supercritical branching (4.5 > 1), so generic path-counting is dead. The actual orbit has additional arithmetic constraints that generic paths do not.

### The "vertical correlation" idea

Zerolessness at digit level k implies zerolessness at all levels j < k (all suffixes are zeroless). This creates a nested tower of constraints. A proof could show this tower becomes "too rigid" for the actual orbit of 2^n, even though the naive branching tree is supercritical.

---

## 9. The Shape of the Gap (from M3-B x2)

M3-B asked: what does the missing mathematics look like? Both responses converge strongly.

### The Landscape Topology (M3-B1)

The search space has four "walls" (barrier hypersurfaces) and four "portals" (surviving escape routes):

**Four Walls:**

| Wall | Name | Effect |
|------|------|--------|
| A | Supercritical branching (4.5 > 1) | Kills all digit-by-digit / level-by-level recursion |
| B | CRT invisibility (density 1.0 in each factor) | Kills all factorized mod-2^k or mod-5^k approaches |
| C | Discrepancy weakness at exponential scale | Kills standard equidistribution / Borel-Cantelli routes |
| D | Non-decaying Fourier obstruction (~1/9) | Kills naive Fourier expansion + cancellation |

**Four Portals:**

1. Coupled-system exponential equidistribution (archimedean + 5-adic joint control)
2. Digit-cylinder-specific shrinking target theorems (bypassing Tseng's general obstruction)
3. New log-time lacunary sum technology (the analytic avatar of the whole problem)
4. Digit-independence theorem for powers of 2 (even weak decorrelation would be a breakthrough)

**Three-coordinate system**: modulus scale (10^k), time scale (~3.32 per level), target measure ((9/10)^k). The obstruction is that coordinate 2 is constant while coordinates 1 and 3 are exponential.

**Success certificate**: Any future method must point to one concrete statement crossing one of the four walls. Best candidate: log-time cancellation.

### Literature Audit (M3-B2)

Concrete references confirming each framework fails at the required scale:

| Framework | Reference | Why It Fails |
|-----------|-----------|-------------|
| Korobov exponential sums | Fuchs survey | Cancellation factor ~exp(-gamma * log^3(N)/log^2(q)) is ~1 when N ~ log(q) |
| Bourgain-Chang additive combinatorics | Bourgain-Chang | Requires orbit length >= q^delta, not N ~ log(q) |
| Shrinking targets for rotations | Tseng (2008) | Deterministic Borel-Cantelli can fail; no guarantee for specific alpha |
| Lacunary discrepancy | Aistleitner-Fukuyama | Only N^{-1/2} control (not exp(-ck)), and only for a.e. alpha |

### Proof Skeleton with Blanks (M3-B2)

The cleanest formulation of what a proof would look like:

- **Step 0**: Re-encode "zeroless at digit length k" as: for n in N_k (~3 exponents), 2^n mod 10^k in S_k
- **Step 1**: Prove sum_{n in N_k} 1_{S_k}(2^n mod 10^k) <= C(9/10)^k + Err(k) with Err exponentially smaller
- **Step 2**: Fourier expand -- reveals the two quantities that must be controlled jointly
- **Blank 1**: Exponential-scale quantitative control in log-time (the core new math)
- **Blank 2**: Structured cancellation avoiding Wiener norm catastrophe
- **Blank 3**: Deterministic mixing/decorrelation for the carry transducer

### Computational Analysis of j(n) (M3-B2)

j(n) = position of first zero digit from the right in 2^n:

| Statistic | Value |
|-----------|-------|
| Mean | 9.95 |
| Median | 7 |
| 90th percentile | 22 |
| 99th percentile | 44 |
| Maximum | 115 (at n=7931) |

Distribution is geometric with parameter ~0.1, consistent with i.i.d. digits. The ratio j(n)/k(n) collapses to ~0, meaning the first zero is always near the right end. Sharp periodicity: j(n)=m is equivalent to a congruence condition on n mod 4*5^m.

Implication: a proof probably cannot "name a digit position" but must show existence via a global mechanism.

### Difficulty Hierarchy (M3-B2)

| Statement | Difficulty Type |
|-----------|----------------|
| At least 1 zero for all large n | Borel-Cantelli / rare-event hard |
| At least k/100 zeros | Intermediate (unknown) |
| At least c*k zeros (normality-like) | Normality hard |

These are genuinely different difficulties, not a continuum. "At least 1 zero" can paradoxically be harder than average-frequency statements because it is a pointwise anti-exception statement.

---

## 10. Historical Paradigm Shifts (from M4-A x2)

M4-A asked: what do breakthroughs in comparable problems look like, and what do they predict for ours?

### Six Case Studies Mapped

| Breakthrough | Key Mechanism | Analogy | Disanalogy |
|---|---|---|---|
| Wiles/FLT | Auxiliary rigid object (Frey curve) | Constraint lives in coupling, not projections | No obvious "Frey object" for digit constraints |
| Perelman/Poincare | Monotone functional across scales | Need exponential control; screams for contractive quantity | No geometric flow; transfer operator yields 4.5^k |
| Green-Tao | Transference from dense model | Sparse set + pseudorandomness | Need non-existence; only ~3 samples |
| Margulis/Oppenheim | Dynamics on homogeneous space + rigidity | Natural dynamical formulation | Kronecker/zero-entropy blocks standard rigidity |
| Elkies/supersingular | Moduli geometry controlling random-looking event | Digit behavior looks random | Digits not obviously moduli data |
| Apery/zeta(3) | Bespoke auxiliary construction | May need one-off, not general theory | Digit condition resists compression |

### Five Extracted Patterns

1. **Reframe into rigid domain** (Wiles, Margulis, Elkies): success comes from re-encoding the problem where rigidity theorems fire
2. **Import from unexpected field** (Perelman, Green-Tao, Elkies): the winning tool often comes from outside the problem's native field
3. **Key step is the right auxiliary object** (Frey curve, pseudorandom majorant, Apery sequences): not stronger estimates, but a constructed object
4. **Computation guides theory** (Apery): heavy experimentation precedes the right ansatz
5. **General theory vs bespoke construction**: breakthroughs split between large frameworks (Wiles/Margulis/Perelman) and specific constructions (Apery/Elkies)

### Five Ranked "Unexpected Source" Fields (convergence across both responses)

1. **Thermodynamic formalism / escape rates** (highest plausibility): open dynamical system with digit-0 as hole; spectral radius < 1 implies exponential escape. Both responses rank this first.
2. **Matrix cocycles / joint spectral radius** (M4-A2): encode digit avoidance as norms of matrix products along the 5-adic orbit; prove deterministic upper bound on growth rate.
3. **Complexity theory / pseudorandomness** (both): circuit lower bounds / extractors as route to digit decorrelation; Green-Tao analogue via complexity rather than averaging.
4. **S-arithmetic / adelic dynamics** (both): embed into higher-rank system where rigidity fires; upgrade from Kronecker to something with positive entropy or unipotent features.
5. **Model theory / definability / automata** (both): Cobham-style rigidity for the set E.

### Innovation Archetype Prediction

Both responses independently predict: **"Apery-like specificity inside a Perelman-like framework"** -- a general structural theorem (spectral gap / escape rate / rigidity) proved for a very specific operator/object tailored to the digit-cylinder + 2^n coupling.

---

## 11. The Reverse Proof (from M4-B x2)

M4-B asked: working backward from what a proof must do, what shapes survive?

### Proof Shape Taxonomy

| Shape | Description | Status |
|---|---|---|
| A: Direct digit witness | Construct j(n), prove digit j is 0 | Alive but needs novel witness rule |
| B: Guaranteed window | Prove zero exists in positions [a(n), b(n)] | Potentially alive via global constraints |
| C: Global carry forcing | Global invariant/energy incompatible with all-nonzero | Most plausible structural survivor |
| D: Cross-scale extinction | Long branches impossible despite local supercriticality | Alive but speculative; needs long-range constraints |
| E: Statistical (log-time cancellation) | Exponential discrepancy in log-time regime | Dead with current tools; alive with new theorems |
| F: Short certificates | Small witness object per n, verifiable efficiently | Unclear; obvious certificates too large |

### Standard Conjectures Audit: None Help

| Conjecture | Verdict | Why |
|---|---|---|
| abc | Irrelevant | S-unit structure, too many terms |
| Schanuel | No bridge | Transcendence does not imply digit statistics |
| GRH | Insufficient | Log-time regime blocks even sqrt cancellation |
| Furstenberg x2-x3 | Irrelevant | Zero entropy / Kronecker |
| Normality of log_10(2) | Far too weak | O(log N/N) vs (9/10)^k needed |

Only custom-fit theorems (log-time cancellation, carry mixing, digit-cylinder shrinking targets) would help. The problem requires genuinely new mathematics, not resolution of existing conjectures.

### Hardness Assessment

| Axis | Verdict |
|---|---|
| ZFC-independent? | No positive evidence; too concrete |
| Missing technique vs unprovable? | Missing technique is far more likely |
| Proof blowup without compression? | Most realistic hardness mode; 4.5^k supercriticality |

### Key New Ideas from M4-B

1. **Global carry forcing** (Shape C): not digit-by-digit (killed), but global invariant for the entire digit string. Three mechanisms: (i) conservation law for carries, (ii) forbidden-pattern theorem for carry chains, (iii) renormalization across digit scales.
2. **Cross-scale extinction** (Shape D): local supercritical branching can coexist with global impossibility of infinite branches ("correlated extinction").
3. **Hybrid structural-statistical path**: structural reduction to a small finite-state object + modest quantitative input at the reduced level.
4. **Certificate complexity equivalence**: "find short certificate" = "find compressible structural reason for zero digit."

---

## 12. The Concept Transfer Game (from M4-C x2)

M4-C asked: what would experts from six other fields see when looking at this problem?

### Six Expert Perspectives (near-perfect convergence across both responses)

| Expert | Reformulation | Best Tool | Verdict |
|---|---|---|---|
| Statistical physicist | 1D lattice, carry = nearest-neighbor interaction, zeroless = hard constraint | Transfer matrix / spectral gap / large deviations | Repackages 4.5^k as partition function; needs "quenched" theorem for deterministic orbit |
| QIT | k qudits, carry = bond variable, projector onto no-zero | Tensor network / MPS / channel contraction | 2^n is a single basis state (no entanglement); useful for computation framing only |
| Tropical geometer | Tropicalize digit equation; carry = non-transversality | Newton polytope / Berkovich / hyperfields | Too coarse: digits {1,...,9} have same valuations; loses residue data |
| Complexity theorist | Language L = {n : 2^n zeroless}; communication complexity of coupling | Circuit complexity / PRG / definability | "Contains a 0?" is a regular language; formalizes coupling obstruction but doesn't produce finiteness |
| Probabilist | Hidden Markov chain; zeroless = avoid state 0 for k steps | Coupling / mixing time / Dobrushin contraction | Cleanest "what would suffice": two-step template |
| Category theorist | Functor from multiplicative monoid to digit strings | Topos / categorical logic | Too abstract; no quantitative control |

### The Two-Step Innovation Template (from probabilist, both responses)

The probabilist's perspective yields the cleanest formulation of what new math is needed:

**Step 1 (correlation decay)**: Prove that the carry-digit constraint system has **uniformly short correlation length** -- influence of boundary conditions at digit position j on digit position j+m decays exponentially in m.

**Step 2 (deterministic typicality)**: Prove that the specific orbit 2^n is **generic enough** relative to the carry-constraint system to inherit the rare-event bound from Step 1.

Step 1 is a statement about the constraint system itself (the transfer operator). Step 2 is the genuinely new mathematics: a "quenched" theorem converting "rare under natural measures" to "never occurs beyond some point" for a specific deterministic orbit.

### The Complexity Reframe

The digit test "contains a 0?" is a **regular language** -- computationally trivial. This means:
- We don't need full equidistribution of 2^n mod 10^k
- We only need pseudorandomness of 2^n against a tiny observer class (finite automata)
- This is strictly weaker than normality

But no known PRG/fooling theorem reaches the required quantitative scale in the log-time regime.

### Cross-Field Collapse

All six perspectives collapse to two surviving families:

1. **Spectral / correlation-length** (physics + QIT + probabilist): the carry-mediated transfer operator and its spectral gap. Three independent fields converge on this as the natural mathematical object.

2. **Complexity / communication** (complexity theorist): formalizes why decoupling fails, but doesn't produce finiteness.

Tropical geometry and category theory lose the residue-level information that makes the problem hard. The missing ingredient across all views: a theorem turning "rare under natural measures" into "never occurs" for a specific deterministic orbit.

---

## 13. Computational Experiments (Post-Synthesis)

Seven experiments were designed based on the synthesis findings and run computationally. The results dramatically sharpen the picture.

### Experiment 1: Transfer Operator with Hole (Escape Rate)
- **Spectral radius of conditioned transfer**: 8.531 (ratio to unconditioned: 0.948)
- Single-step escape rate matches naive 9/10 exactly
- Multi-scale zeroless-to-zeroless fractions EXCEED (9/10)^k: carry dynamics creates persistence
- Survivor counts grow as exactly 4*4.5^{k-1} (confirmed to k=8)

### Experiment 2: Carry Correlation Decay
- **HEADLINE: The carry chain is PERFECTLY MEMORYLESS (Dobrushin coefficient = 0)**
- P(carry_out=1) = 5/9 regardless of carry_in (for zeroless digits)
- All digit-digit correlations < 0.001 at all separations
- Conditional digit distributions deviate from uniform by < 0.0012
- The two-step template's Step 1 (correlation decay) is TRIVIALLY TRUE
- Step 2 (deterministic typicality) is the ENTIRE problem

### Experiment 3: Triple Constraint (x, 2x, 4x)
- Last zeroless pair: n=76. Last zeroless triple: n=35. Last quadruple: n=34.
- P(pair)/P(single)^2 grows with k: 1.00, 1.05, 1.10, 1.16, 1.22, 1.28, 1.35, 1.43 at k=8
- Positive correlation GROWS with scale (carry persistence strengthens)
- The carry-drop mechanism (1-to-0 carry transition) produces elevated zero rate (0.36 vs 0.20)
- Max paired suffix depth: 81 (vs single: 115). Max triple suffix depth: 42.

### Experiment 4: Block Renormalization
- **Block-level branching factor is exactly 4.5^B** for all block sizes B=2..5
- No reduction from blocking whatsoever
- Block entropy near-maximal (efficiency > 0.999)
- Renormalization approach definitively ruled out

### Experiment 5: Global Carry Invariant Search
- **No carry invariant separates zeroless from non-zeroless powers**
- All candidate metrics (carry density, transition density, max carry run, digit sum) overlap completely
- Differences attributed entirely to size (digit count) of zeroless powers being small
- The "global carry forcing" approach (Shape C from M4-B) has no obvious target quantity

### Experiment 6: First-Zero Position Analysis
- Mean j(n) = 11.0 (shifted from geometric(0.1) mean of 10 because j=1 impossible: last digit of 2^n is never 0)
- **38% of j variance explained by n mod 2500 (5-adic structure)**
- Significant autocorrelation at lag 1 (0.328) with period-20 oscillation
- Record growth slower than geometric predicts (slope ratio 0.22)
- j=1 never occurs (2^n mod 10 in {2,4,8,6})

### Experiment 7: Survivor Tree Structure
- **ZERO death rate at every level (k=1 through k=9)**
- Every parent has exactly 4 or 5 children (50/50 split)
- Branching factor exactly 4.5 at every level
- No bottleneck, no narrow waist, no structural weakness of any kind
- The tree is structurally perfect -- the proof CANNOT come from tree structure

### Unified Experimental Picture

The seven experiments converge on a single clear picture:

**The problem contains NO hidden structure.** Specifically:
- Carries are memoryless (Exp 2)
- Digits are i.i.d. uniform (Exp 2)
- The survivor tree has no weakness (Exp 7)
- Blocking doesn't help (Exp 4)
- No carry invariant separates zeroless powers (Exp 5)
- The transfer operator escape rate matches the naive prediction (Exp 1)

**The ONLY thing that matters is equidistribution of 2^n mod 10^k.** The conjecture
is true because the orbit is equidistributed and the "miss" set (digit 0 appears) has
density approaching 1 exponentially. But proving this requires effective equidistribution
bounds for exponential sequences modulo growing moduli -- the exact frontier where
current number theory cannot reach (as confirmed by the meta-synthesis).

**Two non-trivial signals** emerged:
1. **Carry persistence** (Exp 1, 3): consecutive powers have positively correlated zerolessness,
   growing with scale. This means independence arguments UNDERESTIMATE survival.
2. **Strong modular structure in j(n)** (Exp 6): 38% variance explained by 5-adic residue class.
   This gives a concrete handle for orbit-based arguments.

---

## 14. Summary of Consensus

After 46 independent analyses across 23 prompt pairs (16 metaprompt + 10 A-series + 8 B-series + 6 C-series + 6 further experiments):

1. **The problem has one unified obstruction** (no averaging + no compression), not 14 independent barriers
2. **All "outside" paradigms examined reduce** to needing the same missing resources
3. **Three directions survive** the kill analysis, with automata/logic rigidity and non-abelian spectral gap ranked highest
4. **The core missing tool** is log-time cancellation at exponential precision, whether obtained directly (Direction 3), through non-abelian dynamics (Direction 2), or bypassed entirely through logic/automata (Direction 1)
5. **The problem is genuinely open** -- it sits at a frontier where no existing mathematical framework reaches, and likely requires new mathematics
6. **The gap is confirmed by literature audit** -- Korobov, Bourgain-Chang, Tseng, and lacunary theory all fail at exactly the required quantitative scale (M3-B)
7. **j(n) is structurally random** -- the first-zero position follows a geometric distribution, ruling out "name a digit" proof strategies (M3-B)
8. **Four walls / four portals** formalize the search space topology, with a success certificate for evaluating future ideas (M3-B)
9. **Historical pattern predicts hybrid breakthrough**: "Apery-like specificity inside a Perelman-like framework" -- both M4-A responses converge on this
10. **No standard conjecture suffices** -- abc, Schanuel, GRH, Furstenberg, normality of log_10(2) all fail; only custom-fit theorems would help (M4-B)
11. **Global carry forcing is the most plausible structural proof shape** -- distinct from killed digit-by-digit counting; seeks global invariant for entire digit string (M4-B)
12. **Proof blowup without compression** is the most realistic hardness mode, not ZFC-independence (M4-B)
13. **Three fields converge on one object**: physics, QIT, and probability all independently identify the carry-mediated transfer operator with spectral gap as the natural mathematical object (M4-C)
14. **Two-step innovation template**: (1) prove correlation decay for carry-digit constraint, (2) prove deterministic typicality of 2^n -- Step 2 is the genuinely new math (M4-C)
15. **The digit test is computationally trivial**: "contains a 0?" is a regular language, so pseudorandomness against finite automata suffices -- strictly weaker than normality (M4-C)
16. **Carries are perfectly memoryless** (Dobrushin = 0) -- the two-step template's Step 1 is trivially true; Step 2 (deterministic typicality) is the entire problem (Computational Exp 2)
17. **The survivor tree has zero death rate** through k=9 -- no structural weakness exists; the proof cannot come from tree structure (Computational Exp 7)
18. **Block renormalization fails** -- branching factor is exactly 4.5^B with no reduction from blocking; the system has maximum entropy at every scale (Computational Exp 4)
19. **Carry persistence creates growing positive correlations** -- P(pair)/P(single)^2 grows from 1.0 to 1.43 at k=8; independence arguments underestimate survival probability (Computational Exp 3)
20. **The problem is PURELY about equidistribution** -- no hidden carry structure, no tree structure, no block structure; only the orbit's distribution mod 10^k matters (All experiments)
21. **beta(m) = rho(m)/2 decreases monotonically from 4.5 to 1.706** (m=1..18) -- each additional doubling constraint adds ~0.055 nats of information; beta=1 crossing predicted at m~27 (Computational Exp 10)
22. **Conditional survival S_m ~ 0.9 uniformly at every digit level** (m=2..30, mean 0.903, std 0.018) -- perfect digit uniformity among orbit survivors for m >= 5 with chi-squared ~ 0 (Computational Exp 9)
23. **Z(50000) = 35, all at n <= 86** -- no zeroless powers after n=86 in 49,914 checked; density Z(N)/N = 0.0007 and decreasing (Computational Exp 9)
24. **The density-zero argument reduces to a single parity-balance lemma** -- show |E_m|/|Z_m| >= delta > 0 uniformly, where E_m counts even-type survivors (C-series, all 6 responses)
25. **Within-parity digit uniformity is proved** -- the fiber structure u = u_0 + a*5^{m-1} forces exact uniformity within each parity class, a paper-ready theorem (C2-A, C2-B)
26. **The parity-fiber formula S_m = 1 - P(even|survive)/5 connects everything** -- survival rates, digit uniformity, and the missing lemma all reduce to parity balance of the survivor set (C3-A, C3-B)
27. **Noda's transfer-operator is the most aligned existing framework** -- his Lemma 1 already contains the parity-fiber structure; adding a spectral gap for the parity-projected operator would close the density-zero argument (C3-A, C3-B)

---

## 15. A-Series Deep Dive: Equidistribution and Exponential Sums (10 responses)

Five targeted prompts sent to both GPT Pro ("A") and GPT Thinking ("B"), probing equidistribution, exponential sums, discrepancy, character sums, and p-adic dynamics. Full synthesis in A_SERIES_SYNTHESIS.md. Key new findings:

21. **The k^{1/3} exponent comes from v_5(2^h - 1) ~ log_5(h)** -- Korobov differencing is limited by the 5-adic valuation of differences of powers, which grows only logarithmically. This is structural, not a fixable constant (A1-B, A1-A)
22. **With N ~ k sample points, discrepancy has an information-theoretic floor of ~1/k** -- exponentially above the needed e^{-0.105k}. Even perfect exponential sum bounds cannot bridge polynomial to exponential through discrepancy alone (A2-A)
23. **The dominant Fourier character is e(-n/20), of order 20, at j = 5^{k-2}** -- its relative bias GROWS with k (0.110, 0.121, 0.123 for k=2,3,4). The obstruction gets worse, not better (A3-A, A3-B)
24. **The pair-correlation transfer matrix M = [[4,4],[4,5]] has spectral radius (9+sqrt(65))/2 ~ 8.531** -- this unifies the conditioned spectral radius from Exp 1 with the growing pair correlations from Exp 3. Same mathematical object viewed from two angles (A4-A)
25. **The Ramanujan sum structure collapses the counting formula** -- only 5*2^k Fourier terms (those with 5^{k-1} | j) contribute, out of 10^k total. The orbit's exponential sum is exactly the Ramanujan sum c_{5^k}(j), which is 0 for most j (A1-A, A3-A)
26. **Three 2025 references sit on our problem's doorstep** -- Lagarias (ternary digits, dynamical framework), Dumitru (metric finiteness for digit constraints), Noda (transfer-operator for powers of 2). All prove "almost all" or "exceptional sets small" but cannot reach the specific orbit (A4-A)
27. **Density zero is a realistic intermediate target** -- show #{n <= N : 2^n zeroless} = o(N) via logarithmic digit-depth control. Transfer-matrix methods are applicable; you don't need the exact (9/10)^k, just some exponential separation (A4-A)
28. **The bottleneck is not equidistribution but ultra-short, phase-specific hitting in a non-mixing system** -- the system is an equicontinuous rotation on Z_5* with purely discrete spectrum; standard mixing-based Borel-Cantelli doesn't apply; p-adic Diophantine approximation requires a compressed description of Z_k that doesn't exist (A5-A, A5-B)
29. **Every mathematical framework examined reduces to the same obstacle** -- 10 responses from 5 distinct angles (analytic number theory, discrepancy, algebraic number theory, short sums, p-adic dynamics) all arrive at the identical wall. Total convergence with zero exceptions (All A-series)

---

## 16. B-Series Deep Dive: Triple Constraint and Transfer Matrices (8 responses)

Four targeted prompts sent to both GPT Pro ("A") and GPT Thinking ("B"), probing carry automata, transfer matrices, survival probabilities, and pair/triple stepping stones. Full synthesis in B_SERIES_SYNTHESIS.md. Key new findings:

30. **The 4x4 triple-constraint transfer matrix is confirmed 6 times independently** -- M = [[2,2,1,1],[2,2,2,3],[2,2,2,2],[2,2,2,3]] with spectral radius rho ~ 8.03538, root of lambda^3 - 9*lambda^2 + 8*lambda - 2 = 0. Exact recurrence: b_{k+3} = 9*b_{k+2} - 8*b_{k+1} + 2*b_k. (B1-B, B2-A, B2-B, B3-A, B3-B, B1-A)
31. **Per-digit survival ratio for triples is 0.893 vs 0.948 for pairs** -- each additional doubling constraint costs ~0.5 in spectral radius, or ~5.5 percentage points per digit. The triple constraint is substantially more restrictive. (B2-A, B3-A)
32. **Pair extinction for trailing digits is provably FALSE** -- every pair-survivor at level k has at least 4 lifts to level k+1 (5 orbit-lifts minus at most 1 forbidden digit). Pairs exist at every k; concrete example at k=20. The stepping-stone hypothesis must target density, not existence. (B4-B, B4-A)
33. **Triple survivors along the actual orbit exist at k=10 and k=11** -- n = 849,227 gives triple survivors at k=10; n = 38,811,471 at k=11. Any proof strategy claiming early extinction is wrong. (B1-A)
34. **The counting gap is quantified precisely: rho ~ 8.035 >> 5** -- to beat the orbit period 4*5^{k-1} by cardinality alone would require rho < 5. The transfer matrix survivor count is exponentially larger than the period, so counting alone cannot force empty intersection. (All B-series)
35. **Conditioning on survival breaks carry i.i.d. structure** -- unconditionally, carries are Bernoulli(5/9) after step 1, but the zero-avoidance conditioning changes digit distributions at carry-0 positions. The transfer matrix is the exact encoding of this bias. (B3-A, B3-B)
36. **Rigorous all-k upper bound: N_k <= rho^k (C=1)** -- provable by induction from the recurrence, no asymptotic looseness. Alternatively, via PF left eigenvector: N_k <= 1.14214 * rho^k. (B3-A, B3-B)
37. **The orbit-restricted automaton is the natural next computation** -- restrict the transfer matrix to the coset {x : 2^k | x, gcd(x,5)=1} and measure the effective spectral radius. If it drops below 5, counting might work on the orbit itself. But encoding "divisible by 2^k" in base-10 digits is non-local. (B3-B, B2-A)
38. **Convergence across all 8 B-series responses is total** -- same matrix, same eigenvalues, same counts, same limitation, same corrected hypothesis. Zero disagreements. (All B-series)

---

## 17. C-Series Deep Dive: Information Theory and Parity-Balance Reduction (6 responses)

Three targeted prompts sent to both GPT Pro ("A") and GPT Thinking ("B"), probing the information constant, digit uniformity, and the density-zero gap. Full synthesis in C_SERIES_SYNTHESIS.md. Key new findings:

39. **The 1/18 mechanism explains the 0.055-nat information constant** -- a zero digit at a new doubling layer requires carry=0 (prob 1/2) and digit=5 (prob 1/9 among nonzero). So q = 1/18, and I = -ln(17/18) ~ 0.0572 nats. Observed: 0.0550. Both C1 responses derive this independently. (C1-A, C1-B)
40. **beta(m) -> 0 as m -> infinity (no positive floor)** -- the exponential fit beta ~ 4.71*exp(-0.057m) predicts beta=1 at m~27. The total information to push from supercritical to critical is ln(4.5) ~ 1.504 nats, requiring ~26 constraints at 0.057 nats each. (C1-A, C1-B)
41. **Within-parity digit uniformity is automatic and paper-ready** -- the fiber u = u_0 + a*5^{m-1} forces digit m to cycle through exactly one parity class ({0,2,4,6,8} or {1,3,5,7,9}) as a ranges over {0,1,2,3,4}. This is a theorem, not conjecture. (C2-A, C2-B)
42. **Full 10-way uniformity reduces to E = O (parity balance)** -- each even-type fiber contributes one count per even digit; each odd-type fiber contributes one count per odd digit. So full uniformity holds iff |E_m| = |O_m|. (C2-A, C2-B)
43. **The parity-fiber formula: S_m = 1 - P(even|survive)/5** -- from |Z_m| = 4|E_{m-1}| + 5|O_{m-1}| = 5|Z_{m-1}| - |E_{m-1}|. This single formula connects survival rates to parity balance. S_m = 0.9 iff P(even) = 1/2. (C3-A, C3-B)
44. **The weak target S_m <= 0.99 requires only P(even) >= 0.05** -- not 50-50 balance, just "even-type survivors don't vanish." This is a non-concentration statement, plausibly accessible by crude discrepancy bounds. (C3-A, C3-B)
45. **The missing lemma in operator form (carry/parity spectral-gap lemma)**: augment the transfer operator to track even/odd fiber type, then show the induced operator on the parity observable has spectral radius < the Perron eigenvalue. Equivalently: |E_m/Z_m - 1/2| <= C*theta^m for theta < 1. (C3-B)
46. **beta(m) < 1 controls clustering but not isolated points** -- even if m-fold consecutive zeroless windows die out, isolated zeroless powers could persist. The parity-balance lemma is the correct target, not the beta crossing. (C3-B)
47. **Noda is most directly on-target for the missing lemma** -- his transfer-operator formalism already contains the parity-fiber structure (Lemma 1). What's needed: plug in the zeroless weight and prove a spectral gap for the parity-projected operator. (C3-A, C3-B)
48. **Step-20 window transfer matrix suggested** -- build the transfer operator for multiplier 2^20 (targeting lag-20 autocorrelation and the dominant order-20 Fourier character from A-series). If beta_20(m) < 1 for modest m, it could rule out the kinds of clusters the data actually shows. (C3-A)

---

## 18. Experiment 11: Classification Correction and Parity Balance CONFIRMED

Experiment 11 tested the C-series parity-balance prediction computationally, discovered a classification bug in both GPT models, corrected it, and confirmed the entire framework.

**The bug**: Both GPT Pro and GPT Thinking classified even-type survivors using u < 5^m/2. The correct condition is w = u * 2^{-1} mod 5^m < 5^m/2. The factor of 2^{-1} comes from the level-shift relationship: x = 2^m * u at level m implies u_{m+1} = u/2 mod 5^m at level m+1.

**The fix**: Experiment 11b tested three methods. The corrected classification (Method 2) matches ground truth (Method 3, direct digit parity check) exactly at every level m = 1..10.

**Key results with corrected classification**:

| m | Z_m | E/Z | S_{m+1} |
|---|-----|-----|---------|
| 2 | 18 | 0.50000 | 0.90000 |
| 5 | 1,638 | 0.50000 | 0.90000 |
| 8 | 149,268 | 0.50003 | 0.89999 |
| 10 | 3,022,653 | 0.49999 | 0.90000 |

The identity Z_{m+1} = 4*E_m + 5*O_m holds **exactly** at every level tested (m = 1..9). No exceptions.

**What this confirms**: The parity-balance lemma (E/Z -> 1/2) holds empirically in the strong form. The survival rate S_m = 0.9 + O(1/Z_m) at every level. The density-zero reduction chain is computationally validated.

---

## 19. Where This Leaves Us

After 16 AI metaprompt analyses, 11 computational experiments, 10 equidistribution responses (A-series), 8 transfer-matrix responses (B-series), and 6 information-theory responses (C-series), the 86 Conjecture's density-zero component has been reduced to a single lemma that is now empirically confirmed.

**The complete reduction chain (validated by Experiment 11)**:

1. Within-parity digit uniformity is automatic (proved via the u = u_0 + a*5^{m-1} fiber structure)
2. Full 10-way uniformity reduces to E = O (equal even-type and odd-type survivors)
3. The parity-fiber formula gives S_m = 1 - P(even|survive)/5
4. So S_m = 0.9 iff P(even) = 1/2, and S_m <= 0.99 iff P(even) >= 0.05
5. Any uniform S_m < 1 closes density zero via the convergent geometric series

**Note**: The correct classification for even-type uses w = u * 2^{-1} mod 5^m < 5^m/2, not u < 5^m/2 (correcting the original C-series derivation).

**The parity-balance lemma**: Show |E_m|/|Z_m| >= delta > 0 uniformly in m. Empirically confirmed with E/Z = 1/2 + O(Z_m^{-1/2}) through m = 10. The weak form (delta = 0.49) holds trivially in the data.

**The 1/18 mechanism**: The stable 0.055-nat information constant per doubling constraint comes from forbidding (carry=0, digit=5), probability (1/2)(1/9) = 1/18. This explains the exponential decay of beta(m) and predicts the beta=1 crossing at m~27.

**Updated provability hierarchy (A+B+C + Experiment 11)**:

1. Within-parity digit uniformity on orbit -- **PROVED** (fiber structure)
2. Parity-fiber formula S_m = 1 - P(even)/5 -- **PROVED** (arithmetic identity, corrected classification)
3. Identity Z_{m+1} = 4*E + 5*O -- **VERIFIED EXACTLY** (Experiment 11, m=1..9)
4. Parity balance E/Z -> 1/2 -- **EMPIRICALLY CONFIRMED** (Experiment 11, m=1..10)
5. Information constant ~ 0.057 nats/constraint -- **DERIVED** (carry chain)
6. Triple survivor density decays as (0.893)^k -- **PROVABLE** (transfer matrix)
7. Pair survivor density decays as (0.948)^k -- **PROVABLE** (transfer matrix)
8. Metric finiteness (a.e. starting point) -- **PROVABLE** (Borel-Cantelli)
9. Pair survivors exist at every k -- **PROVED** (lifting lemma; false extinction)
10. Density zero for the orbit -- **REDUCED TO ONE LEMMA** (parity-balance, now empirically verified)
11. Finiteness for the specific orbit -- **OUT OF REACH** (needs ultra-short equidistribution)

**Literature assessment**: Noda (arXiv:2510.18414) is closest to the missing lemma; his transfer-operator formalism already contains the parity-fiber structure. Lagarias (math/0512006) is closest for a density-zero theorem via intersection/dimension. Dumitru (arXiv:2503.23177) gives metric support only.

**Revised prediction**: The density-zero theorem is the primary target. The parity-balance lemma is empirically true and should be provable via spectral methods on the carry/parity transfer operator. The key question is whether the map u -> u * 2^{-1} mod 5^m preserves an approximate symmetry of the survivor set. If it does, the spectral gap follows.

**Open computational directions**:
1. Push E_m/O_m to m = 15-20 and measure the convergence exponent theta in |E/Z - 1/2| ~ C * theta^m
2. Step-20 window transfer matrix (target lag-20 autocorrelation structure)
3. Extend beta(m) to m = 25-30 via sparse methods (verify beta=1 crossing)
4. Investigate the 2^{-1} automorphism action on the survivor set (potential structural proof of parity balance)
