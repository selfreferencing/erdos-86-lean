# Erdos-Straus Conjecture: Prompt Fleet Progress Record
## Created: 2026-01-26
## Stage 8 Formalization in Lean 4 / Mathlib

---

## 1. CURRENT STATE OF THE LEAN PROOF

### File: ErdosStraus/ED2/Existence.lean
- **Status**: Compiles successfully in ~92 seconds
- **maxHeartbeats**: 3200000 (set before the doc comment)
- **Total D.6 subcases**: 15 (3 for M=11, 3 for M=19, 9 for M=23)
- **Sorry count**: 1 (the `ed2_qr_classes` theorem)

### The Sorry Region
The single remaining sorry covers primes p where:
- p % 24 = 1
- p % 7 in {1, 2, 4} (quadratic residues mod 7)
- p % 5 in {1, 4} (quadratic residues mod 5)
- p % 11 NOT in {7, 8, 10}
- p % 19 NOT in {14, 15, 18}
- p % 23 NOT in {7, 10, 11, 15, 17, 19, 20, 21, 22}

### The QR Obstruction
D.6 construction produces M = 4*alpha*s*r - 1, so M is always 3 mod 4.
This means D.6 can only cover quadratic NON-residue classes mod M.
The sorry region is defined by primes that are QR mod 7 and QR mod 5,
which D.6 cannot reach directly. This is the fundamental structural limitation.

### Key Build Details
- `set_option maxHeartbeats 3200000 in` placed BEFORE the doc comment
  (Lean 4 requires doc comments immediately before declarations)
- Build command: `cd /Users/kvallie2/Desktop/esc_stage8 && lake build ErdosStraus.ED2.Existence`
- lakefile.lean is at `/Users/kvallie2/Desktop/esc_stage8/lakefile.lean`

---

## 2. D.6 SUBCASE STRUCTURE

### Pattern for each subcase
Each D.6 case proves: given p % M = res, construct (offset, b, c) satisfying
the Type II equation: (p + offset)(b + c) = 4 * offset * b * c

General formulas (from Lemma D.6):
- M = 4*alpha*s*r - 1
- offset = (p + 4*alpha*s^2) / M
- b = alpha*r*s
- c = alpha*r * (r*d - s) where d = (p + 4*alpha*s^2)/M
- For c_coeff > 1: c = c_coeff * ((c_num_expr) / M)

### M=11 cases (3 subcases, existing before this session)
- res=7:  (alpha=1, r=1, s=3)
- res=8:  (alpha=1, r=3, s=1)
- res=10: (alpha=3, r=1, s=1)

### M=19 cases (3 subcases, added this session)
- res=14: (alpha=1, r=1, s=5), offset=(p+100)/19, b=5, c=(p+5)/19, CRT mod 456
- res=15: (alpha=1, r=5, s=1), offset=(p+4)/19, b=5, c=5*(5p+1)/19, CRT mod 456
- res=18: (alpha=5, r=1, s=1), offset=(p+20)/19, b=5, c=5*(p+1)/19, CRT mod 456

### M=23 cases (9 subcases, added this session)
- res=19: (alpha=1, r=6, s=1), offset=(p+4)/23, b=6, c=6*(6p+1)/23, CRT mod 552
- res=7:  (alpha=1, r=3, s=2), offset=(p+16)/23, b=6, c=3*(3p+2)/23, CRT mod 552
- res=10: (alpha=1, r=2, s=3), offset=(p+36)/23, b=6, c=2*(2p+3)/23, CRT mod 552
- res=17: (alpha=1, r=1, s=6), offset=(p+144)/23, b=6, c=(p+6)/23, CRT mod 552
- res=15: (alpha=2, r=3, s=1), offset=(p+8)/23, b=6, c=6*(3p+1)/23, CRT mod 552
- res=20: (alpha=2, r=1, s=3), offset=(p+72)/23, b=6, c=2*(p+3)/23, CRT mod 552
- res=11: (alpha=3, r=2, s=1), offset=(p+12)/23, b=6, c=6*(2p+1)/23, CRT mod 552
- res=21: (alpha=3, r=1, s=2), offset=(p+48)/23, b=6, c=3*(p+2)/23, CRT mod 552
- res=22: (alpha=6, r=1, s=1), offset=(p+24)/23, b=6, c=6*(p+1)/23, CRT mod 552

### Proof structure per subcase
1. `have hdivMa : M | (p + num_a) := by omega` (offset divisibility)
2. `have hdivMb : M | (c_num_expr) := by omega` (c divisibility)
3. `refine <offset, b, c, ?_, by norm_num, ?_, ?_>` (existential intro)
4. Goal 1 (offset % 4 = 3): CRT via `have : p % crt_mod = crt_val := by omega` then omega
5. Goal 2 (c > 0): `Nat.div_pos` or `Nat.mul_pos` + `Nat.div_pos`
6. Goal 3 (Type II identity): set delta/c0, cast to Z, `push_cast`, `nlinarith`

---

## 3. PROMPT FLEET ANALYSIS

### Prompt 1A: Prop 9.25 Bug Analysis
**Key finding**: Prop 9.25 is genuinely false as stated.
- Counterexample: g=2, b'=c'=1, rectangle [0,1)x[1,2)
  - L = {(u,v) : u+v = 0 mod 2}, alpha = gcd(2,2) = 2, d' = g/alpha = 1
  - Rectangle contains only (0,1), which has 0+1=1, not divisible by 2
  - So L intersect R = empty despite H=W=1 >= d'=1
- Two proposed fixes:
  - Fix A: Require H,W >= g (not d')
  - Fix B: Restrict to diagonally aligned rectangles
- The bug is in Step 8 of the paper's proof: "therefore the second coordinate
  is the unique representative in the interval" assumes the constructed point's
  second coordinate lies in the target interval, which isn't proven.

### Prompt 2A: No Non-Lattice Route
**Key finding**: D.6 cannot close the QR gap; the lattice approach is required.
- D.6 is structurally limited to QNR classes (M = 3 mod 4)
- The divisor-pair approach is a special case, not a new method
- Only viable path to close the sorry: full Dyachenko lattice density argument

### Prompt 2B: Divisor-Pair Too Restrictive
**Key finding**: Divisor-pair forces square-discriminant condition.
- More restrictive than the full problem
- Confirms finite congruence cover is the only non-lattice option
- But finite covers can't close ALL residue classes simultaneously

### Prompt 3A: Lean Code for Lattice Steps 1, 2, 4
**Provided**: Lean skeleton code for:
- Step 1: Lattice definition as AddSubgroup (Z x Z)
- Step 2: Proving lattice vectors (c', -b') and (d', d') are in L
- Step 4: Bridge from lattice point to Type II equation
- Confirmed Prop 9.25 is false; proposed two corrected alternatives

### Prompt 3B: Alternative Lattice Approach
**Key difference from 3A**: Instead of fixing Prop 9.25, sidestep it entirely.
- Column-by-column Bezout approach with coprimality assumption
- For each fixed u, use Bezout to find v with correct residue
- Requires only W >= g (one dimension), no diagonal coupling
- **Critical constraint**: needs gcd(c', g) = 1
  - In Dyachenko's setup g = b'c', so Coprime(c', b'c') fails when c' > 1
  - If g is reinterpreted as m = 4A-p, coprimality is a separate question
- Provided AddSubgroup definition, mem_v1, mem_diag_of_dvd helper lemmas

### Prompt 4A: Hybrid Computational + Analytic Plan
**Architecture**: Two-phase approach:
- Part 1: Bounded search + native_decide for small primes
  - ed2_search using nested Finset.findSome? (correct pattern, large bounds needed)
  - Hardcoded certificates verified by `decide` (sanity checks work)
  - Witness list approach feasible for modest bounds
- Part 2: Analytic tail for p > B
  - Bridge lemma: A(4bc-b-c) = Pbc iff (P+offset)(b+c) = 4*offset*b*c
  - ED2 existence from Theorem 9.21 via lattice construction
  - Threshold B can be set to minimize edge-case reasoning
- **Limitation**: Doesn't solve the rectangle lemma; only provides architecture

### Prompt 5A: Theorem D.1 (Appendix D) Formalization
**Forward direction (D1_forward_int)**: Clean and likely compilable.
- Uses calc chain with ring to show:
  (4*alpha*d*b - 1)(4*alpha*d*c - 1) = 4*alpha*P*d^2 + 1
- Given A = alpha*b*c and b+c = (4A-P)*d
- ring handles all the algebra

**Backward direction (D1_backward_int)**: Correct math, messy code.
- Over-engineered with nested simpa/by blocks (3 levels deep)
- Strategy: expand, cancel +1 via linarith, divide by 4*alpha*d
- Would need significant cleanup to compile
- A 10-line version using mul_left_cancel0 would be better

### Prompt 6A: Bridge Lemma (ED2 Parameters -> Type II)
**Most useful single lemma from the fleet.**
- Proves: given (alpha, b', c', d') with sum condition, derive:
  1. offset % 4 = 3 (from p % 4 = 1)
  2. b > 0, c > 0 (from positivity)
  3. Type II identity
- Where offset = 4*alpha*b'*c' - p, b = alpha*d'*b', c = alpha*d'*c'
- Proof structure sound: p + offset = 4A trivializes LHS
- The offset%4=3 proof is over-engineered (manual case split on r=0,1,2,3)
  but omega should handle it directly
- The calc chain for the identity should work with push_cast + ring
- **Minor issues**: interval_cases syntax may need adjustment,
  simpa chains in False.elim branches are fragile
- Worth implementing with cleanup

### Prompt 7A: Interval Representative Lemma (first attempt)
**Two versions**: Int and Nat
- Int: t = (r-x0) % m, u = x0+t. Correct but over-engineered (15 lines for
  divisibility that should be ~3 lines)
- Nat: t = (r%m + m - x0%m) % m. Correct, verbose calc chain for mod equality
- Both would benefit from aggressive omega usage
- Building block for rectangle-hitting argument

### Prompt 7B: Interval Representative Lemma (second attempt)
**Same theorems, slightly cleaner.**
- Int version: uses calc chain for divisibility, more readable than 7A
- Nat version: same t formula, different calc structure
- Neither would compile without tweaks (Int.ediv_add_emod name uncertainty)
- For implementation: write both in ~10 lines each using omega

### Prompt 8A: Correct Rectangle-Hitting Replacement
**Most important answer for closing the sorry.**
- Confirms the g=2, b'=c'=1 counterexample independently
- Provides `rect_hits_kernel` lemma: correct replacement for Prop 9.25
  - Fix any u in x-interval (just u=x0)
  - Compute target residue r = g - (u*b)%g
  - Use coprimality: Nat.exists_mul_mod_eq_of_coprime to solve c*v0 = r mod g
  - Lift v0 to y-interval using interval representative lemma (needs W >= g)
  - Chain congruences: g | (u*b + v*c)
- **Key constraint**: requires Nat.Coprime c g and W >= g
- **Open question**: how to ensure coprimality in the Dyachenko application
  - If g = b'c' (paper's definition), Coprime(c', b'c') fails for c' > 1
  - If g = m = 4A-p (Appendix D modulus), coprimality is parameter-dependent

### Prompt 8B: Rectangle Hits Lattice (fixing Prop 9.25, second response)
**Strong confirmation of 8A, with better Lean skeleton.**
- New counterexample: g=6, b'=1, c'=5, alpha=gcd(6,6)=6, d'=1
  - Rectangle [1,2)x[0,1): only point (1,0), 1*1+0*5=1 not div by 6
  - Cleaner than 8A's example because d'=1 makes failure especially stark
- Same fix as 8A: require H >= g (not d') with IsCoprime b' g
- Lean skeleton `rect_hits_L_of_H_ge_g`: uses IsCoprime (Bezout coefficients),
  interval_has_mod_rep from Prompt 7, dvd_add for combining divisibility
- Three admits remaining: bookkeeping (scoping u, one ring computation)
- Takeaway: replace Prop 9.25 with safe lemma, ensure long side >= g

### Prompt 9A: Simpler Proof for 6 QR Classes (first response)
**Best mathematical analysis of the strategic landscape.**
- Section 0: Cleanest ED2 -> Type II bridge statement
  - offset = (b'+c')/d', automatically 3 mod 4 by Theorem 7.3
  - Type II follows from p(b+c) = offset(4bc - b - c)
- Q1: No clean parametric identity for QR classes
  - D.6 single-parameter congruence structurally limited to QNR
  - No one-page identity known
- Q2: "Square discriminant" shortcut reduces to factoring 4p+1
  - x^2 - y^2 = 4p+1, equivalent to controlled factorization
  - Residue class assumptions alone don't guarantee this
- Q3: **KEY INSIGHT** -- Don't prove general rectangle-hitting.
  Prove a TAILORED lemma for the specific ED2 rectangle, which has
  alignment properties the diagonal coset argument can exploit.
  Much simpler to formalize than general corrected lemma.

### Prompt 9B: Simpler Proof for 6 QR Classes (second response)
**Confirms 9A, with two additional insights.**
- Binary quadratic forms angle: p = x^2 + 35y^2 could selectively hit QR classes
  (splitting in specific number fields), but no known short path to Type II
  and formalizing class field theory would be far heavier than Dyachenko
- More explicit two-generator fix for Prop 9.25:
  - Parameterize (u,v) = a(c',-b') + k(d',d')
  - Pick a (mod d') to tune "phase" between k-interval constraints
  - Pick k via 1D interval representative lemma
  - This is a "CRT/interval argument", entirely elementary
- Bottom line: keep Dyachenko's architecture but rewrite box-hitting as
  explicit two-generator, interval/CRT lemma

### Prompt 10A: Prop 9.25 Proof Verification (first response)
**Clean, rigorous confirmation of the bug.**
- Precise identification: Step 8 requires both (1) correct residue mod d'
  AND (2) membership in [y0, y0+W). Proof establishes (1) but assumes (2).
  Uniqueness cannot be applied to elements outside the interval.
- Same counterexample as 8A (g=2, b'=c'=1, [0,1)x[1,2)), independently derived
- Two repair paths: H >= g fix, or restrict to specific rectangle classes
- ED2 application: can work IF rectangles have the geometric alignment property

### Prompt 10B: Prop 9.25 Proof Verification (second response)
**Strongest and most complete analysis across the entire fleet.**
- Superior counterexample: g=6, b'=c'=1, alpha=gcd(6,2)=2, d'=3
  - Rectangle [1,4)x[0,3), H=W=3=d'. Sums range 1-5, never 0 mod 6.
  - Shows failure with non-trivial d'=3 (not just degenerate d'=1)
- Clearest coupling formulation: two m-intervals
  - m in [(x0-u0)/d', (x0+H-u0)/d') width >= 1
  - m in [(y0-v0)/d', (y0+W-v0)/d') width >= 1
  - Two width-1 intervals need NOT intersect
- Explicit diagonal alignment condition for original proof to work:
  [y0,y0+W) must contain [x0+(v0-u0), x0+H+(v0-u0))
- Honest ED2 assessment: gap remains unless rectangles have implicit alignment

### Crashed / Missing Prompts
The following prompts crashed and produced only traces:
- 4B, 5B, 6B, 10B-variant (4 answers lost)
- These covered less critical areas (4B: computational backup,
  5B: D.1 backward direction, 6B: bridge variant)

---

## 4. SYNTHESIS: PATH TO CLOSING THE SORRY (Updated with full fleet)

### What we know works
1. D.6 subcases (M=11, 19, 23) cover many residue classes
2. Additional M values could cover more (find_covering.py shows D6 covers most primes)
3. Bridge lemma (6A, 9A, 9B) connects lattice parameters to Type II equation
4. Interval representative lemma (7A/7B) is a building block
5. The corrected rectangle lemma (8A/8B) works with H >= g and coprimality

### What's blocked
1. Prop 9.25 is FALSE as stated (confirmed by 8 responses: 1A, 2A, 3A, 3B, 8A, 8B, 10A, 10B)
2. The correct replacement needs coprimality (IsCoprime b' g or IsCoprime c' g)
3. Coprimality condition may not hold universally in Dyachenko's setup
4. No clean parametric identity exists for the 6 QR classes (9A, 9B)
5. The "square discriminant" shortcut reduces to factoring 4p+1 (9A), no easier

### Strategic options (ranked by feasibility, updated with fleet insights)

**Option A: Two-generator CRT/interval lemma (RECOMMENDED)**
- 9A/9B's key insight: don't prove general rectangle-hitting at all
- Use both lattice generators: (c',-b') and (d',d')
- Parameterize as (u,v) = a(c',-b') + k(d',d')
- Pick a (mod d') using coprimality gcd(c',d')=1 (follows from gcd(c',g)=1)
- Pick k via interval representative lemma
- This is entirely elementary: CRT + interval arithmetic
- **Advantage**: Avoids the coupling problem entirely by using 2 degrees of freedom
- **Risk**: Still need to verify the coprimality gcd(c',g)=1 holds in ED2 setup
- **Lean complexity**: ~100 lines of new lemmas (lattice def, generators, CRT step, bridge)

**Option B: Corrected rectangle lemma with H >= g**
- Formalize 8A/8B's `rect_hits_L_of_H_ge_g` with coprimality
- Simpler proof: fix v=y0, solve for u via Bezout, lift to interval
- Requires only W >= g (one dimension), H >= 1 (trivial)
- **Advantage**: Simpler proof structure than Option A
- **Risk**: Need W >= g in the application; g may be large relative to box side

**Option C: More D.6 M-values + finite congruence cover**
- Add more M values (M=31, 43, 47, 59, 67, 71, ...) to cover more residues
- Use find_covering.py to identify which M values give best coverage
- Pro: Each D.6 subcase is mechanical (gen_lean_cases.py automates it)
- Con: Cannot close all classes (QR obstruction is fundamental)
- Con: Only narrows the sorry, never eliminates it

**Option D: Hybrid computational + analytic**
- Use native_decide / precomputed witnesses for p < B
- Use Options A or B for p >= B
- Pro: Reduces the lattice argument to "sufficiently large" primes
- Con: Still needs the lattice argument; computational part adds complexity

**Option E: Accept the sorry with documentation**
- Document the sorry as depending on Prop 9.25 (known to be false as stated)
- Note that computational verification passes up to 10^7
- Publish the formalization with one sorry annotated as a known paper gap
- Pro: Honest, publishable, documents a genuine issue in the paper
- Con: Not sorry-free

---

## 5. KEY FILES

### Main proof file
`/Users/kvallie2/Desktop/esc_stage8/ErdosStraus/ED2/Existence.lean`
- ed2_qr_classes theorem with 15 D.6 subcases
- Sorry at approximately line 410 (after all by_cases chains)

### Code generation
`/Users/kvallie2/Desktop/esc_stage8/gen_lean_cases.py`
- Generates Lean code for M=19 and M=23 subcases
- Data tables: cases_m19 (3 entries), cases_m23 (9 entries)
- gen_chain() handles nested by_cases with proper indentation

### Generated output
`/Users/kvallie2/Desktop/esc_stage8/lean_m19_m23_code.txt` (225 lines)
`/Users/kvallie2/Desktop/esc_stage8/lean_replacement.txt`

### Analysis scripts
`/Users/kvallie2/Desktop/esc_stage8/find_covering.py`
- Finds covering sets for the 6 hard QR classes
- Phase 1: D6 coverage with M values up to 200
- Phase 2: Divisor-pair (DP) coverage for remaining primes
- Phase 3: Essential M-values analysis
- Phase 4: Verification up to 10M

`/Users/kvallie2/Desktop/esc_stage8/analyze_uncovered.py`
- Analyzes which primes remain uncovered after D6

---

## 6. TECHNICAL LESSONS LEARNED

### Lean 4 / Mathlib specifics
1. `set_option maxHeartbeats N in` must come BEFORE doc comments, not between
   doc comment and declaration
2. `Nat.div_mul_cancel` gives `a / b * b = a` from `b | a`
3. `exact_mod_cast` converts Nat facts to Int facts
4. `push_cast` + `nlinarith` handles the Type II identity verification
5. CRT values computed as p % lcm(24, M) to determine offset % 4 = 3

### D.6 formula derivation
- M = 4*alpha*s*r - 1
- Residue covered: (-4*alpha*s^2) mod M
- offset numerator: p + 4*alpha*s^2
- b = alpha*r*s (constant for given alpha, r, s)
- c numerator: alpha*r * (r * ((p + 4*alpha*s^2)/M) - s)
  = alpha*r * (r*d - s) where d = offset
- c_coeff: alpha*r^2 (the coefficient of (c_num_expr / M))
- c_num_expr: r*p + r*4*alpha*s^2/M*... simplified to patterns like "3*p+2"

### Indentation rules for nested by_cases
- Each by_cases adds 2 to the indent level
- Bullet · at indent ci, content at ci+2
- Negative branch · at ci, next by_cases at ci+2
- M transition: negative · gets a comment, then by_cases at ci+2

---

## 7. PROMPT FLEET FINAL INVENTORY

### Received and analyzed (16 total):
1A, 2A, 2B, 3A, 3B, 4A, 5A, 6A, 7A, 7B, 8A, 8B, 9A, 9B, 10A, 10B

### Crashed / lost (4 total):
4B, 5B, 6B, and one additional variant

### Coverage by topic:
- Full approach strategies: 1A, 2A, 2B, 3A, 3B, 4A (6 answers)
- Theorem D.1 formalization: 5A (1 answer, 5B crashed)
- Bridge lemma: 6A (1 answer, 6B crashed)
- Interval representative: 7A, 7B (2 answers)
- Rectangle hitting / Prop 9.25 fix: 8A, 8B (2 answers)
- Research on simpler proofs: 9A, 9B (2 answers)
- Prop 9.25 verification: 10A, 10B (2 answers)

---

## 8. COMPUTATIONAL VERIFICATION RESULTS

From find_covering.py and related scripts:
- Hard primes (p%24=1, p%7 in {1,2,4}, p%5 in {1,4}, p%11 not in {7,8,10})
  up to 1M: counted and filtered
- D6 with M values up to 200 covers most hard primes
- DP (divisor-pair) covers remaining primes up to tested limits
- ALL primes verified up to 10^7 (zero failures)
- Verification files:
  - k13_verification_10000000.txt
  - k13_verify_50000000.txt
  - max_witness_scan_100000000.txt
  - crt_certificate_2000.txt / crt_certificate_5000.txt

---

## 9. TODO STATUS

- [x] Record Dyachenko paper content into notes file
- [x] Analyze paper content to extract d' bound and formalization path
- [x] Verify Existence.lean still compiles cleanly
- [x] Derive D6/M=11 parametric identities for p mod 11 in {7,8,10}
- [x] Add M=19 and M=23 cases to ed2_qr_classes in Existence.lean
- [x] Build and verify the extended proof compiles
- [x] Review GPT prompt answers for lattice formalization (16/16 received)
- [x] Save final prompt fleet progress record
- [x] Read Section 9 of Dyachenko paper (coprimality resolved: gcd(b',g)=gcd(c',g)=1 is explicit)
- [ ] Determine final strategy for closing the sorry
- [ ] Implement chosen sorry-closing strategy

---

## 10. CROSS-PROMPT CONSENSUS (Final, 16 responses)

### Universally agreed (all relevant prompts concur):

1. **Prop 9.25 is false as stated** (1A, 2A, 3A, 3B, 8A, 8B, 10A, 10B)
   - Three independent counterexamples: g=2/b'=c'=1 (8A,10A), g=6/b'=1/c'=5 (8B), g=6/b'=c'=1 (10B)
   - 10B's is strongest: d'=3 (non-trivial period), sums 1-5 never 0 mod 6
   - Step 8 gap: congruence alone does not imply interval membership
2. **D.6 cannot close the QR gap** (2A, 2B, 9A, 9B)
   - M = 4*alpha*s*r - 1 always 3 mod 4, forcing QNR-only coverage
   - No parameter choice can flip this
3. **No simple parametric identity exists** for the 6 QR classes (9A, 9B)
   - Square discriminant approach reduces to factoring 4p+1 (9A)
   - Binary quadratic forms angle is theoretically possible but unformalizable (9B)
4. **Lattice approach is required** for full closure (2A, 2B, 3A, 3B, 4A, 9A, 9B)
   - But only elementary modular arithmetic + combinatorics needed, not Minkowski
5. **Bridge lemma is trivial algebra** (6A, 9A, 9B)
   - p + offset = 4A makes the identity immediate
   - offset = (b'+c')/d' is automatically 3 mod 4 by Theorem 7.3
6. **Interval representative lemma is a building block** (7A, 7B, 8A, 8B)
   - Should compile in ~10 lines with omega

### Key uncertainty: RESOLVED (2026-01-26, Section 9 analysis)

1. **Coprimality condition: CONFIRMED in the paper.**
   - Theorem 9.21 condition (I) explicitly states: gcd(b', g) = gcd(c', g) = 1
   - Lemma 9.22 explicitly requires: gcd(b', g) = gcd(c', g) = 1
   - This is a DEFINING CONDITION of the admissible parameter set C_ED2(P)
   - Since d' | g and gcd(c', g) = 1, we get gcd(c', d') = 1 for free
   - This means Option A (two-generator CRT) is fully viable
   - The coprimality is NOT derived; it's part of what "admissible" means

2. **Prop 9.25 bug confirmed in paper text.**
   - Lines 3584-3830: proof picks p0 = (u0, v0), finds u* = u0 (mod d') in x-interval
   - Sets m := (u* - u0)/d', shifts both coordinates by m*d'
   - ASSUMES v0 + m*d' = v* in y-interval, but m was determined by x-coordinate only
   - This is exactly the coupling error identified by all GPT prompts

3. **Which fix is best for Lean**: Two-generator CRT (Option A) recommended
   - Both generators (c',-b') and (d',d') are in L (Lemma 9.22)
   - gcd(c', d') = 1 from coprimality (resolved above)
   - Use CRT: for target x-residue mod d', solve for a mod d' using gcd(c',d')=1
   - Then k handles interval placement
   - Entirely elementary: no Minkowski, no geometry, just CRT + interval arithmetic

### Prop 9.25 counterexample summary table:

| Source | g | b' | c' | alpha | d' | Rectangle | Why fails |
|--------|---|----|----|-------|----|-----------|-----------|
| 8A, 10A | 2 | 1 | 1 | 2 | 1 | [0,1)x[1,2) | sum=1, not 0 mod 2 |
| 8B | 6 | 1 | 5 | 6 | 1 | [1,2)x[0,1) | 1*1+0*5=1, not 0 mod 6 |
| 10B | 6 | 1 | 1 | 2 | 3 | [1,4)x[0,3) | sums 1-5, never 0 mod 6 |

---

## 10. COMPUTATIONAL WITNESS INFRASTRUCTURE (Session 3, 2026-01-26)

### Coverage Analysis Results

| Metric | Value |
|--------|-------|
| Q = lcm(24,5,7,11,19,23) | 4,037,880 |
| Sorry-region classes mod Q | 10,752 |
| D6-covered (M <= 5000) | 10,293 (95.7%) |
| Uncovered classes | 459 (4.3%) |
| QNR obstruction | PROVEN: D6 residue always QNR mod M |

### QNR Obstruction Proof
For D6 with M = 4*alpha*s*r - 1:
Legendre symbol (-4*alpha*s^2 / M) = (-1/M) * (alpha/M) * (4s^2/M) = -1.
- M = 3 mod 4 => (-1/M) = -1
- 4s^2 is a perfect square => (4s^2/M) = 1
- alpha is QR mod M (by quadratic reciprocity) => (alpha/M) = 1
Therefore D6 can ONLY produce QNR residues. 459 classes are permanently
uncovered at the class level. Individual primes in those classes ARE solvable
by D6 with specific large M values, but no finite M-set covers the class.

### Witness Generation
- Script: `gen_witnesses.py` finds (offset, b, c) for each sorry-region prime
- Methods: D6 construction (max_M=10000) then DP fallback (max_delta=100000)
- Results: ALL sorry-region primes up to 10M have witnesses (6,959 primes)

### Lean Infrastructure Created (COMPILES SUCCESSFULLY)

Three new files in `ErdosStraus/ED2/`:

1. **Type2Data.lean** (34 lines)
   - `Type2Cert` structure: (p, offset, b, c) deriving DecidableEq, Repr
   - `Type2CertOK` predicate: offset%4=3, b>0, c>0, identity in N
   - Decidable instance for native_decide

2. **Type2CertData.lean** (770 lines, B=1M)
   - 750 Type2Cert entries for all sorry-region primes up to 1,000,000
   - Needs `set_option maxRecDepth 65536 in` before the definition
   - Generated by `gen_lean_type2.py`

3. **Type2Covering.lean** (35 lines)
   - `type2_certs_all_ok : List.Forall Type2CertOK type2Certs := by native_decide`
   - `type2_cert_ok_gives_witness`: bridges N identity to Z existential
   - Build time: ~150s total for all three files

### Build Lessons
- `List.Forall.forall` does NOT exist in Lean 4.27.0-rc1
- `?` in refine needs `?_` (not just `?`)
- `push_cast` before `exact_mod_cast` is unnecessary; `exact_mod_cast` alone works
- Lists >500 entries need `set_option maxRecDepth 65536 in`
- `native_decide` handles 750 Type2Cert entries without issue

### Blueprint Status
- Full blueprint saved to `LATTICE_BLUEPRINT.md` with 9 sections
- Section 9 gives concrete Lean implementation strategy for Aristotle
- Two-phase approach: computational (p <= B) + analytic sorry (p > B)
- Analytic tail blocked on Landau-Ramanujan theorem (not in Mathlib)

### Next Steps for Aristotle
1. Connect Type2Covering theorems to the sorry in Existence.lean:415
2. Split sorry into `p <= B` (use cert lookup) and `p > B` (documented sorry)
3. The coverage bridge (finding p in the cert list) needs either:
   - native_decide over Fin range (may be slow for B=1M)
   - interval_cases with explicit witnesses per prime
   - Trust external Python verification
4. Scale to B=10M (6,959 entries) if needed
