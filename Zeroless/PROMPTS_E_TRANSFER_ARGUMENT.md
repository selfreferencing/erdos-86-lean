# E-Series Prompts: The Transfer Argument and the Strong Parity-Balance Lemma

## Context for all prompts

These prompts build on 55 prior AI responses (16 metaprompt, 10 A-series, 8 B-series, 6 C-series, 9 D-series) and 11 computational experiments. The D-series **proved density zero unconditionally** via a range argument on the recurrence e_{m+1} = f(e_m, p_m). The E-series targets the STRONG parity-balance lemma: e_m -> 1/2 exponentially, with the exact rate theta = 2*sqrt(6)/(9+sqrt(65)) = 0.28712.

**Problem**: 2^86 is the last power of 2 with no digit 0 in base 10. Density zero is proved. We now seek the strong form: |e_m - 1/2| = O(theta^m) where theta = 0.287.

**What the D-series established**:

The D-series constructed a 4x4 parity-augmented carry matrix M_aug with states (carry, parity-type) in {0,1} x {E,O}. In the parity (+,-) basis, M_aug decomposes into:

- **M_tot = [[4,4],[4,5]]**: governs total survivor count Z_m. PF eigenvalue = (9+sqrt(65))/2 ~ 8.531.
- **M_par**: governs parity bias Delta_m = E_m - O_m. Characteristic polynomial lambda^2 - 3*lambda + 6 = 0, eigenvalue modulus sqrt(6) ~ 2.449.
- **theta = sqrt(6) / ((9+sqrt(65))/2) = 0.28712**: the spectral gap ratio.

Two independent GPT-Pro constructions gave DIFFERENT 4x4 matrices but IDENTICAL spectral decomposition (same M_tot, same M_par characteristic polynomial, same theta). This is strong cross-validation.

**What independent computational verification revealed (the gap the E-series must close)**:

Five findings from independent verification expose a subtle gap between the matrix theory and the orbit:

1. **Neither M_aug is the exact orbit transfer matrix.** Testing v_{m+1} = M_aug * v_m overestimates survivor counts by a factor ~1.9 = PF/4.5 = 8.531/4.5. The carry matrix M_tot counts the PAIR constraint (both x and 2x have nonzero digit at position m), while the orbit fiber formula Z_{m+1} = 4E_m + 5O_m counts orbit children. Even parents: 8 carry transitions vs 4 orbit children (factor 2); odd parents: 9 carry transitions vs 5 orbit children (factor 1.8).

2. **The per-level transition matrix is NOT constant.** The empirical (carry, u-parity) transition matrix changes with level m. The state (carry, u mod 2) is NOT a sufficient Markov statistic. The u-parity depends on ALL digits of x through the global 5-adic parametrization u = x/2^m.

3. **The eigenvalue ratio theta = 0.287 nonetheless matches the observed parity decay.** Despite the overcount, the envelope of |E_m/Z_m - 1/2| decays at rate ~0.29, consistent with theta = 0.287. The parity bias "knows about" the pair-constraint spectral gap even though the count normalization is wrong.

4. **All parity imbalance comes from carry-1 survivors.** At every level tested (m=1..9), among survivors with carry-out = 0, E = O exactly. ALL of the E - O imbalance resides in the carry-1 component.

5. **The orbit carry distribution is 4/9, not the PF equilibrium.** Among orbit survivors, the fraction with carry-out = 0 is 4/9 at every level, NOT the PF equilibrium ~0.469.

**The central question for the E-series**: How does the pair-constraint spectral gap (trivially: sqrt(6) < 8.531) rigorously control the orbit's parity balance?

**The proved framework (all identities exact through m=12)**:

At each digit level m, the orbit of 2^n mod 10^m has period T_m = 4*5^{m-1}. Elements are x = 2^m * u where u in (Z/5^m Z)*. Survivors have all m trailing digits nonzero. E_m = #{even-type survivors} (u even), O_m = #{odd-type survivors} (u odd), Z_m = E_m + O_m.

Key identities:
- Z_{m+1} = 4*E_m + 5*O_m (exact, proved)
- e_{m+1} = (2 + p_m(1-e_m)) / (5 - e_m) where p_m in [0,1]
- e_m in [2/5, 3/5] for all m (proved unconditionally; density zero follows)
- Bias identity: e_{m+1} - 1/2 = (p_m - 1/2)(1 - e_m)/(5 - e_m) (proved)

Experiment 11 data:

| m | Z_m | E_m | O_m | E/Z | |E/Z - 1/2| |
|---|-----|-----|-----|-----|------------|
| 1 | 4 | 2 | 2 | 0.500000 | 0 |
| 2 | 18 | 9 | 9 | 0.500000 | 0 |
| 3 | 81 | 41 | 40 | 0.506173 | 6.17e-03 |
| 4 | 364 | 182 | 182 | 0.500000 | 0 |
| 5 | 1,638 | 819 | 819 | 0.500000 | 0 |
| 6 | 7,371 | 3,685 | 3,686 | 0.499932 | 6.78e-05 |
| 7 | 33,170 | 16,582 | 16,588 | 0.499910 | 9.04e-05 |
| 8 | 149,268 | 74,639 | 74,629 | 0.500033 | 3.35e-05 |
| 9 | 671,701 | 335,852 | 335,849 | 0.500002 | 2.23e-06 |
| 10 | 3,022,653 | 1,511,320 | 1,511,333 | 0.499998 | 2.15e-06 |
| 11 | 13,601,945 | 6,800,982 | 6,800,963 | 0.500001 | 6.98e-07 |
| 12 | 61,208,743 | 30,604,369 | 30,604,374 | 0.500000 | 4.08e-08 |

Fitted decay: |E/Z - 1/2| ~ 0.26 * (0.29)^m.

E - O sequence: [0, 0, +1, 0, 0, -1, -6, +10, +3, -13, +19, -5]

---

## Prompt E1: The Pair-to-Orbit Transfer Argument

The D-series identified theta = 0.287 as the spectral gap ratio of the 4x4 parity-augmented carry matrix. But this matrix describes the PAIR constraint (x and 2x both zeroless at each digit position), NOT the orbit's fiber extension (level-m survivors producing level-(m+1) survivors). The normalization differs by a factor ~1.9 at every level. Yet the RATIO theta = sqrt(6)/((9+sqrt(65))/2) matches the observed parity decay.

This prompt asks: why does the pair-constraint spectral gap control the orbit's parity balance, despite the overcount?

**The pair constraint vs. the orbit fiber**:

Consider the carry matrix M_tot = [[4,4],[4,5]] with states {carry-0, carry-1}. Entry M_tot[i,j] counts: "how many digits d in {1,...,9} produce carry-out i when the carry-in is j and 2d + j gives a nonzero output digit." This counts ordered pairs (d_{m}, d_{m+1}) where d_{m+1} = (2*d_m + carry) mod 10 and both are nonzero. The PF eigenvalue 8.531 is the growth rate of admissible digit STRINGS of length m (i.e., the zeroless digit constraint on generic integers, not tied to the orbit).

The orbit fiber formula says: a level-m survivor x produces 4 children if x is even-type, 5 if odd-type. This gives Z_{m+1} = 4*E_m + 5*O_m with average branching 4.5 (since e_m ~ 1/2). The factor 1.9 = 8.531/4.5 accounts for the overcounting: each carry transition corresponds to ~1.9 orbit children on average.

But the parity RATIO is preserved: if the pair constraint has E/Z = 1/2 + epsilon, the orbit also has E/Z = 1/2 + epsilon (to leading order), because the 1.9x overcount factor is the SAME for even-type and odd-type survivors. The overcount cancels in the ratio.

**Questions:**

1. Make this cancellation argument precise. The 1.9x overcount is NOT exactly the same for even-type (factor 2 = 8/4) and odd-type (factor 1.8 = 9/5). The slight asymmetry (2 vs 1.8) introduces a correction. Compute the correction and show it is subleading relative to the theta^m decay.

2. The pair-constraint spectral gap gives: among all m-digit strings with no zero digits such that each digit is obtained from the previous by the doubling-carry rule, the fraction with even leading digit converges to 1/2 at rate theta^m. The orbit constraint is: among all residues x = 2^m * u mod 10^m with u in (Z/5^m Z)* such that all digits of x are nonzero, the fraction with u even converges to 1/2. These are DIFFERENT counting problems. The first counts digit strings; the second counts orbit residues. What is the exact relationship? Is there a bijection, a projection, or a measure-preserving map?

3. The carry matrix counts digit-extension transitions. The orbit counts residue-class survivors. Each residue class has a unique digit sequence (its base-10 representation), so there IS a natural bijection between m-digit zeroless strings and zeroless residues mod 10^m. Under this bijection, does the "parity type" (u mod 2) correspond to a simple property of the digit string? If so, the spectral gap on strings directly transfers to a spectral gap on residues.

4. The independent verification found that the orbit carry distribution is 4/9 at every level, while the PF equilibrium of M_tot is ~0.469. This means the orbit does NOT sample the carry states according to the PF measure. However, the PARITY ratio E/Z still matches the spectral prediction. Explain why the carry distribution can be "wrong" without affecting the parity ratio. Is this because the parity bias is controlled by M_par, which is independent of M_tot in the block decomposition?

5. The independent verification found that carry-0 survivors have E = O EXACTLY at every level. This means all parity imbalance resides in the carry-1 subspace. Does this follow from the structure of M_par? The M_par matrix governs Delta = E - O, and its action restricted to carry-0 might be trivial (zero). Check whether the carry-0 row of M_par is zero, which would explain the exact balance.

6. Formulate a rigorous theorem connecting the pair-constraint spectral gap to the orbit parity balance. What are the necessary hypotheses? Possible framework:

   **Theorem (Transfer)**: Let S_m be the set of zeroless residues mod 10^m. Let E_m, O_m partition S_m by u-parity. Let M_tot, M_par be the total and parity blocks of the carry matrix M_aug. If:
   (i) Every zeroless residue has a unique digit representation (trivially true),
   (ii) The carry chain is memoryless (Dobrushin coefficient = 0, verified Exp 2),
   (iii) The orbit visits each residue exactly once per period,
   then |E_m - O_m| / Z_m = O(theta^m) where theta = rho(M_par)/rho(M_tot).

   Is this correct? Are conditions (i)-(iii) sufficient? Is (ii) actually needed, or does (i) alone suffice?

---

## Prompt E2: The Carry-0 Exact Balance, the 4/9 Phenomenon, and the Correct Orbit Operator

The independent verification of the D-series matrices uncovered two striking structural facts:

**Fact A (Carry-0 exact balance)**: At every level m = 1..9, among survivors with carry-out = 0, E = O exactly. All E - O imbalance comes from carry-1 survivors.

**Fact B (Orbit carry fraction = 4/9)**: Among orbit survivors at every level, exactly 4/9 have carry-out = 0 and 5/9 have carry-out = 1. This differs from the PF equilibrium of M_tot, which is ~0.469 (close to 4/9 but not equal).

**Fact C (Non-Markov transition)**: The empirical (carry, u-parity) transition matrix changes with level m. The state (carry, u mod 2) is not a sufficient Markov statistic for the orbit fiber extension.

These facts constrain any proof of the strong lemma. This prompt asks for their explanation and implications.

**Questions:**

1. **Prove Fact A from structure.** The carry-0 condition means: the doubling 2*d_m + c_m gives a result < 10 (no carry generated). Consider the digit values d such that 2d + c < 10 and 2d + c != 0. For c = 0: d in {1,2,3,4} (digits giving 2d in {2,4,6,8}, all < 10 and nonzero). So carry-0 with carry-in = 0 always gives even output digits {2,4,6,8}. For c = 1: d in {1,2,3,4} gives 2d+1 in {3,5,7,9}, all odd.

   How does this digit structure interact with u-parity to produce exact E = O among carry-0 survivors? The key is likely: carry-0 survivors have digits constrained to {1,2,3,4} regardless of carry-in, and this constraint is parity-neutral. Prove this.

2. **Prove or explain Fact B.** The PF equilibrium of M_tot = [[4,4],[4,5]] is the eigenvector (4, 4+sqrt(65)-9)/... Numerically the PF right eigenvector is proportional to (1, (sqrt(65)-1)/8) ~ (1, 0.882), giving carry-0 fraction ~ 1/(1+0.882) = 0.531 ... wait, that would be carry-0 fraction 0.531. But the orbit has carry-0 fraction 4/9 = 0.444. So the orbit has LESS carry-0 than the PF equilibrium. Why?

   The orbit fiber formula gives Z_{m+1} = 4E_m + 5O_m. Among even parents, each produces 4 children. Among odd parents, each produces 5 children. The carry distribution of the CHILDREN depends on the digit values of the parent. Since odd parents (u odd) have all odd digits and even parents (u even) have all even digits (this is the within-parity digit uniformity result), the carry distribution of children might be computable from the digit distribution within each parity class.

   Is 4/9 a consequence of the orbit fiber structure rather than the generic pair-constraint? Compute the carry-0 fraction from the fiber formula and compare.

3. **What IS the correct Markov state space for the orbit?** The D3-Thinking #2 response proposed an 8-state system with states (carry c, parity-type tau, v_0-parity sigma). Is this sufficient? The 5-adic parametrization gives u = x/2^m, and the parity of u depends on all digits of x. But the carry chain propagates local information. Can the correct state space be identified by asking: what information about x mod 10^m is needed to determine both (a) the carry into digit position m+1 and (b) the u-parity of x?

   Carry c_{m+1} is determined by d_m and c_m (local, 2 states). The u-parity is u mod 2 = (x/2^m) mod 2 = (x mod 2^{m+1})/2^m. Since x = 2^m * u, x mod 2^{m+1} = 2^m * (u mod 2). So u mod 2 is determined by floor(x / 2^m) mod 2, which involves the digit representation globally.

   But perhaps there's a LOCAL characterization. Consider: u = x * 2^{-m} mod 5^m. Since 2^{-1} mod 5 = 3, we have 2^{-m} mod 5^m = 3^m mod 5^m. So u = x * 3^m mod 5^m. The parity of u = (x * 3^m mod 5^m) mod 2. This is NOT a local digit property.

   Given this, is the orbit fiber extension fundamentally non-Markov in any finite-state carry space? Or does a refinement to u mod 4, u mod 8, etc., eventually close?

4. **The hierarchy question.** The D1-Thinking response identified a 2-adic hierarchy: e_m depends on p_m (u-parity balance among odd survivors), which depends on the mod-4 balance, which depends on mod-8, etc. Does this hierarchy ever close? Specifically: let pi_k(m) be the fraction of survivors with u = 1 mod 2^k among those with u = 1 mod 2^{k-1}. Is there a k_0 such that pi_{k_0}(m) = 1/2 exactly for structural reasons?

   If the hierarchy closes at some finite k, the 2^{k+1}-state transfer operator is exact, and the strong lemma reduces to its spectral analysis. If it never closes, a different approach is needed.

5. **Can the strong lemma be proved using ONLY Fact A (carry-0 exact balance) and the known recurrence?** Since all parity imbalance is in carry-1, and the carry-1 fraction is 5/9, we have:
   Delta_{m+1} = E_{m+1} - O_{m+1} = 0 + Delta_1^{carry-1}
   where Delta_1^{carry-1} is the E - O imbalance among carry-1 survivors. Can we bound this using the M_par matrix restricted to carry-1?

6. **Design an experiment to resolve Fact C.** What is the minimal level m at which the (carry, u-parity) transition matrix visibly changes? Propose a computational test that would determine the minimal Markov state space: try (carry, u mod 4) [8 states], (carry, u mod 8) [16 states], etc., and check which gives a constant transition matrix.

---

## Prompt E3: Complete Proof of the Strong Parity-Balance Lemma

This prompt asks for a complete, self-contained proof that |e_m - 1/2| = O(theta^m) where theta = 2*sqrt(6)/(9+sqrt(65)) = 0.287. This is the "strong parity-balance lemma."

**What is proved**: Density zero follows from the WEAK lemma e_m in [2/5, 3/5], which is proved unconditionally. The STRONG lemma is a quantitative refinement giving exponential convergence to 1/2. It would sharpen the survival bound from S_m <= 23/25 to S_m = 9/10 + O(0.287^m).

**Available ingredients**:

(A) **Exact identities**:
- Z_{m+1} = 4*E_m + 5*O_m (Lemma 1, proved)
- e_{m+1} = (2 + p_m(1-e_m)) / (5 - e_m) (derived from Lemma 1 + Lemmas 2-3)
- e_{m+1} - 1/2 = (p_m - 1/2)(1 - e_m) / (5 - e_m) (bias identity, proved)

(B) **The self-correction structure**:
- Even parents produce exactly 2 even + 2 odd children (proved)
- Odd parents produce (2+p_m) even + (3-p_m) odd children on average
- The contraction factor (1-e_m)/(5-e_m) ~ 1/9 at the fixed point e = 1/2

(C) **The spectral data**:
- Carry matrix M_tot = [[4,4],[4,5]], PF = (9+sqrt(65))/2 ~ 8.531
- Parity block M_par, char poly lambda^2 - 3*lambda + 6 = 0, modulus sqrt(6) ~ 2.449
- theta = rho(M_par)/rho(M_tot) = 0.28712, matching data

(D) **Structural facts from verification**:
- The carry matrix describes the pair constraint, not the exact orbit transfer
- The orbit carry distribution is 4/9, not PF equilibrium
- Carry-0 survivors have E = O exactly (all imbalance is in carry-1)
- The per-level transition is not Markov for (carry, u-parity)

(E) **The orbit structure**:
- The orbit 2^n mod 10^m is cyclic of order T_m = 4*5^{m-1}
- It visits each residue in the coset 2^m * (Z/5^m Z)* exactly once per period
- Carry memorylessness: Dobrushin coefficient = 0 for the carry chain (Experiment 2)
- Within-parity digit uniformity is proved

(F) **Key references**:
- Noda (arXiv:2510.18414): Transfer operator framework, Lemma 1 contains fiber structure
- Banks-Conflitti-Shparlinski (2002): Character sums over digit-restricted sets via transfer matrices
- Lagarias (math/0512006): Dynamical framework for ternary digits of powers of 2

**The challenge**: The proof must bridge from the pair-constraint spectral gap (ingredients B, C) to the orbit's parity balance (ingredient A). The direct matrix iteration v_{m+1} = M_aug * v_m overcounts by ~1.9x, so it cannot be applied naively. The proof must either:

(i) Show that the 1.9x overcount cancels in the parity RATIO (the "transfer argument"), or
(ii) Build the correct orbit transfer operator and prove its spectral gap directly, or
(iii) Use a non-matrix argument (e.g., induction on the bias identity with control of p_m).

**Task**: Write a complete proof of the strong parity-balance lemma. State the theorem precisely, list all lemmas needed, prove each one, and assemble the argument. If a gap remains, state it explicitly and explain what would close it.

Specific sub-questions if a complete proof is not possible:

1. For approach (i): The even-type overcount factor is exactly 2 (8 carry transitions / 4 orbit children) and the odd-type factor is exactly 9/5 (9 carry transitions / 5 orbit children). The parity ratio among pair-constraint strings at level m is E_pair/Z_pair = 1/2 + C*theta^m. The orbit ratio is E_orbit/Z_orbit = (E_pair/2) / (E_pair/2 + O_pair * 5/9) ... work this out. Does the factor difference introduce a correction that is O(theta^m) or larger?

2. For approach (ii): The correct orbit operator acts on the survivor set, not on digit strings. At level m, the survivor set S_m consists of residues x mod 10^m with all digits nonzero. The fiber map sends x to {x + a*10^m : a = 0,...,9} intersected with S_{m+1}. The state of x is (carry-out of x, u-parity of x). We KNOW this is not exactly Markov, but the deviation from Markov decreases with m (the empirical transition matrix stabilizes). Can you prove that the deviation is O(theta^m), making the Markov approximation accurate enough for the spectral gap argument?

3. For approach (iii): The bias identity says e_{m+1} - 1/2 = (p_m - 1/2) * g(e_m) where g(e) = (1-e)/(5-e) ~ 1/9. If |p_m - 1/2| <= C * theta^m, then |e_{m+1} - 1/2| <= C * theta^m / 9 <= C * theta^{m+1} (since 1/9 < theta = 0.287). So it suffices to prove |p_m - 1/2| = O(theta^m). But p_m is the even-v_0 fraction among odd-type survivors, which is itself a parity-balance statement at the next level of the 2-adic hierarchy. Can you prove the full hierarchy closes, or that each level of the hierarchy has a contraction factor that gives geometric decay?

4. The carry-0 exact balance (Fact A from E2) means that only carry-1 survivors contribute to E - O. Since 5/9 of survivors have carry-1, Delta_{m+1} = Delta_{m+1}^{carry=1}. The carry-1 parity block of M_aug has specific eigenvalues. Can you use this to get a tighter bound on the decay of Delta_m?

---

## Prompt E4: The Bijection Between Digit Strings and Orbit Residues

This prompt isolates the most concrete sub-question of the transfer argument: the relationship between zeroless digit strings (counted by the carry matrix) and orbit residues (counted by the fiber formula).

**Setup**: An m-digit string (d_1, d_2, ..., d_m) with all d_i in {1,...,9} and satisfying the carry chain 2*d_i + c_i = 10*c_{i+1} + d_{i+1}' (where d_{i+1}' is the output digit) represents a residue x mod 10^m via x = sum d_i * 10^{i-1}.

Wait: the carry matrix doesn't directly encode a bijection this way. Let me re-state.

**The carry matrix counts TRANSITIONS**: For carry-in c and next digit d in {1,...,9}:
- Output digit: d' = (2d + c) mod 10
- Carry-out: c' = floor((2d + c) / 10)
- Zeroless filter: d' != 0

So M_tot[c', c] = #{d in {1,...,9} : (2d+c) mod 10 != 0, floor((2d+c)/10) = c'}.

This counts the number of ways to EXTEND a carry chain by one digit while maintaining the zeroless property of 2x. The PF eigenvalue 8.531 is the growth rate of admissible carry-chain paths of length m.

**The orbit fiber formula counts CHILDREN**: Each level-m survivor x has exactly 5 lifts x + a*10^m for a in {0,...,4} (since T_{m+1}/T_m = 5). Among these, even-type parents lose 1 lift (the one with digit 0) giving 4 children, and odd-type parents lose 0 giving 5 children.

**Questions:**

1. An m-digit admissible carry-chain path (c_0, d_1, c_1, d_2, c_2, ..., d_m, c_m) with initial carry c_0 = 0 encodes a number x with specific digits. Does this x lie in the orbit of 2^n mod 10^m? In other words: every orbit element has a unique carry-chain path, but does every admissible carry-chain path correspond to an orbit element?

   If NOT (i.e., the carry matrix overcounts), explain the multiplicity. How many carry-chain paths correspond to the same orbit element? Is this the source of the 1.9x factor?

2. The orbit consists of T_m = 4*5^{m-1} elements. The number of admissible carry paths of length m starting from c_0 = 0 should be approximately PF^m * v_0 where v_0 is the PF eigenvector's c=0 component. For m=1: paths are (c=0, d, c') with d in {1,...,9} and (2d) mod 10 != 0. Valid d values: 1,2,3,4,6,7,8,9 (d=5 gives 10, carry 1, digit 0 -- excluded). Wait, d=5 gives 2*5+0=10, digit 0, carry 1. So 8 valid paths at m=1. The orbit has Z_1 = 4 survivors at m=1. Ratio: 8/4 = 2.

   At m=2: the number of carry paths should be around 8.531 * 8 ~ 68. The orbit has Z_2 = 18. Ratio: 68/18 = 3.8. But the reported ratio was ~1.9 at all levels. I may be confusing the counting. Clarify: what exactly does the carry matrix count, and what is the exact relationship to the orbit survivor count Z_m?

3. The parity-augmented matrix M_aug assigns each carry-chain transition a parity label (E or O). Under the bijection/correspondence between paths and orbit elements, does the parity label of the path match the u-parity of the orbit element? If so, the spectral gap of M_par directly gives the parity decay for orbit elements. If not, what is the relationship?

4. A cleaner formulation might avoid carry chains entirely. The survivor set S_m = {x in Z/10^m Z : all digits of x nonzero, x = 0 mod 2^m, gcd(x, 5) = 1}. The partition S_m = S_m^E union S_m^O is by u-parity, where u = x * 3^m mod 5^m (since 2^{-1} = 3 mod 5). The question |S_m^E - S_m^O| / |S_m| -> 0 is a character sum: sum_{x in S_m} (-1)^{x * 3^m mod 5^m mod 2} / |S_m|. Can this character sum be bounded using the Banks-Conflitti-Shparlinski framework directly, without going through carry matrices?

5. An alternative approach: the function u = x * 2^{-m} mod 5^m maps S_m bijectively to U_m = {u in (Z/5^m Z)* : all digits of 2^m * u mod 10^m are nonzero}. The digit constraint on 2^m * u is: for each position i = 1,...,m, the i-th digit of 2^m * u (mod 10^m) is nonzero. Each digit is a function of u mod 5^i and a carry from lower digits. The character sum is sum_{u in U_m} (-1)^u / |U_m|.

   This is a character sum of the simplest character (-1)^u over a set U_m defined by m independent digit constraints. Each constraint is a "forbidden residue class" at level i. The "transfer matrix" for this sum is exactly M_par. Can you make this precise?
