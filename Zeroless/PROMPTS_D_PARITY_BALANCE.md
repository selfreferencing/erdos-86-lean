# D-Series Prompts: Proving the Parity-Balance Lemma

## Context for all prompts

These prompts build on 46 prior AI responses (16 metaprompt, 10 A-series on equidistribution, 8 B-series on transfer matrices, 6 C-series on information theory) and 11 computational experiments. The D-series targets the ONE remaining lemma identified by the C-series, now with a corrected and simplified formulation validated by Experiment 11.

**Problem**: 2^86 is the last power of 2 with no digit 0 in base 10. We seek a proof of density zero: #{n <= N : 2^n is zeroless} = o(N).

**The reduction (C-series + Experiment 11)**: Density zero follows from a single parity-balance lemma about the survivor set. The C-series identified this reduction; Experiment 11 discovered a classification error in the C-series, corrected it, and confirmed the corrected framework exactly through m=12.

**The corrected framework (all identities verified exactly)**:

At each digit level m, the orbit of 2^n mod 10^m has period T_m = 4*5^{m-1}. The orbit elements are x = 2^m * u where u is the "5-adic parameter," u in (Z/5^m Z)* (units mod 5^m). An orbit element x is a "survivor at level m" if all m trailing digits of x are nonzero.

The 5 lifts of a level-m survivor to level m+1 have a fixed digit parity determined by the parity of u:

- **Even-type** (u even): lifts produce digits {0, 2, 4, 6, 8}. One lift is killed (digit 0). **4 survivors.**
- **Odd-type** (u odd): lifts produce digits {1, 3, 5, 7, 9}. None killed. **5 survivors.**

Derivation: The base lift parameter is v_0 = u * 2^{-1} mod 5^m. If u is even, v_0 = u/2 < 5^m/2, giving even digits. If u is odd, v_0 = (u + 5^m)/2 >= 5^m/2, giving odd digits.

**Exact identities (verified through m=11)**:

- Z_{m+1} = 4*E_m + 5*O_m (exact at every level tested)
- S_{m+1} = Z_{m+1} / (5*Z_m) = 1 - E_m / (5*Z_m)
- S_m = 0.9 iff E_m/Z_m = 1/2

where E_m = #{even-type survivors at level m}, O_m = #{odd-type survivors}, Z_m = E_m + O_m.

**Experiment 11 data (corrected classification: even-type iff u is even)**:

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

Fitted decay: |E/Z - 1/2| ~ 0.26 * (0.29)^m, theta ~ 0.29.

E - O sequence: [0, 0, +1, 0, 0, -1, -6, +10, +3, -13, +19, -5]

Note: m = 1, 2, 4, 5 have E/Z = 1/2 exactly (zero bias).

**Structural finding from Experiment 11 (proved, not just observed)**:

Even-type parents (u even) produce children with an exact 50/50 parity split. The 4 surviving lifts have parameters v_0 + a*5^m for a in {1,2,3,4} (a=0 killed by digit 0). Since 5^m is odd, adding a*5^m alternates the parity of v_0: exactly 2 children are even-type, 2 are odd-type.

Odd-type parents produce children with a 3:2 or 2:3 split depending on v_0's parity, averaging to 5/2 : 5/2 when v_0's parity is balanced (which it is by the same mechanism at the previous level).

This creates inherently self-correcting dynamics: even if E != O at some level, the even-parent 50/50 split pushes the ratio back toward 1/2.

**Prior results from A/B/C series**:

- The orbit is a cyclic group of order T_m = 4*5^{m-1} in the coset {x : 2^m | x, gcd(x,5) = 1}
- Transfer matrix for m-fold constraints has spectral radius rho(m) decreasing from 9 (m=1) to 3.41 (m=18)
- The orbit branching factor beta(m) = rho(m)/2 predicts beta = 1 crossing at m ~ 27
- Within-parity digit uniformity is proved (one-page proof)
- Density zero follows from proving E_m/Z_m >= delta > 0 for any fixed delta

---

## Prompt D1: The Self-Correction Mechanism and a Proof of the Weak Parity Lemma

The parity-balance dynamics have a proved self-correction mechanism. Can it be made into a rigorous proof?

**The dynamics**: Define the parity fractions e_m = E_m/Z_m and o_m = O_m/Z_m = 1 - e_m. From the exact identity Z_{m+1} = 4*E_m + 5*O_m and the transition statistics:

**From even parents** (proved exactly):
- 4 children, split exactly 2 even + 2 odd
- Contribution to E_{m+1}: 2*E_m
- Contribution to O_{m+1}: 2*E_m

**From odd parents** (approximate, depends on secondary balance):
- 5 children. If v_0 of the parent is even: 3 even + 2 odd children. If v_0 is odd: 2 even + 3 odd.
- Let p_m = fraction of odd-type parents with even v_0. Then:
  - Contribution to E_{m+1}: (3*p_m + 2*(1-p_m)) * O_m = (2 + p_m) * O_m
  - Contribution to O_{m+1}: (2*p_m + 3*(1-p_m)) * O_m = (3 - p_m) * O_m

So:
- E_{m+1} = 2*E_m + (2 + p_m)*O_m
- O_{m+1} = 2*E_m + (3 - p_m)*O_m
- Z_{m+1} = 4*E_m + 5*O_m (check: independent of p_m)

The ratio:
e_{m+1} = E_{m+1}/Z_{m+1} = [2*E_m + (2+p_m)*O_m] / [4*E_m + 5*O_m]

If e_m = 1/2 and p_m = 1/2, then e_{m+1} = [1 + (2.5)*1] / [2 + 5*1] = not quite right since we need to use actual counts...

Let me state it differently. With E_m = e*Z_m and O_m = (1-e)*Z_m:

e_{m+1} = [2e + (2+p)(1-e)] / [4e + 5(1-e)] = [2 + p - pe] / [5 - e]

At the fixed point e = 1/2, p = 1/2:
e_{m+1} = [2 + 0.5 - 0.25] / [5 - 0.5] = 2.25 / 4.5 = 1/2. Consistent.

**Questions:**

1. The even-parent 50/50 split is proved. For odd parents, p_m (fraction with even v_0) is itself a parity balance at a different level. Can you set up a coupled recurrence for (e_m, p_m) and prove it has a unique stable fixed point at (1/2, 1/2)? What are the eigenvalues of the linearized system?

2. Even without knowing p_m, can the weak lemma be proved? Suppose we only know 0 <= p_m <= 1. Then:
   e_{m+1} = [2 + p_m - p_m*e_m] / [5 - e_m]
   What is the range of e_{m+1} as p_m varies over [0,1], for a given e_m? In particular: if e_m >= delta, is e_{m+1} >= delta' for some delta' > 0 independent of p_m? This would give the weak lemma by induction.

3. The data shows E/Z = 1/2 EXACTLY at m = 1, 2, 4, 5. At m=3, E/Z = 41/81 (one extra even-type). Why is the balance exact at these levels? Is there a symmetry of the survivor set at these specific m values?

4. The fitted theta ~ 0.29 means the parity bias decays as ~(0.29)^m. Does the linearized recurrence predict this rate? If the Jacobian at the fixed point (1/2, 1/2) has spectral radius 0.29, that would explain the data and prove the strong parity-balance lemma.

5. The key structural fact: the map u -> u * 2^{-1} mod 5^m is an automorphism of (Z/5^m Z)*. The survivor set Z_m is a subset of this group. Even-type = {u : u even} is exactly the kernel of the mod-2 character chi(u) = (-1)^u. The parity-balance lemma says this character has small average over the survivor set. Can you formulate the lemma as: the Fourier coefficient of the survivor indicator at the mod-2 character decays geometrically?

---

## Prompt D2: The Parity-Augmented Transfer Operator

The C-series and Experiment 11 reduce density zero to a spectral gap statement about a transfer operator that tracks both carry state and parity type. This prompt asks for the explicit construction and analysis.

**Setup**: At each digit position, the carry state c in {0,1} and the parity type tau in {E, O} evolve together. The combined state is (c, tau) in {0,1} x {E,O}, giving a 4-state system.

The digit-extension process: given a level-m survivor with carry c and parity type tau (determined by u mod 2), we extend to level m+1 by choosing the new digit d. The carry and parity of the child are determined by the specific lift.

**From the fiber structure**:

An even-type parent (u even, tau = E) has 4 surviving lifts. The child parameters are v_0 + a*5^m for a = 1,2,3,4 where v_0 = u/2. Each lift has:
- A specific digit d = floor(2*(v_0 + a*5^m) / 5^m) mod 10
- A carry into the NEXT digit position (from the doubling 2*digit + carry)
- A parity type for the child: even if (v_0 + a*5^m) is even, odd otherwise

Since v_0 = u/2 and 5^m is odd: v_0 + a*5^m has parity (parity of u/2) XOR (parity of a). For a = 1,2,3,4: a is odd for a=1,3 and even for a=2,4. So exactly 2 children match v_0's parity and 2 flip it.

Similarly for odd-type parents: all 5 lifts survive (a = 0,1,2,3,4), with 3 matching and 2 flipping v_0's parity (or vice versa).

**The carry transition**: When doubling x = 2^m * u to get 2x = 2^{m+1} * v, the carry at digit position m+1 depends on the digit d_m and the incoming carry c_m:
- t = 2*d_m + c_m
- c_{m+1} = floor(t / 10)

So the carry transition depends on the specific digit, which depends on the lift parameter a.

**Questions:**

1. Construct the explicit 4x4 transfer matrix M_{aug} with states (c, tau) in {0,1} x {E, O}, ordered as (0,E), (0,O), (1,E), (1,O). Each entry M_{aug}[i,j] counts the number of valid lifts from state j to state i. Compute this matrix and its eigenvalues.

2. The Perron-Frobenius eigenvalue of M_{aug} should equal the leading eigenvalue of the standard 2x2 carry matrix (since the total count Z_{m+1} doesn't depend on the parity decomposition). What is the SECOND eigenvalue? If it governs the parity bias, its ratio to the leading eigenvalue should be theta ~ 0.29.

3. More precisely: decompose M_{aug} into a "total" part (projecting onto the (1,1) parity direction) and a "parity" part (projecting onto the (1,-1) direction). The total part should reproduce the 2x2 matrix [[4,4],[4,5]] with rho ~ 8.531. The parity part should have spectral radius rho_parity < rho. What is rho_parity, and is rho_parity / rho ~ 0.29?

4. If the spectral gap exists: the parity bias decays as (rho_parity / rho)^m. Combined with the proved identity Z_{m+1} = 4*E_m + 5*O_m, this gives:
   S_m = 0.9 + O((rho_parity/rho)^m)
   And density zero follows because the survivor density decays as (0.9 + epsilon)^k -> 0.
   Write out this argument explicitly. What are the constants?

5. There is a subtlety: the transfer matrix counts GENERIC digit strings, not the specific orbit. The orbit's behavior matches the transfer matrix prediction because the orbit samples all residues mod 10^m. But is there a rigorous way to pass from the matrix spectral gap to the orbit's parity balance? The orbit visits each residue exactly once per period, so the parity count along the orbit equals the count over ALL residues. Does this mean the matrix spectral gap directly implies the orbit parity balance?

6. Alternatively: can the 4x4 matrix be derived directly from the orbit structure (the cyclic group Z/T_m Z acting by multiplication by 2) rather than from the digit-extension process? This would bypass the orbit-vs-random issue entirely.

---

## Prompt D3: Three Routes to Proving the Lemma

The parity-balance lemma |E_m/Z_m - 1/2| -> 0 has been verified computationally to m=12 with theta ~ 0.29. Three proof routes have been identified. This prompt asks for the most promising approach and a concrete outline.

**Route 1: Self-Correction (Inductive)**

The even-parent 50/50 split is proved. The odd-parent split depends on a secondary quantity p_m (fraction of odd parents with even v_0). If one could show p_m -> 1/2 (which is itself a parity-balance statement at a different level), the main balance follows.

The recursive structure: p_m is related to the parity of v_0 among odd-type survivors. Since v_0 = (u + 5^m)/2 for u odd, the parity of v_0 depends on u mod 4. So p_m = fraction of odd-type survivors u with u = 1 mod 4 (vs u = 3 mod 4). This is a "mod-4 balance" among odd survivors.

Is there a hierarchy of balance conditions (mod 2, mod 4, mod 8, ...) each implied by the next, with a base case? Or does the hierarchy close at some finite level?

**Route 2: Spectral Gap (Operator-Theoretic)**

Build the parity-augmented transfer operator (see D2) and prove a spectral gap. This is the Noda approach: his transfer-operator formalism (arXiv:2510.18414, Lemma 1) already tracks digit-weighted functions. Adding parity tracking doubles the state space. If the resulting operator has a gap, the lemma follows.

Key question: does Noda's framework already handle this, or does the parity augmentation require new analysis?

**Route 3: Character Sum / Fourier (Algebraic)**

The parity type is chi(u) = (-1)^u, a multiplicative character on (Z/5^m Z)*. The parity balance is:

|sum_{u in survivors} chi(u)| / |survivors| -> 0

This is a character sum over a combinatorially defined subset of (Z/5^m Z)*. The survivor set is defined by: the base-10 digits of r(u) = 2^m * u mod 10^m are all nonzero.

The digit constraint is "additive" (it depends on base-10 representation) while chi is "multiplicative" (it depends on u mod 2). The misalignment between additive and multiplicative structure is exactly what should produce cancellation.

Can this be proved using sum-product estimates, or the Weil bound for character sums over algebraically defined sets?

**Questions:**

1. Rank these three routes by feasibility. Which is closest to a complete proof? Which requires the least new machinery?

2. For Route 1: Set up the coupled recurrence for (e_m, p_m) explicitly, linearize at (1/2, 1/2), compute eigenvalues. If both eigenvalues have magnitude < 1, the strong lemma follows. Does the data (theta ~ 0.29) match the predicted eigenvalue?

3. For Route 2: The transfer matrix for the single-doubling constraint has dimension 2 (carry states). The parity augmentation doubles it to 4. But can the parity degree of freedom be separated cleanly? If M_{aug} = M_total (x) I_parity + M_cross, what is M_cross and what controls its spectral radius?

4. For Route 3: The character chi(u) = (-1)^u is a character of order 2 on (Z/5^m Z)*. It factors as the composition (Z/5^m Z)* -> (Z/5^m Z)* / ker(chi) -> {+/- 1}. The kernel of chi is the subgroup of even units, which has index 2. The survivor set is a subset of (Z/5^m Z)*. The sum sum_{u in S} chi(u) = #(S intersect even units) - #(S intersect odd units) = E_m - O_m. Bounding this sum requires understanding the distribution of S relative to the even/odd cosets. What is known about character sums over digit-constrained sets?

5. Is there a proof that combines Routes 1 and 2? The self-correction mechanism (Route 1) could provide the qualitative structure (the fixed point is stable), while the spectral gap (Route 2) could provide the quantitative rate.

6. What is the simplest self-contained proof of the WEAK lemma E_m/Z_m >= 0.01? This is all that's needed for density zero. Can it be proved in one page?

7. Three relevant papers:
   - Noda (arXiv:2510.18414): Transfer-operator for digit-weighted generating functions of 2^n
   - Lagarias (math/0512006): Ternary digits of 2^n, dynamical framework
   - Dumitru (arXiv:2503.23177): Metric finiteness for "all digits even" via Borel-Cantelli

   Given the corrected framework and the self-correction mechanism, does any of these three contain the ingredients for a proof of the parity-balance lemma? What would need to be added?
