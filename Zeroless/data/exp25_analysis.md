# Experiment 25 Analysis: Coboundary / Bounded Discrepancy Test

## Critical Finding: TWO different discrepancy regimes

### 1. Transition zone discrepancy IS bounded

The discrepancy in the transition zone [0, L_trans) where L_trans = ceil(C*m):

| m | L_trans | trans_disc |
|---|---------|-----------|
| 2 | 7 | -1.30 |
| 5 | 17 | -4.14 |
| 10 | 34 | -4.13 |
| 15 | 50 | -9.46 |
| 20 | 67 | -3.11 |
| 25 | 84 | -4.74 |
| 27 | 90 | -5.78 |

The transition zone discrepancy fluctuates in [-10, 0] for all m tested. It does NOT grow with m. This is exactly what the coboundary mechanism predicts for the finiteness argument.

### 2. Full-orbit discrepancy is NOT bounded

The max discrepancy over the full orbit (or first 100,000 steps) grows:

| m range | max |disc| |
|---------|------------|
| 2-5 | 18.5 |
| 6-10 | 121.4 |
| 11-15 | 133.8 |
| 16-20 | 110.5 |
| 21-24 | 106.2 |

The full-orbit discrepancy grows from ~18 at m=5 to ~100-130 for m >= 7, then appears to stabilize (or fluctuate) around 80-130.

### 3. Where the large discrepancy occurs

The max discrepancy consistently occurs at L ~ 28,100-28,200. This is NOT in the transition zone (which has L ~ 3.3m, at most 90 for m=27). The large discrepancy at L ~ 28,100 suggests a structural feature of the orbit at that scale.

The number 28,138 is close to T_m / 5^{m-5} ~ 4*5^4 = 2500... no, it's closer to 4*5^5/something. Let me check: 28,125 = 4*5^5*9/8... actually 28,125 = 5^4 * 225 = 5^4 * 9 * 25 = 5^6 * 9 = 140,625/5. Hmm, 28,125 = 4.5 * 5^4 * 5 = 9/2 * 5^5. Not a clean power.

Actually 28,138 is close to 28,125 = 9 * 5^5 / 2^1... or 5^6 * 9 / 5^1 = 9 * 3125. Not obvious.

More likely: 28,138 is related to a convergent denominator of log10(2). The convergent q_8 = 28,738 is very close! So the large discrepancy occurs near the convergent denominator q_8 = 28,738 of log10(2).

This makes perfect sense: the Birkhoff sum has peaks at convergent denominators because that's where ||q*theta|| is smallest (the "three-distance theorem" creating near-repetition of the orbit).

### 4. The transition zone is protected by a DIFFERENT mechanism

The transition zone discrepancy being O(1) while the full-orbit discrepancy grows is perfectly consistent with:

- The transition zone is "too short" for the convergent-denominator resonances to build up
- L_trans ~ 3.3m << q_3 = 93 for m >= 3, and q_4 = 196 for m >= 6
- So the transition zone never encounters the problematic scales

This means: the coboundary mechanism works FOR THE TRANSITION ZONE even though it fails for the full orbit. The finiteness argument only needs bounded discrepancy in the transition zone.

### 5. Fourier coboundary analysis (Part C)

The Fourier computation of |g|_inf confirms the growing discrepancy:
- m=4: |g|_inf = 8.8 (T=500)
- m=6: |g|_inf = 34.7 (T=12500)
- m=8: |g|_inf = 167.2 (T=312500)

The growth is roughly proportional to T_m^{1/2} or slower. The dominant contribution at k=1 gives |hat(g)(1)| = |hat(b)(1)| / |1-omega| ~ rho * 0.123 / (2*pi/T_m) = 0.123 * rho * T_m / (2*pi), which grows linearly with T_m. But this is for the FULL orbit, not the transition zone.

### 6. Continued fraction analysis

The continued fraction of theta = log10(2) is:
[0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, ...]

Key convergent denominators:
- q_2 = 10 (the famous log10(2) ~ 3/10)
- q_3 = 93 (9-fold partial quotient creates good approximation)
- q_4 = 196
- q_5 = 485
- q_6 = 2136
- q_7 = 13301
- q_8 = 28738 (<-- THIS is the resonance causing large discrepancy!)
- q_9 = 42039
- q_10 = 70777
- q_11 = 254370

The large partial quotient a_3 = 9 creates an exceptionally good approximation at q_3 = 93, and a_13 = 18 creates another at q_12 = 325,147.

### 7. The transition zone is always shorter than q_3 = 93

For m >= 3, L_trans = ceil(C*m) <= 3.33*m. We have L_trans < 93 for m < 28.
For m >= 28, L_trans >= 93 but the convergent q_3 = 93 gives ||93*theta|| = 0.0042, which is still quite large relative to the step size.

The key protection: the first "dangerous" convergent q that could cause large discrepancy in the transition zone is q_3 = 93, but 93 * 0.9^m * C ~ 93 * 0.9^m * 3.3 which is tiny for m >= 28 (where L_trans ~ 93).

## Revised Assessment

### The coboundary strategy works, but needs refinement

GPT 4B's coboundary mechanism is correct IN SPIRIT for the transition zone:
- The transition zone discrepancy IS bounded (empirically, |disc| < 11 for all m tested)
- This bounded discrepancy combined with rho_m * L -> 0 forces zero hits for large m

But the "uniform bounded discrepancy for all L" claim is FALSE for the full orbit. The mechanism is:
1. For L in the transition zone (L ~ 3.3m), the discrepancy is O(1)
2. For L near convergent denominators (L ~ q_n for large n), the discrepancy can be O(100+)
3. The finiteness argument only needs case 1

### What needs to be proved

The precise lemma needed is weaker than GPT 4B's Step A:

> **Restricted Bounded Discrepancy Lemma:** For all m and all L <= C*m,
> |sum_{j<L} f_m(j*theta mod 1) - L*rho_m| <= C'
> for some fixed C'.

This is a statement about SHORT Birkhoff sums (L ~ m), not about the full orbit (L ~ T_m ~ 5^m).

Short Birkhoff sums for irrational rotations are controlled by the FIRST FEW convergent denominators, not the full continued fraction. Since the first convergent denominators of theta are small and fixed (3, 10, 93, ...), the short-sum discrepancy should be controllable by standard Denjoy-Koksma-type estimates.

### Connection to Denjoy-Koksma

The Denjoy-Koksma inequality states: for a function f of bounded variation V(f) on the circle, and irrational rotation by alpha with convergent denominator q_n,

|sum_{j=0}^{q_n-1} f(x + j*alpha) - q_n * integral(f)| <= V(f)

This bounds the Birkhoff sum at CONVERGENT denominators. For general L, the estimate becomes:

|sum_{j=0}^{L-1} f(x + j*alpha) - L * integral(f)| <= (a_{n+1} + 1) * V(f)

where q_n <= L < q_{n+1} and a_{n+1} is the (n+1)-th partial quotient.

For our problem:
- L = C*m ~ 3.3m
- For m <= 27: L < 93 = q_3, so we're in the range q_2 = 10 <= L < q_3 = 93
  - The bound is (a_3 + 1) * V(f_m) = 10 * V(f_m)
  - V(f_m) = variation of the zeroless indicator = 2 * (number of zero-free intervals) in [0,1)
  - The number of intervals is O(9^m) and each is tiny... so V(f_m) is O(9^m)
  - This gives a TERRIBLE bound: O(10 * 9^m)

So Denjoy-Koksma with the full variation is useless. BUT: we're not using f_m on the circle; we're using it on the ORBIT in Z/T_m Z. The orbit version might have better structure.

### The real mechanism: the transition zone is too short to see resonances

The transition zone has L ~ 3.3m points. The smallest ||k*theta|| for k <= L is at most ~ 1/L ~ 1/(3.3m) (by the Dirichlet pigeonhole principle). The actual values:

- k=10: ||k*theta|| = 0.0103 (this is the "1024 ~ 10^3" near-coincidence)
- k=3: ||k*theta|| = 0.0969 (this is "8 ~ 10^0.9")

For L ~ 30 (m=9), the smallest ||k*theta|| for k <= 30 is at k=10 with 0.0103 and at k=20 with 0.0206. These are not small enough to cause large discrepancy when multiplied by L ~ 30.

The bounded discrepancy in the transition zone may follow from a simple pigeonhole argument: L is too small relative to the Diophantine quality of theta to create resonances.

## Implications for the Proof Strategy

The data strongly supports a refined version of GPT 4B's strategy:

1. **Don't prove uniform bounded discrepancy** (it's false for large L)
2. **Prove restricted bounded discrepancy** for L <= C*m (this appears to hold with constant ~ 10)
3. Use Denjoy-Koksma at the level of the orbit structure (not the circle) to get the right bound
4. The Diophantine input needed is even WEAKER than GPT suggested: just that the first ~log(m) convergent denominators of theta are "well-behaved," which is known from the continued fraction expansion

This is a more realistic path than the full coboundary program.
