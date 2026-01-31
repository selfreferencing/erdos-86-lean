# GPT Prompt 10: Deep Formalization of Dyachenko's Theorem 9.21

## Purpose

This is a MATHEMATICAL DECOMPOSITION prompt, not a code prompt. I need you to break Dyachenko's Theorem 9.21 into atomic sub-lemmas suitable for Lean 4 formalization.

## What I have already

The Erdos-Straus conjecture (4/n = 1/x + 1/y + 1/z) is fully formalized in Lean 4 EXCEPT for one sorry. That sorry asks:

**For every prime p with p >= 1,000,001 and p === 1 (mod 24), there exists A in [(p+3)/4, (3p-3)/4] and d | A^2 such that (4A-p) | (d+A).**

Equivalently (setting delta = 4A - p): find A in the window and d | A^2 with d === -A (mod delta).

### Proven Lean infrastructure

1. **WindowLattice.lean** (all proven, no sorrys):
   - `ED2KernelLattice g b' c'`: the lattice L = {(u,v) : g | u*b' + v*c'}
   - `ed2_window_lemma`: any g x g rectangle contains a point of L (when gcd(g,b') = gcd(g,c') = 1)
   - `kernel_lattice_index`: L has index g in Z^2
   - `v1_mem`: (c', -b') is in L
   - `v2_mem`: (d', d') is in L where d' = g/alpha, alpha = gcd(g, b'+c')

2. **CertificateGoodDivisor.lean** (proven by native_decide):
   - All primes p === 1 (mod 24) with p < 1,000,001 are handled computationally.

3. **ExistsGoodDivisor.lean** (proven EXCEPT the sorry at line 206):
   - Cases p === 5 (mod 8) and p === 17 (mod 24): PROVEN
   - Case p === 1 (mod 24), p < 1,000,001: PROVEN (certificate)
   - Case p === 1 (mod 24), p >= 1,000,001: SORRY <-- THIS IS IT

4. **Phase3.lean** (proven infrastructure):
   - `ed2_of_good_divisor`: converts (A, d) with divisor conditions into Type II solution
   - `ed2_dyachenko_bridge`: routes Type II to the final conjecture

5. **Appendix D lemmas** (proven in earlier prompts):
   - D.1: algebraic equivalence between product identity and sum/divisibility conditions
   - D.16: bridge from (u,v) lattice point to (alpha, d', b', c') parameters

### What previous prompts accomplished and where they stalled

- **Prompt 1**: Proved D.1 algebraic equivalence. COMPILED.
- **Prompt 2**: Proved D.16 bridge (u,v) -> parameters. COMPILED.
- **Prompt 3**: Attempted full lattice setup. STALLED at `exists_lattice_point_in_window` which was noted "FALSE as stated" with counterexample p=5, A=2, alpha=2. The issue: the lattice L depends on b' and c', but b' and c' are the OUTPUT we're trying to find. This circularity was never resolved.
- **Prompts 4-7**: Attempted alternative routes (Fermat two-squares, hyperbola-lattice intersection). All left sorrys.
- **Prompt 8**: Three GPT instances correctly diagnosed the gap but none solved it.
- **Prompt 9**: CRT/covering approach (different strategy, sent separately).

## The circularity problem (THE KEY ISSUE)

The paper's argument has a subtle structure that our formalization hasn't captured:

**Paper's flow**: Fix alpha and a candidate (b', c') pair. Define g = 4*alpha*b'*c' - P (= m, the step modulus). Define L using these b', c'. The window lemma gives a lattice point. D.33 says the discriminant is automatically a perfect square. D.16 extracts the actual b', c' from the lattice point.

**The problem**: L is defined using the b', c' we're trying to find. The window lemma gives us a DIFFERENT point in L, say (u*, v*). From (u*, v*) we extract NEW b*, c* = (u*+v*)/2, (u*-v*)/2. But now g changes (because g = 4*alpha*b*c* - P depends on b*, c*), so L changes, and the whole construction is circular.

**How the paper resolves this**: I believe the paper fixes alpha and d' first, then searches over (b', c') in the lattice defined by g = alpha * d'. The lattice is defined by g, not by b' and c'. Then:
- L = {(u,v) : g | u*b0' + v*c0'} for some FIXED basis (b0', c0')
- Window lemma gives (u,v) in L in a rectangle
- The point (u,v) with u = m*d' and u^2 - v^2 = 4M gives b' = (u+v)/2, c' = (u-v)/2
- These b', c' satisfy the identity because they're in L and on the hyperbola

But the basis (b0', c0') of L must satisfy gcd(b0', g) = gcd(c0', g) = 1 for the window lemma. And g = alpha * d' (from the lattice index theorem). So g is determined by alpha and d', NOT by b' and c'.

## What I need you to do

### Step 1: Clarify the paper's argument

Read the following transcription of key paper sections and tell me EXACTLY what the mathematical argument is, step by step. No hand-waving. For each step, identify:
- What is GIVEN (fixed/chosen)
- What is PROVED TO EXIST
- What is the logical dependency

### Step 2: Identify the correct order of quantifiers

The proof has the structure: for all p, exists alpha, exists d', exists b', exists c', [conditions]. What gets fixed when? I think the correct order is:

1. Fix p (prime, p === 1 mod 4)
2. Choose alpha (typically alpha = 1 suffices for large p)
3. Choose A in the window -- but A = alpha * b' * c', so this depends on b', c'
4. The lattice L depends on g = 4A - p = 4*alpha*b'*c' - p

This is circular. How does the paper break the circularity?

### Step 3: Decompose into atomic lemmas

Once the logical flow is clear, state each step as a self-contained mathematical lemma. For each lemma:
- State it precisely (hypotheses and conclusion)
- Say whether it's trivial, routine, or deep
- Give the proof idea

## Paper transcription (for reference)

### Theorem 9.21 (Main existence, condition III)

Consider the two-dimensional lattice
  L = {(u,v) in Z^2 : u*b' + v*c' === 0 (mod g)},
where g in N, b', c' satisfy gcd(b', g) = gcd(c', g) = 1,
and set alpha := gcd(g, b' + c'), d' := g/alpha.

### Lemma 9.22 (Kernel structure)

L is a full-rank lattice of index g, containing:
- v1 = (c', -b')
- v2 = (d', d')

The vector v2 is a diagonal period of length d' = g/alpha.

### Proposition 9.25 (Rectangle hitting)

If H >= d' and W >= d', then any H x W rectangle contains a point of L.

Proof: Choose p0 = (u0, v0) in L (e.g., v1). By division algorithm, find unique u* in [x0, x0+H) with u* === u0 (mod d') and unique v* in [y0, y0+W) with v* === v0 (mod d'). Set m = (u* - u0)/d'. Then p = p0 + m*w (where w = (d',d')) is in L, with first coordinate u* in [x0, x0+H). By Lemma 9.24, the second coordinate is in the same class mod d' as v0, hence equals v* in [y0, y0+W).

### Connection with Section 7.3

For this point to produce a solution to the ED2 problem, we use the normalization (u, v) and the inverse test (Lemmas D.33, D.16): for m = 4A - P we take u = m*d' and find v === u (mod 2) with u^2 - v^2 = 4A/alpha.

### D.33 (Sum and discriminant)

Let S = b'+c', M = b'*c', Delta = S^2 - 4M. Under normalization: S = u, Delta = v^2. In particular, Delta is ALWAYS a perfect square.

### D.16 (Necessary and sufficient conditions)

Fix alpha, P, A with m := 4A-P > 0, M := A/alpha. For integer point (u,v), the following are EQUIVALENT:
1. There exist d', b', c' with u = m*d', v = b'-c', b' = (u+v)/2, c' = (u-v)/2, and the identity holds.
2. m | u, u === v (mod 2), u^2 - v^2 = 4M.
3. There exists d' with u = m*d' and Delta := u^2 - 4M = v^2 is a perfect square.

## The specific questions I need answered

1. **Does the paper fix b', c' first and then use the lattice to find MORE solutions?** Or does it fix g and use the lattice to find the FIRST b', c'?

2. **If b', c' are the output, what are the inputs to the lattice L?** The lattice L = {(u,v) : g | u*b' + v*c'} seems to require b', c' as inputs. What breaks this circularity?

3. **Is there a version of the argument that avoids the lattice entirely?** For instance: "for A in the window, the number of d | A^2 with d === -A (mod delta) equals (number of QR-class divisors) which is positive when A has enough small prime factors, which it does when p is large enough." This would be a divisor-counting argument rather than a lattice argument.

4. **What is the SIMPLEST self-contained proof** that for all primes p === 1 (mod 24) with p >= 10^6, there exist A in [(p+3)/4, (3p-3)/4] and d | A^2 with (4A-p) | (d+A)?

## Constraints

- I need MATHEMATICAL CLARITY, not Lean code (yet).
- Every step must be logically watertight. No "it follows from density considerations" without specifying what density argument.
- If the paper's argument is genuinely circular or requires unstated additional input, say so.
- If you think a different approach (not the lattice) would be simpler, propose it with full details.
- The argument must work for ALL primes >= 10^6 in the residue class, not just "sufficiently large" primes (since our certificate handles everything below 10^6).
