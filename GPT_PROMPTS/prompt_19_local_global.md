# GPT Prompt 19: Local-Global Principles and Strong Approximation for Erdos-Straus

## Background

We are trying to prove the Erdos-Straus conjecture for primes P === 1 (mod 24). Through extensive analysis, we've reduced this to:

**For every prime P === 1 (mod 24), there exist positive integers alpha, s, r such that M := 4*alpha*s*r - 1 divides P + 4*alpha*s^2.**

We are aware this is equivalent to the Erdos-Straus conjecture for the hard residue class. We have proven computationally that this holds for all P < 10^7. We want to explore whether local-global principles from number theory can bridge the gap between local solvability (which we can verify) and global solvability (which we need).

## Local solvability: what we know

### The D.6 equation modulo small primes

For each prime q, the equation P + 4*alpha*s^2 === 0 (mod 4*alpha*s*r - 1) has solutions (alpha, s, r) modulo q.

Specifically, for fixed q, we need: there exist alpha, s, r mod q such that 4*alpha*s*r === 1 (mod q) and P === -4*alpha*s^2 (mod q).

The first condition says r === (4*alpha*s)^{-1} (mod q) (assuming gcd(4*alpha*s, q) = 1). The second says P === -4*alpha*s^2 (mod q).

For any prime q not dividing 2P: choose s = 1, alpha = -(P+4) * (4)^{-1} (mod q) (if this gives alpha !== 0). Then P + 4*alpha === 0 (mod q), and r = (4*alpha)^{-1} (mod q). This gives a solution mod q.

So: **for every prime q not dividing 2P, the system has a q-adic solution.** For q = 2 and q = P, local solvability can be checked directly.

### Local solvability of the original equation

The equation 4xyz = P(xy + xz + yz), or equivalently 4/P = 1/x + 1/y + 1/z, always has a p-adic solution for every prime p and a real solution. This is because:

- Over R: take x = y = z = 3P/4 (the "equilateral" solution, real-valued).
- Over Q_p for p != P: the equation is smooth at the equilateral point.
- Over Q_P: need to check separately, but solutions exist (the equation has solutions mod P^k for all k by Hensel).

So: **the Erdos-Straus equation satisfies the Hasse condition** (local solvability everywhere). The question is whether the Hasse principle holds.

## Strong approximation

Strong approximation is a tool for showing that a variety with points everywhere locally also has integral points. The classical result:

**Strong approximation theorem (Kneser, Platonov):** Let G be a simply connected semisimple algebraic group over Q. If G is isotropic at infinity (i.e., G(R) is non-compact), then G(Z) is dense in G(A_f) (the finite adeles).

This means: if G has points modulo every prime power (i.e., in G(Z_p) for all p), then G(Z) is non-empty.

### Does strong approximation apply to ES?

The ES equation 4xyz - P(xy + xz + yz) = 0 is NOT a group variety (it's a surface, not a group). So the classical strong approximation theorem doesn't apply directly.

However, there are generalizations:

1. **Strong approximation for affine homogeneous spaces** (Borovoi, Colliot-Thelene, Xu): If V = G/H is an affine homogeneous space of a simply connected group G, then strong approximation holds for V (under certain conditions on H).

2. **Strong approximation for affine quadrics** (Colliot-Thelene, Xu, 2009): For an affine quadric Q defined by a non-degenerate quadratic form, strong approximation holds (off the real place) if Q(R) is non-compact and the relevant spin group is simply connected.

3. **Strong approximation for cubic surfaces** is much harder and generally NOT known. This is active research.

## Reformulating ES as an affine quadric

Can the ES equation be reformulated as a quadratic equation in more variables?

The equation 4xyz = P(xy + xz + yz) can be rewritten by substituting x = a+b, etc., or by completing squares.

Alternatively, the D.6 equation P + 4*alpha*s^2 = (4*alpha*s*r - 1)*m involves 4 variables (alpha, s, r, m) and is LINEAR in r and m (for fixed alpha, s). So it's not quadratic in the usual sense.

But consider: 4*alpha*s*r*m - m = P + 4*alpha*s^2. This is bilinear in (r, m).

Setting u = r*m, the equation becomes: 4*alpha*s*u - m = P + 4*alpha*s^2, so m = 4*alpha*s*u - P - 4*alpha*s^2. And r = u/m = u/(4*alpha*s*u - P - 4*alpha*s^2). For r to be a positive integer, we need m | u and m > 0.

Hmm, this doesn't simplify to a standard form.

### Alternative: ternary quadratic form

The ES equation can be viewed as: find integers x, y, z such that the ternary quadratic form Q(x,y,z) = 4xyz - P(xy + xz + yz) vanishes.

But this is not a quadratic form in the usual sense (it's cubic, not quadratic). However, if we fix one variable, say z, then:

4xyz - P(xy + xz + yz) = 0
xy(4z - P) = Pz(x + y)
xy(4z - P) - Pzx - Pzy = 0
x(y(4z-P) - Pz) = Pzy
x = Pzy / (y(4z-P) - Pz)

For fixed z, this is a rational function of y, and x is rational iff the denominator divides the numerator. This doesn't help with the quadratic form approach.

### Alternative: Mordell-type equation

From P + m = 4*alpha*s*t (where t = r*m - s), and m = (P + 4*alpha*s^2)/M:

We can write: P*M + 4*alpha*s^2 = M * (4*alpha*s*t + P - 4*alpha*s*t)... this is circular.

Let me try a different substitution. From the ES equation directly:

4/P = 1/x + 1/y + 1/z

Set x = Pa, y = Pb, z = Pc (so a, b, c are rational, and we need 1/a, 1/b, 1/c to be positive integers dividing P... no, x, y, z need not be multiples of P).

Actually, the Type II decomposition says one of x, y, z is divisible by P. WLOG z = Pk. Then:

4/P = 1/x + 1/y + 1/(Pk)
4/P - 1/(Pk) = 1/x + 1/y
(4k - 1)/(Pk) = 1/x + 1/y

So: 1/x + 1/y = (4k-1)/(Pk). This is a two-variable Egyptian fraction equation. Setting delta = 4k - 1 (so delta === 3 mod 4):

(x + y)/(xy) = delta/(Pk)
Pk(x + y) = delta * xy
Pk*x + Pk*y - delta*xy = 0
x(Pk - delta*y) = -Pk*y
x = Pk*y / (delta*y - Pk)

For x > 0: need delta*y > Pk, i.e., y > Pk/delta. And x is a positive integer iff (delta*y - Pk) | (Pk*y).

Since Pk*y = Pk*(delta*y - Pk)/(delta) + Pk*Pk/delta... hmm, let me use the standard approach:

delta*xy = Pk*(x + y). Set x = Pk/delta * (1 + delta/d), y = Pk/delta * (1 + delta/(delta - d)) where d | delta^2... this is getting complicated.

The point is: the problem can be reduced to a divisibility problem involving Pk and delta = 4k-1, which is essentially what D.6 does.

## What I need from you

### Question 1: Local-global for the D.6 divisibility condition

For the divisibility condition M | (P + 4*alpha*s^2) where M = 4*alpha*s*r - 1:

- We've shown local solvability modulo every prime q.
- Does any version of the Hasse principle or strong approximation apply to this divisibility condition?
- The condition "M | N" is equivalent to "N === 0 (mod M)," which is an equation in (alpha, s, r) modulo M. But M depends on (alpha, s, r), making this non-standard.

### Question 2: Is the ES surface an affine homogeneous space?

The ES surface S_P: 4xyz = P(xy + xz + yz) has the symmetric group S_3 acting by permuting (x, y, z). But this is a finite group, not an algebraic group.

Are there larger symmetry groups? Is S_P homogeneous under some algebraic group action? If so, strong approximation for homogeneous spaces might apply.

### Question 3: Fibration structure

Consider the fibration pi: S_P -> A^1 given by pi(x,y,z) = z. The fiber pi^{-1}(z_0) is a curve in the (x,y)-plane: 4z_0*xy = P(xy + xz_0 + yz_0), i.e., (4z_0 - P)*xy = P*z_0*(x+y). This is a rational curve (genus 0) for each z_0 (assuming 4z_0 != P).

A fibration into rational curves is a strong structural property. If each fiber is a conic, and every fiber has a rational point, then S_P is rational (Tsen's theorem generalized). Can this be used to show the existence of integer points?

### Question 4: Hardy-Littlewood circle method on the fibered equation

For fixed z = Pk (Type II), the equation becomes:

1/x + 1/y = (4k-1)/(Pk)

This asks for representations of a rational number as a sum of two unit fractions. By the classical theory (Erdos-Graham), the number of such representations is related to the divisor function of Pk*(4k-1).

The Hardy-Littlewood circle method could potentially count solutions (x, y) for the two-variable equation, giving an asymptotic with main term and error term. If the main term is positive (which it should be for P large enough), this gives existence.

### Question 5: Hensel lifting and p-adic density

For each prime q, the q-adic density of solutions (alpha, s, r) to M | (P + 4*alpha*s^2) can be computed. If the product of local densities is positive (the "singular series"), this suggests a positive number of global solutions.

Can you compute this singular series for the D.6 equation? Specifically:

For each prime q, what is the q-adic density:

sigma_q = lim_{k->inf} #{(alpha,s,r) mod q^k : (4*alpha*s*r - 1) | (P + 4*alpha*s^2) mod q^k} / q^{3k}

And is the product prod_q sigma_q positive?

### Question 6: Strong approximation for the specific parametric family

Even though S_P is not an algebraic group, the D.6 parametrization gives a specific affine variety V: the set of (alpha, s, r, m) with P + 4*alpha*s^2 = (4*alpha*s*r - 1)*m.

This variety V is a 3-dimensional affine variety (4 variables, 1 equation). It's a hypersurface in A^4.

**Key property:** V is defined by a BILINEAR equation in (r, m):

4*alpha*s*r*m - m - (P + 4*alpha*s^2) = 0

For fixed (alpha, s), this is: m*(4*alpha*s*r - 1) = P + 4*alpha*s^2, a product of two linear forms equaling a constant. This is a hyperbola in the (r, m)-plane.

Lattice points on hyperbolas are well-studied. The number of lattice points on xy = N is tau(N) (the divisor function). So for fixed (alpha, s), the number of (r, m) solutions is tau(P + 4*alpha*s^2) restricted to divisors === -1 (mod 4*alpha*s).

The question becomes: is this restricted divisor count positive for SOME (alpha, s)?

## Key data to support your analysis

- Local solvability: verified computationally for all primes q <= 10^6 and all P === 1 (mod 24) up to 10^7.
- Global solvability: verified for all P < 10^7 via the D.6 search.
- The singular series (product of local densities) should be positive because the local obstructions are rare.
- For alpha = 1, s = 1: the restricted divisor count tau_{3 mod 4}(P + 4) is positive iff P + 4 has a prime factor === 3 (mod 4). This fails 46.7% of the time.
- Using multiple (alpha, s) pairs reduces the failure rate exponentially.

## Constraints

- We need a result for ALL primes P >= 10^6 (below that, computational certificate).
- Conditional results are acceptable (state the conditions precisely).
- The local-global approach should either (a) prove ES outright, (b) prove it conditionally on a specific conjecture, or (c) explain precisely WHY local-global fails for this problem and what additional information is needed.
- We are formalizing in Lean 4, but deep theorems from algebraic number theory can be axiomatized.
