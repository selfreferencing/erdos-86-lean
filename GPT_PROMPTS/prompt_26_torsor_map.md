# GPT Prompt 26: D.6 as Rational Map on Torsor in Cayley Compactification

## Context (follow-up to your previous response)

In your previous response (prompt 17), you offered to "express the D.6 map (alpha, s, r) -> (x, y, z) as a rational map from a torsor to S_P, showing how the (4*alpha*s*r - 1) denominator sits relative to boundary lines in the Cayley compactification." We are accepting that offer.

## Background

We are proving the Erdos-Straus conjecture for primes P === 1 (mod 24). From prompts 17A and 17B:

1. **S_P: 4xyz = P(xy + xz + yz)** is an affine cubic surface whose projective closure is the **Cayley nodal cubic** (4 A_1 nodes, 9 lines, NOT a smooth del Pezzo).

2. **All S_n are isomorphic over Q** by rescaling (x,y,z) -> (x/n, y/n, z/n). The difficulty is entirely in integrality.

3. **S_P is rational over Q.** Explicit birational map: z = Pxy / (4xy - P(x+y)).

4. **Br(S_P)/Br(Q) = Z/2**, transcendental class (quaternion algebra). No BM obstruction to natural-number solutions.

5. **D.6 parametrization gives a rational map from A^3 (or an open subset) to S_P.** The "(4*alpha*s*r - 1)" denominator corresponds to a specific divisor in the Cayley compactification.

## The D.6 map explicitly

Given (alpha, s, r) with M = 4*alpha*s*r - 1 dividing P + 4*alpha*s^2, set:
- m = (P + 4*alpha*s^2) / M
- d = alpha * s^2
- A = alpha * s * (m*r - s)
- delta = 4A - P = m - 1 (from P + m = 4A)
- b' = s, c' = m*r - s
- Then x = A, y = b'*P = s*P, z = c'*P = (m*r - s)*P

So the map (alpha, s, r) -> (x, y, z) is:

x = alpha * s * ((P + 4*alpha*s^2)*r / (4*alpha*s*r - 1) - s)
y = s * P
z = ((P + 4*alpha*s^2)*r / (4*alpha*s*r - 1) - s) * P

This is a rational map from A^3 to S_P, defined on the open set where 4*alpha*s*r - 1 != 0 and M | (P + 4*alpha*s^2).

## What I need from you

### Task 1: Write the map in homogeneous coordinates

Express the D.6 map in the projective closure. The Cayley cubic in P^3 is:

4X_0 X_1 X_2 = P * X_3 * (X_0 X_1 + X_0 X_2 + X_1 X_2)

(where X_3 is the homogenizing coordinate, with x = X_0/X_3, y = X_1/X_3, z = X_2/X_3).

Write the map (alpha, s, r) -> [X_0 : X_1 : X_2 : X_3] explicitly. Clear denominators to get a polynomial map from A^3 to P^3.

### Task 2: Identify the base locus

The rational map fails to be defined where the denominator vanishes. In affine coordinates, this is the locus {4*alpha*s*r - 1 = 0} (plus the locus where m*r - s = 0, giving A = 0).

In the projective setting, what is the base locus of the map? Is it a curve, a point, or empty?

### Task 3: Image and boundary

The image of the D.6 map lands in the affine part of S_P (where x, y, z > 0 for solutions). What part of the BOUNDARY of S_P in the Cayley compactification does it approach as parameters degenerate?

The Cayley cubic has:
- 4 nodes (A_1 singularities)
- 9 lines (6 edge lines connecting nodes, 3 coplanar)

As (4*alpha*s*r - 1) -> 0 (the "M -> 0" limit), where does the image go in the compactification? Does it approach a specific node or line?

As alpha -> infinity (with s, r fixed), where does the image go?
As s -> infinity (with alpha, r fixed)?
As r -> infinity (with alpha, s fixed)?

### Task 4: The denominator as a boundary divisor

The denominator 4*alpha*s*r - 1 defines a hypersurface in the parameter space A^3. Its image in S_P should correspond to a specific divisor in the compactification.

Identify: which of the 9 lines or which boundary component of the Cayley cubic corresponds to the locus where 4*alpha*s*r - 1 = 0?

This is relevant because: the integrality condition (M | N) is asking for the map to avoid this boundary divisor in a specific way (M divides N means the image lands at a point where the "distance" to the boundary is measured by M).

### Task 5: Is D.6 a universal torsor map?

Bright-Loughran note that D.6 parametrization IS a dominant rational map from a candidate universal torsor to S_P. Can you verify this?

A universal torsor for a variety V is a torsor under the Neron-Severi torus T = Hom(Pic(V), G_m). For the Cayley cubic:
- Pic(U) = Z for the open log surface U (prompt 17B)
- The NS torus is G_m (rank 1)

So a universal torsor should be a G_m-torsor over U. Is the D.6 parameter space (or an open subset of it) such a torsor?

If yes, then integral points on S_P correspond bijectively to integral points on the torsor satisfying coprimality conditions. State these conditions.

### Task 6: How does the Brauer element interact with D.6?

The Brauer group element alpha in Br(S_P)/Br(Q) = Z/2 is computed by Bright-Loughran as a quaternion algebra. When we pull this back along the D.6 map, we get an element of Br(A^3) which should be trivial (since Br(A^3) = Br(Q)).

But the evaluation of alpha at a specific rational point (x, y, z) = D.6(alpha_0, s_0, r_0) gives a Hilbert symbol that constrains solutions.

Compute this Hilbert symbol in terms of (alpha_0, s_0, r_0, M, m). Does it impose a condition beyond the D.6 divisibility?

## Constraints

- This prompt is about ORGANIZATION, not proof. The goal is to understand the geometry of our parametrization.
- Concrete computations for specific examples (e.g., P=97, the smallest prime === 1 (mod 24) that needs the full D.6 machinery) are welcome.
- If the universal torsor identification is too involved, a partial answer (identifying the map as dominant rational, without the torsor structure) is acceptable.
- Connections to the "A = (P+m)/4" reformulation from prompt 18 are welcome.
