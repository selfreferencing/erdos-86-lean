# Erdős-Straus Conjecture: Proof Strategy Explained

## The Conjecture

The Erdős-Straus conjecture states that for every integer n ≥ 2:

```
4/n = 1/x + 1/y + 1/z
```

has a solution in positive integers x, y, z.

## Why Focus on "Mordell-Hard" Primes?

Most integers n have easy solutions. The difficult cases are certain **prime** numbers. Through classical analysis (going back to Mordell, Schinzel, and others), the "hard" primes are those satisfying:

```lean
def MordellHard (p : ℕ) : Prop :=
  p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨
  p % 840 = 289 ∨ p % 840 = 361 ∨ p % 840 = 529
```

These are exactly the primes where simpler methods (Type I constructions, basic divisibility tricks) fail.

**Key fact**: 840 = 2³ × 3 × 5 × 7. The Mordell-hard residues {1, 121, 169, 289, 361, 529} are exactly the perfect squares mod 840 that are coprime to 840.

## The Bradford Type II Construction

The strategy uses the **Bradford Type II construction**. Given a prime p ≡ 1 (mod 4):

### Step 1: Choose x and compute m

For a parameter k, define:
- **x = x₀(p) + k** where x₀(p) = ⌈p/4⌉ = (p+3)/4
- **m = 4x - p = 4k + 3**

### Step 2: Find a witness divisor d

We need a divisor d of x² satisfying:
- d ≤ x
- d ≡ -x (mod m)  [equivalently: x + d ≡ 0 (mod m)]

### Step 3: The explicit solution

When such d exists, the Erdős-Straus solution is:
```
y = p(x + d) / m
z = p(x + x²/d) / m
```

The Bradford.lean file proves this construction is valid (produces positive integers satisfying the equation).

## What is K10?

**K10** is a "cover set" of 10 values of k:

```lean
def K10 : Finset ℕ := {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}
```

**Claim**: For every Mordell-hard prime p, at least one k ∈ K10 provides a valid Bradford Type II witness.

### Why these specific k values?

Each k gives a modulus m = 4k + 3:

| k  | m = 4k+3 |
|----|----------|
| 5  | 23       |
| 7  | 31       |
| 8  | 35       |  ← This is what K8Lemmas.lean handles!
| 9  | 39       |
| 11 | 47       |
| 14 | 59       |
| 17 | 71       |
| 19 | 79       |
| 23 | 95       |
| 26 | 107      |
| 29 | 119      |

## The "kSufficient" Predicate

For each k, we define when k "works" for prime p:

```lean
def kSufficient (k p : ℕ) : Prop := d1Sufficient k p ∨ QRSufficient k p
```

### Option 1: d1Sufficient (The Easy Family)

```lean
def d1Sufficient (k p : ℕ) : Prop := p % (16*k + 12) = (12*k + 5)
```

When p falls in this special congruence class, **d = 1** works as the witness!

Why? Because the congruence guarantees x + 1 ≡ 0 (mod m).

### Option 2: QRSufficient (General Witness Existence)

```lean
def QRSufficient (k p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (xK p k)^2 ∧ d ≤ xK p k ∧ Nat.ModEq (mK k) (xK p k + d) 0
```

This is the witness-carrying condition: there exists some d with the required properties.

## The QR Obstruction Analysis

When does QRSufficient **fail**? The key insight is about **quadratic residues**.

### The Obstruction Conditions

```lean
def AllQR (k p : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ xK p k → IsQuadraticResidue q (mK k)

def TargetNQR (k p : ℕ) : Prop :=
  ¬ IsSquare (-(xK p k : ZMod (mK k)))

def QROstruction (k p : ℕ) : Prop := AllQR k p ∧ TargetNQR k p
```

**Translation**: The QR obstruction occurs when:
1. Every prime factor of x is a quadratic residue mod m
2. BUT the target value -x is NOT a quadratic residue mod m

When both hold, no divisor of x² can be congruent to -x mod m (because divisors of x² only cover quadratic residues, not non-residues).

## What K8Lemmas.lean Proves

For k = 8 (m = 35), we prove the QR obstruction **cannot occur** for Mordell-hard primes:

```lean
theorem no_qr_obstruction_k8 (p : ℕ) (_hp : Nat.Prime p) (hMH : MordellHard p) :
    ¬ QROstruction 8 p
```

### The Key Lemmas (3.1.A through 3.1.D):

1. **mordell_hard_mod_12**: Mordell-hard ⟹ p ≡ 1 (mod 12)

2. **three_divides_x_k8**: p ≡ 1 (mod 12) ⟹ 3 ∣ x where x = (p+35)/4

3. **three_nqr_mod_35**: 3 is NOT a quadratic residue mod 35

4. **no_qr_obstruction_k8**: Combining (2) and (3): Since 3 divides x and 3 is NQR mod 35, the "AllQR" condition fails ⟹ no obstruction!

## The Overall Proof Structure

```
For all Mordell-hard primes p:
  ∃ k ∈ K10 such that kSufficient k p

where kSufficient means:
  (p is in the d=1 family for this k)
  OR
  (∃ witness d: d|x², d≤x, x+d≡0 (mod m))

The second option is proven by showing:
  ¬QROstruction k p  (no quadratic residue obstruction)
  ⟹ ∃ witness d     (by the subgroup/coset argument)
```

## File Organization

| File | Purpose |
|------|---------|
| `Basic.lean` | Core definitions: EscEq, Conjecture, MordellHard, x0, x_of, m_of |
| `Bradford.lean` | Proves Bradford Type II gives valid solution |
| `K0.lean` | Special case k=0 (m=3), uses mod-3 prime factors |
| `K1.lean` | Definitions for quadratic residue analysis |
| `K8Lemmas.lean` | **The key file**: proves no QR obstruction at k=8 |
| `FamiliesK10Common.lean` | Shared definitions for all k in K10 |
| `Families_k*.lean` | Individual family analysis for each k |
| `Covering*.lean` | The finite certificate verification for p ≤ 10⁷ |
| `Main.lean` | Top-level imports |

## What's Still Needed

1. **Prove kSufficient for each k ∈ K10**: Show that for each k, either the d1 family covers the prime, OR the QR obstruction doesn't hold (so a witness exists).

2. **Prove the cover is complete**: Show that for any Mordell-hard prime p, at least one k ∈ K10 satisfies kSufficient k p.

3. **Connect to the conjecture**: Chain everything together:
   - kSufficient ⟹ HasBradfordII ⟹ Conjecture

## The Insight Behind K10

The 10 values were discovered empirically: for all Mordell-hard primes up to 10⁷, at least one k in {5,7,9,11,14,17,19,23,26,29} provides a valid Bradford witness.

The theoretical goal is to prove this holds for ALL Mordell-hard primes, not just small ones. The QR obstruction analysis is the key: by showing that certain k values avoid the obstruction for various residue classes, we can cover all cases.
