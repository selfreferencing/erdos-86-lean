/-
# Quick Pattern Scan

Fast computational checks to identify analytic proof patterns.
-/

import Mathlib

/-- Check if k works for construction (a,b,e) at m -/
def works (a b e m k : ℕ) : Bool :=
  k % 2 = 1 && (k^2 * e + 1) % (m * a * b) = 0

/-! ## Direct Tests for Pattern Discovery -/

-- Construction (1,1,2): Test small witnesses
#eval works 1 1 2 1 1   -- m=1, k=1
#eval works 1 1 2 3 1   -- m=3, k=1
#eval works 1 1 2 5 1   -- m=5, k=1
#eval works 1 1 2 5 3   -- m=5, k=3
#eval works 1 1 2 7 1   -- m=7, k=1

-- Pattern hypothesis: k=1 works for many m with construction (1,1,2)?
#eval [(1,1,2,1,1), (1,1,2,3,1), (1,1,2,5,1), (1,1,2,7,1), (1,1,2,9,1),
       (1,1,2,11,1), (1,1,2,13,1), (1,1,2,15,1), (1,1,2,17,1), (1,1,2,19,1)]
  |>.map fun (a,b,e,m,k) => (m, works a b e m k)

-- When does k=1 work for (1,1,2,m)?
-- Need: 1² · 2 + 1 = 3 ≡ 0 (mod m·1·1 = m)
-- So: 3 ≡ 0 (mod m), i.e., m | 3
-- This means k=1 only works when m ∈ {1, 3}!

-- Let's check k=1 fails for m=5:
#eval works 1 1 2 5 1   -- Should be false

-- For m=5, try other small odd k:
#eval [(1,k) | k ← [1,3,5,7,9,11,13,15]].map fun (m,k) =>
  (5, k, works 1 1 2 5 k)

-- Check m=7:
#eval [(7,k) | k ← [1,3,5,7,9,11,13,15,17,19]].map fun (m,k) =>
  (m, k, works 1 1 2 m k)

/-! ## Systematic Small Witness Search -/

-- For each m ≤ 30 with 4∤m, find smallest odd k that works for (1,1,2)
def findSmallestWitness (a b e m : ℕ) : Option ℕ :=
  let bound := min (m * a * b * 2) 200
  (List.range bound).find? fun k =>
    k % 2 = 1 && (k^2 * e + 1) % (m * a * b) = 0

#eval [(m, findSmallestWitness 1 1 2 m) |
       m ← (List.range 31).filter fun m => m > 0 ∧ ¬(4 ∣ m)]

/-! ## Pattern Analysis -/

-- Hypothesis: For (1,1,2), if 2 is a QR mod m, then small k exists
-- Quadratic reciprocity: (2/p) = 1 iff p ≡ ±1 (mod 8) for odd prime p

-- Check pattern for small primes:
-- p=3: 3 ≡ 3 (mod 8), expect (2/3) = -1, so might be hard
-- p=5: 5 ≡ 5 (mod 8), expect (2/5) = -1
-- p=7: 7 ≡ 7 (mod 8), expect (2/7) = 1
-- p=17: 17 ≡ 1 (mod 8), expect (2/17) = 1

#eval [3,5,7,11,13,17,19,23,29].map fun p =>
  (p, p % 8, findSmallestWitness 1 1 2 p)

/-! ## Construction (1,2,3) Analysis -/

-- Need: k² · 3 + 1 ≡ 0 (mod m·1·2 = 2m)
-- i.e., k² ≡ -1/3 (mod 2m)

#eval [(m, findSmallestWitness 1 2 3 m) |
       m ← [1,2,3,5,6,7,9,10,11,13,14,15,17,18,19,21,22,23]]

/-! ## Construction (2,3,5) Analysis -/

-- Need: k² · 5 + 1 ≡ 0 (mod m·2·3 = 6m)

#eval [(m, findSmallestWitness 2 3 5 m) |
       m ← [1,2,3,5,6,7,9,10,11,13,14,15,17,18,19]]

/-! ## Which construction covers each m? -/

def portfolio : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 2), (1, 2, 3), (2, 3, 5), (1, 10, 11), (1, 34, 35), (1, 58, 59)]

def whichConstructions (m : ℕ) : List (ℕ × ℕ × ℕ) :=
  portfolio.filter fun (a,b,e) =>
    (findSmallestWitness a b e m).isSome

#eval [(m, whichConstructions m) | m ← [1,2,3,5,6,7,9,10,11,13,14,15,17,18,19]]

/-! ## Summary

This quick scan should reveal:
1. Which constructions cover which m values
2. Witness sizes (are they small/predictable?)
3. Modular patterns (m mod 8, etc.)
4. Candidate analytic theorems based on QR theory
-/
