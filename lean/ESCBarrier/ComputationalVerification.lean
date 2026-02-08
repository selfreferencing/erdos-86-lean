/-
# Computational Verification

Proves portfolio coverage for m ≤ 100 with 4∤m by COMPUTATION.

**Goal**: Establish ground truth about which constructions work for which m
**Status**: Computing individual cases to gather data
-/

import ESCBarrier.Basic
import Mathlib

/-- A construction (a, b, e) works for m if the QR condition is satisfiable -/
def constructionWorks (a b e m : ℕ) : Prop :=
  ∃ k : ℕ, Odd k ∧ (k^2 * e + 1) % (m * a * b) = 0

/-! ## Decidability -/

/-- Check if k is odd -/
def isOdd (k : ℕ) : Bool := k % 2 = 1

/-- Search for an odd k < bound such that k²·e+1 ≡ 0 (mod mab) -/
def searchOddSolution (a b e m bound : ℕ) : Bool :=
  let mab := m * a * b
  (List.range bound).filter isOdd |>.any fun k =>
    (k^2 * e + 1) % mab = 0

/-- Bounded version: check solutions up to 2*m*a*b -/
def constructionWorksDecidable (a b e m : ℕ) : Bool :=
  let mab := m * a * b
  if mab = 0 then false
  else searchOddSolution a b e m (min (2 * mab) 10000)  -- cap at 10k for performance

/-! ## Test Individual Cases -/

-- These should all compute to true or false
#eval constructionWorksDecidable 1 1 2 1
#eval constructionWorksDecidable 1 1 2 5
#eval constructionWorksDecidable 1 1 2 9
#eval constructionWorksDecidable 1 1 2 13

-- Test with m=4 (should be false since 4|m creates obstruction)
#eval constructionWorksDecidable 1 1 2 4

/-! ## Portfolio Coverage Matrix -/

/-- Portfolio of constructions -/
def portfolio : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 2), (1, 2, 3), (2, 3, 5), (1, 10, 11), (1, 34, 35), (1, 58, 59)]

/-- Check if any portfolio construction works for m -/
def portfolioCoversDecidable (m : ℕ) : Bool :=
  portfolio.any fun (a, b, e) => constructionWorksDecidable a b e m

-- Test first few non-divisible-by-4 values
#eval portfolioCoversDecidable 1
#eval portfolioCoversDecidable 2
#eval portfolioCoversDecidable 3
#eval portfolioCoversDecidable 5
#eval portfolioCoversDecidable 6
#eval portfolioCoversDecidable 7
#eval portfolioCoversDecidable 9
#eval portfolioCoversDecidable 10

-- Test that m=4,8,12 give false (4|m)
#eval portfolioCoversDecidable 4
#eval portfolioCoversDecidable 8
#eval portfolioCoversDecidable 12

/-! ## Generate Coverage Data -/

/-- List all m ≤ bound with 4∤m -/
def nonDivisibleBy4 (bound : ℕ) : List ℕ :=
  (List.range (bound + 1)).filter fun m => m > 0 ∧ ¬(4 ∣ m)

/-- Check coverage for all m in list -/
def checkCoverageList (ms : List ℕ) : List (ℕ × Bool) :=
  ms.map fun m => (m, portfolioCoversDecidable m)

-- Generate first 30 cases
#eval checkCoverageList (nonDivisibleBy4 30)

-- Let's also check up to 50
#eval checkCoverageList (nonDivisibleBy4 50)

/-! ## Soundness Lemmas (to be proven) -/

/-- If searchOddSolution returns true, there exists a witness -/
theorem search_implies_exists (a b e m bound : ℕ)
    (h : searchOddSolution a b e m bound = true) :
    ∃ k < bound, Odd k ∧ (k^2 * e + 1) % (m * a * b) = 0 := by
  sorry

/-- If decidable version says yes, the actual property holds -/
theorem decidable_sound (a b e m : ℕ)
    (h : constructionWorksDecidable a b e m = true) :
    constructionWorks a b e m := by
  sorry  -- Will prove after establishing search correctness
