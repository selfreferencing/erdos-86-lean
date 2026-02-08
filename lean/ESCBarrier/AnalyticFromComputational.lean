/-
# Analytic Proofs from Computational Evidence

Extract patterns from computational verification to generate analytic proofs.

**Strategy**:
1. Track WHICH constructions work for WHICH m values
2. Find witnesses (specific k values) for each success
3. Identify patterns: modular classes, prime factorizations, etc.
4. Generate analytic theorems from patterns

This mirrors the Erdős Ternary Digits approach where computational scanning
revealed analytic proof patterns.
-/

import ESCBarrier.Basic
import Mathlib

/-- A construction (a, b, e) works for m if the QR condition is satisfiable -/
def constructionWorks (a b e m : ℕ) : Prop :=
  ∃ k : ℕ, Odd k ∧ (k^2 * e + 1) % (m * a * b) = 0

/-- Portfolio of constructions -/
def portfolio : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 2), (1, 2, 3), (2, 3, 5), (1, 10, 11), (1, 34, 35), (1, 58, 59)]

/-! ## Detailed Computational Analysis -/

/-- Find the SMALLEST odd k that works, if any -/
def findWitness (a b e m bound : ℕ) : Option ℕ :=
  let mab := m * a * b
  if mab = 0 then none
  else
    (List.range bound).filter (fun k => k % 2 = 1)
    |>.find? fun k => (k^2 * e + 1) % mab = 0

/-- Detailed result: which construction works and with what witness -/
structure CoverageDetail where
  m : ℕ
  construction : ℕ × ℕ × ℕ  -- (a, b, e)
  witness : ℕ               -- the k that works
  deriving Repr

/-- Find all constructions that cover m, with witnesses -/
def analyzeCoverage (m : ℕ) (bound : ℕ := 1000) : List CoverageDetail :=
  portfolio.filterMap fun (a, b, e) =>
    match findWitness a b e m bound with
    | none => none
    | some k => some ⟨m, (a, b, e), k⟩

/-- Batch analysis for multiple m values -/
def analyzeRange (mList : List ℕ) : List CoverageDetail :=
  mList.bind analyzeCoverage

/-! ## Pattern Extraction -/

/-- Group m values by which construction covers them -/
def groupByConstruction (details : List CoverageDetail) :
    List ((ℕ × ℕ × ℕ) × List ℕ) :=
  portfolio.map fun constr =>
    (constr, details.filter (fun d => d.construction == constr) |>.map (·.m))

/-- Analyze modular patterns for a specific construction -/
def analyzeModularPattern (a b e : ℕ) (covered : List ℕ) : List (ℕ × ℕ) :=
  -- For each modulus d from 2 to 20, check what residue classes appear
  (List.range 18 |>.map (·+2)).bind fun d =>
    let residues := covered.map (· % d) |>.eraseDups
    if residues.length < d then [(d, residues.length)] else []

/-! ## Run Detailed Analysis -/

-- Analyze first 30 non-divisible-by-4 values
def testRange : List ℕ :=
  (List.range 31).filter fun m => m > 0 ∧ ¬(4 ∣ m)

#eval testRange.length  -- Should be 23 values

-- Get full coverage details
#eval analyzeCoverage 1
#eval analyzeCoverage 5
#eval analyzeCoverage 9
#eval analyzeCoverage 13

-- Full analysis
def fullAnalysis := analyzeRange testRange

#eval fullAnalysis.length  -- How many (m, construction, witness) triples?

-- Group by construction to see coverage patterns
#eval groupByConstruction fullAnalysis

/-! ## Specific Pattern Tests -/

-- Construction (1,1,2): Does it cover all m ≡ 1 (mod 4)?
def mod4_is_1 := testRange.filter (· % 4 = 1)
#eval mod4_is_1
#eval mod4_is_1.all fun m =>
  (analyzeCoverage m).any (fun d => d.construction == (1, 1, 2))

-- Construction (1,1,2): Does it cover all odd primes?
def oddPrimes30 := [3, 5, 7, 11, 13, 17, 19, 23, 29]
#eval oddPrimes30.all fun m =>
  (analyzeCoverage m).any (fun d => d.construction == (1, 1, 2))

-- Construction (1,2,3): What residue classes mod 6 does it cover?
def covered_by_123 := fullAnalysis.filter (fun d => d.construction == (1, 2, 3))
  |>.map (·.m)
#eval covered_by_123.map (· % 6) |>.eraseDups

-- Construction (2,3,5): What about mod 10?
def covered_by_235 := fullAnalysis.filter (fun d => d.construction == (2, 3, 5))
  |>.map (·.m)
#eval covered_by_235.map (· % 10) |>.eraseDups

/-! ## Witness Pattern Analysis -/

-- For construction (1,1,2), what are the witnesses?
def witnesses_112 := fullAnalysis.filter (fun d => d.construction == (1, 1, 2))
  |>.map fun d => (d.m, d.witness)
#eval witnesses_112

-- Pattern: Is k related to m in a simple way?
-- Check if k ≡ ±1 (mod something related to m)
#eval witnesses_112.map fun (m, k) =>
  (m, k, k % m, (m - k % m) % m)  -- (m, k, k mod m, -k mod m)

/-! ## Analytic Theorem Candidates -/

/-- Candidate Theorem 1: Construction (1,1,2) covers m ≡ 1,3 (mod 8) -/
theorem construction_112_covers_mod8_pattern (m : ℕ)
    (h : m % 8 = 1 ∨ m % 8 = 3)
    (hm_pos : 0 < m) :
    constructionWorks 1 1 2 m := by
  sorry  -- To be proven after verifying pattern holds computationally

/-- Candidate Theorem 2: Every odd m is covered by SOME portfolio construction -/
theorem odd_implies_covered (m : ℕ) (hm : Odd m) :
    ∃ t ∈ portfolio, let (a, b, e) := t; constructionWorks a b e m := by
  sorry  -- To be proven after computational verification

/-- Candidate Theorem 3: Construction (1,1,2) works when 2 is QR mod m -/
theorem construction_112_when_2_is_QR (m : ℕ) (hm : Odd m)
    (h_qr : ∃ x : ZMod m, x^2 = 2) :
    constructionWorks 1 1 2 m := by
  sorry  -- Connect to witness via quadratic reciprocity

/-! ## Meta-Analysis Functions -/

/-- Check if a proposed pattern holds for all tested m values -/
def checkPattern (pattern : ℕ → Bool) (mValues : List ℕ) : Bool :=
  mValues.all pattern

/-- Find modular patterns: for what moduli d do covered values fall in few residue classes? -/
def findModularStructure (covered : List ℕ) : List (ℕ × List ℕ) :=
  (List.range 18 |>.map (·+2)).filterMap fun d =>
    let residues := (covered.map (· % d)).eraseDups.toArray.qsort (·<·) |>.toList
    -- If less than 75% of residue classes are used, report it
    if residues.length * 4 < 3 * d then some (d, residues) else none

#eval findModularStructure covered_by_123
#eval findModularStructure covered_by_235

/-! ## Summary

This file provides tools to:

1. Extract detailed witnesses for each (m, construction) pair
2. Group m values by which construction covers them
3. Analyze modular patterns (residue classes)
4. Test candidate analytic theorems
5. Identify structure that might lead to proofs

**Next steps**:
- Run on larger ranges (m ≤ 100)
- Identify strong patterns (>95% confidence)
- Generate analytic proofs for those patterns
- Chain patterns to get full coverage
-/
