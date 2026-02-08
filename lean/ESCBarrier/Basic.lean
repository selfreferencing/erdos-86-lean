/-
# ESC Barrier: Basic Definitions

This file contains the core definitions for the ESC barrier theorems.
Each definition corresponds to a section in the written proof.

## Correspondence Table
| Definition | Written Proof Section |
|------------|----------------------|
| TypeICert | Barrier_Formalization_Guide.md §Type I Structure |
| TypeIICert | Barrier_Formalization_Guide.md §Type II Structure |
| egyptianFraction | META_THEOREM_PROOF.md §Statement |
-/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Field.Basic

/-! ## Type I Certificate Structure

**Written proof reference**: Barrier_Formalization_Guide.md, Section "Type I Existence Conditions"

A Type I certificate consists of parameters (a, b, c, d, e) satisfying:
- ce = a + b
- mabd = ne + 1

For simplicity, we often take c = 1, so e = a + b.
-/

/-- Type I certificate parameters for the equation m/n = 1/x + 1/y + 1/z -/
structure TypeICert where
  a : ℕ+
  b : ℕ+
  d : ℕ+
  e : ℕ+
  h_sum : (e : ℕ) = a + b  -- Taking c = 1

/-- The Type I condition: mabd = ne + 1 -/
def typeI_holds (m n : ℕ) (cert : TypeICert) : Prop :=
  m * cert.a * cert.b * cert.d = n * cert.e + 1

/-! ## Type II Certificate Structure

**Written proof reference**: Barrier_Formalization_Guide.md, Section "Type II Existence Conditions"

A Type II certificate satisfies:
- ce = a + b
- mabd = n + e
-/

/-- Type II certificate parameters -/
structure TypeIICert where
  a : ℕ+
  b : ℕ+
  d : ℕ+
  e : ℕ+
  h_sum : (e : ℕ) = a + b

/-- The Type II condition: mabd = n + e -/
def typeII_holds (m n : ℕ) (cert : TypeIICert) : Prop :=
  m * cert.a * cert.b * cert.d = n + cert.e

/-! ## Egyptian Fraction Representation

**Written proof reference**: META_THEOREM_PROOF.md, Statement
-/

/-- m/n = 1/x + 1/y + 1/z has a solution in positive integers -/
def hasEgyptianRep (m n : ℕ) : Prop :=
  ∃ x y z : ℕ+, (m : ℚ) / n = 1 / x + 1 / y + 1 / z

/-! ## Odd Square Predicate

**Written proof reference**: Coverage_Lemma_Proof.md, Statement
-/

/-- n is an odd perfect square -/
def isOddSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, Odd k ∧ n = k^2

/-! ## Solution Counts

**Written proof reference**: Type_I_II_Generalization.md
-/

/-- Count of Type I solutions for m/n (noncomputable placeholder) -/
noncomputable def f_I (m n : ℕ) : ℕ :=
  -- In the actual proof, this counts certificates
  0  -- Placeholder

/-- Count of Type II solutions for m/n (noncomputable placeholder) -/
noncomputable def f_II (m n : ℕ) : ℕ :=
  0  -- Placeholder

/-! ## Portfolio of Constructions

**Written proof reference**: Coverage_Lemma_Proof.md, Portfolio Theorem
-/

/-- The portfolio of (a, b, e) constructions that cover all m with 4 ∤ m -/
def portfolio : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 2), (1, 2, 3), (2, 3, 5), (1, 10, 11), (1, 34, 35), (1, 58, 59)]

/-! ## Key Divisibility Predicates -/

/-- 4 divides m -/
def fourDivides (m : ℕ) : Prop := 4 ∣ m

/-- 4 does not divide m -/
def fourNotDivides (m : ℕ) : Prop := ¬(4 ∣ m)
