import ErdosStraus.Basic
import ErdosStraus.FamiliesK10Common
import Mathlib.Tactic

namespace ErdosStraus

/-- Stage 8 core goal: show the 10-k disjunction of (d=1 or QR-sufficient) conditions.

This file isolates *one* hard lemma: `ten_k_cover_exists`, whose proof is the
mathematical content of Stage 8.

Everything else is structural glue that turns an `∃ k ∈ K10` statement into the
explicit disjunction required by downstream files.
-/

/-- **Stage 8 key lemma (the only missing mathematical step).**

For every Mordell-hard prime `p`, at least one `k` in `K10` satisfies
`kSufficient k p`.

In the project roadmap, this is obtained by proving that the simultaneous failure of
all 10 `QRSufficient k p` predicates is impossible (via the QR obstruction pattern).
-/
theorem ten_k_cover_exists (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    ∃ k ∈ K10, kSufficient k p := by
  -- TODO(Stage 8): prove existence of a QR-sufficient k in K10 for every Mordell-hard prime.
  --
  -- Suggested route (from the Stage 8 prompt):
  --   1. Assume all k in K10 fail, i.e. `¬ kSufficient k p`.
  --   2. From `¬ QRSufficient k p`, obtain `QROstruction k p` via
  --      `qr_obstruction_of_not_QRSufficient`.
  --   3. Show the 10 obstructions cannot hold simultaneously for a Mordell-hard prime.
  --
  -- This is the *only* place where new number theory is needed.
  sorry

/-- The explicit 10-way disjunction (as in the Stage 8 prompt). -/
theorem ten_k_cover_complete (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    k5Sufficient p ∨ k7Sufficient p ∨ k9Sufficient p ∨ k11Sufficient p ∨
    k14Sufficient p ∨ k17Sufficient p ∨ k19Sufficient p ∨ k23Sufficient p ∨
    k26Sufficient p ∨ k29Sufficient p := by
  classical
  rcases ten_k_cover_exists p hp hMH with ⟨k, hkK, hkS⟩
  -- Turn `k ∈ K10` into a concrete equality `k = ...`.
  have hkEq : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 14 ∨
              k = 17 ∨ k = 19 ∨ k = 23 ∨ k = 26 ∨ k = 29 := by
    -- `simp` expands membership in the explicit finset literal.
    simpa [K10] using hkK
  -- Dispatch to the appropriate disjunct.
  rcases hkEq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    -- each branch is immediate
    (first | exact Or.inl hkS
           | exact Or.inr (Or.inl hkS)
           | exact Or.inr (Or.inr (Or.inl hkS))
           | exact Or.inr (Or.inr (Or.inr (Or.inl hkS)))
           | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkS))))
           | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkS)))))
           | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkS))))))
           | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkS)))))))
           | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hkS))))))))
           | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hkS)))))))))

end ErdosStraus
