import Mathlib
import ErdosStraus.Bradford

namespace ErdosStraus

/--
A reusable *parametric family* interface for Stage 6+.

Intended usage:

- pick a modulus `M` (e.g. 840),
- fix a shift `k` and define the candidate `x(p) = ceil(p/4)+k`,
- for each residue class `r (mod M)` supply a lemma producing a Type II witness divisor `d`.

This structure is deliberately minimal: it only records the data needed to turn a witness into a certificate.
-/
structure TypeIIFamily where
  (M : ℕ)
  (k : ℕ)
  (goodClass : ℕ → Prop)
  (x : ℕ → ℕ)
  (witness : ∀ {p : ℕ}, goodClass p → ∃ d : ℕ, TypeIIWitness p (x p) d)

/--
Turn any `TypeIIFamily` witness into an Erdős–Straus certificate (once Bradford validity is available).

In Stage 6 this lemma becomes the main bridge:

`family` + `bradford_typeII_valid` ⇒ solutions for every prime in the family.
-/
theorem family_implies_solution
    (F : TypeIIFamily) {p : ℕ} (hp : Nat.Prime p) (hgood : F.goodClass p)
    (hm : m p (F.x p) > 0) (hx : F.x p < p) : HasSolution p := by
  rcases F.witness hgood with ⟨d, hd, hle, hcong⟩
  -- Apply the core Bradford lemma.
  -- (Note: `bradford_typeII_valid` in `ErdosStraus/Bradford.lean` still has `sorry`s;
  -- Stage 6 should replace them with a fully proven lemma.)
  simpa [HasSolution] using bradford_typeII_valid (p := p) (x := F.x p) (d := d)
    hp hm hx hd hcong hle

end ErdosStraus
