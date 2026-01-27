# Model Strategy Notes

## M3 Vindicated Again (January 26, 2025)

The micro-decomposition strategy works. When monolithic prompts crash every model (Thinking crashed twice at ~30 min each, Pro crashed at 92 min), breaking the problem into small isolated lemmas succeeds.

**What failed:**
- Full `hdigit_iff` prompt to Thinking: non-compiling code (confused top/bottom digit, circular reference)
- Full Lemma C prompt to Thinking x2: both crashed (~28-30 min each, lemma shopping loops)
- Full `hdigit_iff` prompt to Pro: 92 minutes, forgot its own input

**What worked:**
- Lemma A (1 micro-lemma): solved instantly by Thinking
- Lemma B (3 sub-lemmas): solved by Thinking b1 with explicit calc chains
- C1 (five_q_zero + q_sq_zero): solved by Thinking
- C2 (product_zmod_eq): solved by Thinking -- the hardest piece, used explicit calc chains alternating `ring` and `simp [hypothesis]`
- C3 (val_of_small_nat): solved by Thinking
- C4 (ne_zero_iff_cast_ne_zero): solved by Thinking
- C5 (mod_cast_eq_digit): solved by Thinking

**The pattern:** Models crash when they have to search a large tactic space. They succeed when the goal is small enough that explicit calc chains or 2-3 tactic calls close it. The key failure mode is "lemma shopping" -- cycling through `simp` configurations until budget exhaustion.

**The lesson:** Go micro. Decompose until each piece is trivially within the model's reliable range. Then assemble.
