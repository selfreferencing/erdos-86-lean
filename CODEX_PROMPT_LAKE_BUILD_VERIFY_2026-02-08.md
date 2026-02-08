# Codex: Build ESCBarrier and Report Results

## Task

Clone the ESCBarrier repo, build it with `lake build`, and report every error and warning. Repeat builds until either (a) the critical-path files compile clean or (b) you've identified every remaining issue.

## Step 1: Clone and Setup

```bash
git clone https://github.com/selfreferencing/erdos-86-lean.git esc
cd esc/lean
cat lean-toolchain
cat lakefile.lean
```

Expected: Lean 4 v4.24.0, Mathlib pinned at `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

## Step 2: Fetch Mathlib and Build

```bash
cd esc/lean
lake update
lake exe cache get   # pulls prebuilt Mathlib oleans if available
lake build 2>&1 | tee build_log_1.txt
```

This will take significant time. You have 32 GB RAM, so Mathlib should fit. If `lake exe cache get` fails, `lake build` will build Mathlib from source (slow but will work).

## Step 3: Analyze Build Output

After `lake build` finishes, run:

```bash
# Count sorry warnings
grep -c "sorry" build_log_1.txt

# List all errors (not warnings)
grep "error" build_log_1.txt

# List all sorry warnings by file
grep "sorry" build_log_1.txt | sort

# Check which critical-path files have issues
for f in Basic OddSquareVanishing CertificateQNR Periodicity CoverageLemma GRHConditional Main; do
  echo "=== ESCBarrier/$f ==="
  grep "ESCBarrier/$f" build_log_1.txt | head -5
done
```

## Step 4: Fix Any Errors

If there are type errors or import errors in the critical-path files:

1. Read the error message carefully
2. The most likely issues are:
   - `dvd_refl` might need to be `Dvd.dvd.refl` or `dvd_refl 4`
   - `Nat.dvd_of_mod_eq_zero` might have moved in this Mathlib version
   - `Nat.eq_mul_of_div_eq_right` might need different syntax
   - PNat coercion issues (ℕ+ to ℕ)
   - `Even.mul_of_left` / `Even.mul_of_right` API may differ
3. Fix the error in the .lean file
4. Re-run `lake build` and repeat

**Critical-path files** (these MUST compile clean):
- `ESCBarrier/Basic.lean` (no sorry, no axioms, should be clean)
- `ESCBarrier/OddSquareVanishing.lean` (2 axioms, proved lemmas)
- `ESCBarrier/CertificateQNR.lean` (3 axioms, proved theorems)
- `ESCBarrier/Periodicity.lean` (3 axioms)
- `ESCBarrier/CoverageLemma.lean` (2 axioms, proved lemmas)
- `ESCBarrier/GRHConditional.lean` (4 axioms)
- `ESCBarrier/Main.lean` (4 theorems, no sorry)

**Non-critical files** (sorry warnings are expected, errors should be fixed):
- `AnalyticTheorems.lean`, `Mod8Coverage.lean`, `QuadraticReciprocityProof.lean`
- `ComputationalVerification.lean`, `AnalyticFromComputational.lean`
- `*_aristotle.lean` files (old Aristotle attempts, may have import issues)

## Step 5: If Errors Require Fixes

Common patterns for this codebase:

### Axiom syntax
Axioms should compile without issue:
```lean
axiom foo : ∀ (n : ℕ), P n
```

### dvd_refl
If `dvd_refl 4` doesn't work, try:
```lean
⟨1, by ring⟩  -- proof that 4 ∣ 4
```

### ZMod issues
If `@IsSquare (ZMod p) _ (r.val : ZMod p)` errors, the instance might need explicit specification. Try:
```lean
@IsSquare (ZMod p) (ZMod.instMul) (r.val : ZMod p)
```

### PNat coercion
If `(cert.a : ℕ)` doesn't coerce, try `cert.a.val` or `(cert.a : ℕ)` with explicit cast.

### Nat.eq_mul_of_div_eq_right
If this API doesn't exist, try:
```lean
Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_div)
```

## Step 6: Report

After the final successful build (or after exhausting fixes), report:

1. **Build status**: PASS / FAIL
2. **Critical-path files**: Which compiled clean? Any errors?
3. **Sorry count**: How many sorry warnings total?
4. **Axiom count**: How many axiom declarations total?
5. **Error list**: Every remaining error, with file:line and message
6. **What you fixed**: Every change you made to get it building

Write the report to `BUILD_REPORT_2026-02-08.md`.

## Important Notes

- You have 32 GB RAM. Mathlib fits comfortably.
- `lake update` + `lake exe cache get` is fastest (downloads prebuilt oleans).
- If cache get fails, `lake build` from source takes ~30-60 min but works.
- Do NOT modify Main.lean unless absolutely necessary.
- Do NOT add sorry to fix errors. Use axioms if you must add assumptions.
- After each fix, re-run `lake build` to check.
- Keep iterating until the critical path compiles clean.
