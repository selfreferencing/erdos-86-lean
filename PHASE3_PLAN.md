# Phase 3 Plan: Eliminate the Sorry

## Key Insight

The sorry covers ALL primes in uncovered CRT residue classes, not just the 9
specific primes below 10^6. The sorry region has:

- p % 24 = 1 (1 class)
- p % 7 in {1,2,4} (3 classes)
- p % 5 in {1,4} (2 classes)
- p % 11 in {1,2,3,4,5,6,9} (7 classes, excluding 0,7,8,10)
- p % 19 in {1..13,16,17} (15 classes, excluding 0,14,15,18)
- p % 23 in {1..6,8,9,12..14,16,18} (13 classes, excluding 0,7,10,11,15,17,19..22)

Total CRT classes mod LCM(840, 11*19*23) = mod 4,037,880:
**1 x 3 x 2 x 7 x 15 x 13 = 8,190 classes**

We've only examined 750 of these (those containing primes < 10^6).
The 22 D.6 helpers might cover many of the remaining 7,440, but we haven't checked.

**Critical question: Can a finite set of M values cover ALL 8,190 classes?**
If yes, the sorry is eliminated with ZERO asymptotic argument needed.
D.6 formulas work for ALL primes in each covered class, regardless of size.

## Step 1: Computational Feasibility (Python script)

Write `check_full_coverage.py` that:
1. Enumerates all 8,190 CRT classes (by iterating mod 24, 7, 5, 11, 19, 23)
2. For each class, checks if any of the 25 M values covers it
   (M=11: {7,8,10}; M=19: {14,15,18}; M=23: 9 residues; plus 22 helpers)
3. Reports: how many classes uncovered
4. For uncovered classes, searches for M values up to 5000

## Step 2A: If all classes coverable (best case)

- Generate additional D.6 helpers for new M values
- Put them in a SEPARATE file (ED2HelpersExtra.lean) to avoid memory blowup
- Update dispatch in Existence.lean to call the new helpers
- **Sorry ELIMINATED** -- no asymptotic argument needed

## Step 2B: If not all classes coverable (fallback)

Two sub-options:
- 2B.i: Extend certificates to larger bound + split sorry on p < B
- 2B.ii: Formalize the asymptotic argument (Prop 9.25 + back-test bridge)

## Step 3: File splitting (defensive, do regardless)

Move the 22 D.6 helpers from Existence.lean to ED2Helpers.lean.
This prevents the 70GB memory blowup by splitting compilation units.
