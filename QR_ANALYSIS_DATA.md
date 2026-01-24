# Quadratic Residue Analysis for K10 Moduli

## The moduli m_k = 4k + 3

| k | m_k | Factorization | φ(m_k) | |Q_m| |
|---|-----|---------------|--------|--------|
| 5 | 23 | prime | 22 | 11 |
| 7 | 31 | prime | 30 | 15 |
| 9 | 39 | 3 × 13 | 24 | 6 |
| 11 | 47 | prime | 46 | 23 |
| 14 | 59 | prime | 58 | 29 |
| 17 | 71 | prime | 70 | 35 |
| 19 | 79 | prime | 78 | 39 |
| 23 | 95 | 5 × 19 | 72 | 18 |
| 26 | 107 | prime | 106 | 53 |
| 29 | 119 | 7 × 17 | 96 | 24 |

---

## QR Status of Small Primes

For prime p and odd prime m, (p/m) = p^((m-1)/2) mod m.
For composite m = ab, use CRT: p is QR mod m iff p is QR mod a AND mod b.

### Prime 2
- (2/23) = 2^11 mod 23 = 2048 mod 23 = 2048 - 89×23 = 2048 - 2047 = 1 → QR
- (2/31) = 2^15 mod 31 = 32768 mod 31 = 32768 - 1057×31 = 32768 - 32767 = 1 → QR
- (2/39): (2/3) = -1 (NQR), (2/13) = -1 (NQR) → 2 is QR mod 39 (both -1 means product is +1)
- (2/47) = 2^23 mod 47. 2^23 = 8388608. 8388608 mod 47 = 1 → QR
- (2/59) = 2^29 mod 59. By quadratic reciprocity: (2/p) = (-1)^((p²-1)/8). (59²-1)/8 = (3481-1)/8 = 435. 435 mod 2 = 1 → (2/59) = -1 → NQR
- (2/71) = (-1)^((71²-1)/8) = (-1)^630 = 1 → QR
- (2/79) = (-1)^((79²-1)/8) = (-1)^780 = 1 → QR
- (2/95): (2/5) = -1, (2/19) = 1 → product = -1 → NQR mod 95
- (2/107) = (-1)^((107²-1)/8) = (-1)^1428 = 1 → QR
- (2/119): (2/7) = 1, (2/17) = 1 → QR mod 119

| k | m_k | (2/m_k) |
|---|-----|---------|
| 5 | 23 | QR |
| 7 | 31 | QR |
| 9 | 39 | QR |
| 11 | 47 | QR |
| 14 | 59 | **NQR** |
| 17 | 71 | QR |
| 19 | 79 | QR |
| 23 | 95 | **NQR** |
| 26 | 107 | QR |
| 29 | 119 | QR |

**Key insight**: If 2 | x_k for k ∈ {14, 23}, then Obs_k fails (2 is NQR, so not all prime factors are QR).

---

### Prime 3
Using (3/p) = (-1)^((p-1)/2) × (p/3) by quadratic reciprocity.

- (3/23): (23/3) = (2/3) = -1, (23-1)/2 = 11 odd → (3/23) = -1 × -1 = 1 → QR
- (3/31): (31/3) = (1/3) = 1, (31-1)/2 = 15 odd → (3/31) = -1 × 1 = -1 → NQR
- (3/39): 3 | 39, so 3 ≡ 0 mod 3, not a unit → N/A (always divides, trivially fails QR test)
- (3/47): (47/3) = (2/3) = -1, (47-1)/2 = 23 odd → (3/47) = 1 → QR
- (3/59): (59/3) = (2/3) = -1, (59-1)/2 = 29 odd → (3/59) = 1 → QR
- (3/71): (71/3) = (2/3) = -1, (71-1)/2 = 35 odd → (3/71) = 1 → QR
- (3/79): (79/3) = (1/3) = 1, (79-1)/2 = 39 odd → (3/79) = -1 → NQR
- (3/95): 3 is coprime to 95. (3/5) = -1, (3/19): (19/3) = (1/3) = 1, (19-1)/2 = 9 odd → (3/19) = -1 → NQR. Product = 1 → QR mod 95
- (3/107): (107/3) = (2/3) = -1, (107-1)/2 = 53 odd → (3/107) = 1 → QR
- (3/119): (3/7) = -1, (3/17) = -1 → product = 1 → QR mod 119

| k | m_k | (3/m_k) |
|---|-----|---------|
| 5 | 23 | QR |
| 7 | 31 | **NQR** |
| 9 | 39 | divides m |
| 11 | 47 | QR |
| 14 | 59 | QR |
| 17 | 71 | QR |
| 19 | 79 | **NQR** |
| 23 | 95 | QR |
| 26 | 107 | QR |
| 29 | 119 | QR |

**Key insight**: If 3 | x_k for k ∈ {7, 19}, then Obs_k fails.

---

### Prime 5
- (5/23): (23/5) = (3/5) = -1, (23-1)/2 = 11 odd → (5/23) = 1 → QR
- (5/31): (31/5) = (1/5) = 1, (31-1)/2 = 15 odd → (5/31) = -1 → NQR
- (5/39): (5/3) = -1, (5/13) = (13/5) × (-1)^2 = (3/5) = -1 → product = 1 → QR
- (5/47): (47/5) = (2/5) = -1, (47-1)/2 = 23 odd → (5/47) = 1 → QR
- (5/59): (59/5) = (4/5) = 1, (59-1)/2 = 29 odd → (5/59) = -1 → NQR
- (5/71): (71/5) = (1/5) = 1, (71-1)/2 = 35 odd → (5/71) = -1 → NQR
- (5/79): (79/5) = (4/5) = 1, (79-1)/2 = 39 odd → (5/79) = -1 → NQR
- (5/95): 5 | 95 → divides m
- (5/107): (107/5) = (2/5) = -1, (107-1)/2 = 53 odd → (5/107) = 1 → QR
- (5/119): (5/7) = -1, (5/17) = (17/5) × 1 = (2/5) = -1 → product = 1 → QR

| k | m_k | (5/m_k) |
|---|-----|---------|
| 5 | 23 | QR |
| 7 | 31 | **NQR** |
| 9 | 39 | QR |
| 11 | 47 | QR |
| 14 | 59 | **NQR** |
| 17 | 71 | **NQR** |
| 19 | 79 | **NQR** |
| 23 | 95 | divides m |
| 26 | 107 | QR |
| 29 | 119 | QR |

**Key insight**: If 5 | x_k for k ∈ {7, 14, 17, 19}, then Obs_k fails.

---

### Prime 7
- (7/23): (23/7) = (2/7) = 1, (23-1)/2 = 11 odd → (7/23) = -1 → NQR
- (7/31): (31/7) = (3/7) = -1, (31-1)/2 = 15 odd → (7/31) = 1 → QR
- (7/39): (7/3) = 1, (7/13) = (13/7) × (-1)^3 = (6/7) × (-1) = (-1) × (-1) = 1 → QR
- (7/47): (47/7) = (5/7) = -1, (47-1)/2 = 23 odd → (7/47) = 1 → QR
- (7/59): (59/7) = (3/7) = -1, (59-1)/2 = 29 odd → (7/59) = 1 → QR
- (7/71): (71/7) = (1/7) = 1, (71-1)/2 = 35 odd → (7/71) = -1 → NQR
- (7/79): (79/7) = (2/7) = 1, (79-1)/2 = 39 odd → (7/79) = -1 → NQR
- (7/95): (7/5) = -1, (7/19) = (19/7) × (-1)^3 = (5/7) × (-1) = (-1) × (-1) = 1 → product = -1 → NQR
- (7/107): (107/7) = (2/7) = 1, (107-1)/2 = 53 odd → (7/107) = -1 → NQR
- (7/119): 7 | 119 → divides m

| k | m_k | (7/m_k) |
|---|-----|---------|
| 5 | 23 | **NQR** |
| 7 | 31 | QR |
| 9 | 39 | QR |
| 11 | 47 | QR |
| 14 | 59 | QR |
| 17 | 71 | **NQR** |
| 19 | 79 | **NQR** |
| 23 | 95 | **NQR** |
| 26 | 107 | **NQR** |
| 29 | 119 | divides m |

**Key insight**: If 7 | x_k for k ∈ {5, 17, 19, 23, 26}, then Obs_k fails.

---

## Summary Table: Which k values are "broken" by which small primes

A prime q "breaks" k means: if q | x_k, then Obs_k is false (q is NQR mod m_k).

| q | k values where q is NQR mod m_k |
|---|---------------------------------|
| 2 | 14, 23 |
| 3 | 7, 19 |
| 5 | 7, 14, 17, 19 |
| 7 | 5, 17, 19, 23, 26 |
| 11 | (need to compute) |
| 13 | (need to compute) |

---

## The Covering Strategy

The x_k values are: n, n+2, n+4, n+6, n+9, n+12, n+14, n+18, n+21, n+24

Among any 25 consecutive integers, we are guaranteed divisibility by small primes.

**Key observation**:
- At least one of {n, n+2, n+4, ...} is even (divisible by 2)
- At least one is divisible by 3
- At least one is divisible by 5
- At least one is divisible by 7

The question is whether these divisibilities hit the "breaking" k values.

For example:
- If 2 | x_14 or 2 | x_23, that k is "safe" (Obs fails)
- If 3 | x_7 or 3 | x_19, that k is "safe"
- If 5 | x_7 or 5 | x_14 or 5 | x_17 or 5 | x_19, that k is "safe"
- If 7 | x_5 or 7 | x_17 or 7 | x_19 or 7 | x_23 or 7 | x_26, that k is "safe"

---

## Critical Computation Needed

Compute: For which residue classes of n (mod lcm(2,3,5,7) = 210) is at least one k "broken" by a small prime factor?

If the answer is "all of them", then we have a proof via finite case analysis on n mod 210.
