"""
Experiment 55 (Simple): Test the key hypothesis directly.

For each depth m, check what fraction of E∩X cylinders have floor(w/2) containing 0.
"""

from itertools import product

def has_entry_witness(prefix):
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            return True
    return False

def has_exit_witness(prefix):
    for i in range(len(prefix) - 1):
        if prefix[i] == '5' and prefix[i+1] in '1234':
            return True
    return False

print("Depth | E∩X Count | floor(w/2) has 0 | % blocked")
print("-" * 55)

for depth in range(3, 10):
    total = 0
    blocked = 0

    for digits in product(range(1, 10), repeat=depth):
        cyl = ''.join(str(d) for d in digits)
        if has_entry_witness(cyl) and has_exit_witness(cyl):
            total += 1
            half = int(cyl) // 2
            if '0' in str(half):
                blocked += 1

    if total > 0:
        pct = 100 * blocked / total
        print(f"  {depth}   |  {total:>8}  |     {blocked:>8}     |  {pct:5.1f}%")
