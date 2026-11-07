#!/usr/bin/env python3
"""Independent exact-arithmetic probes; not a proof of the continuous theorem."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import math
import random

out = Path(__file__).resolve().parent
counts = {}
alphas = [F(1, 100), F(1, 3), F(1, 2), F(2, 3), F(1)]
grid = [F(k, 3) for k in range(-30, 31)]

def relative(x, y, a):
    return y - x <= (1 - a) * max(abs(x), abs(y))

count = 0
for a, x, y in product(alphas, grid, grid):
    threshold = a * y if y >= 0 else y / a
    assert relative(x, y, a) == (x >= threshold)
    if x >= y:
        assert relative(x, y, a)
    count += 1
for a, y in product(alphas, grid):
    threshold = a * y if y >= 0 else y / a
    for x in [threshold - F(1, 1000), threshold, threshold + F(1, 1000)]:
        assert relative(x, y, a) == (x >= threshold)
        count += 1
counts['signed_pair_equivalence_cases'] = count

count = 0
row_grid = [F(k, 2) for k in range(-5, 6)]
for a, row in product(alphas, product(row_grid, repeat=3)):
    if sum(row) <= 0:
        continue
    for own in range(3):
        rel = all(relative(row[own], y, a) for y in row)
        cake = all(row[own] >= a * y for y in row)
        assert rel == cake
        if rel:
            assert row[own] >= a * sum(row) / (2 + a) > 0
        count += 1
counts['positive_total_row_cases'] = count
assert relative(F(-1), F(-1), F(1, 2))
assert not F(-1) >= F(1, 2) * F(-1)
counts['positive_total_hypothesis_necessary_example'] = {
    'row': [-1, -1, -1], 'alpha': '1/2',
    'relative_EF': True, 'usual_cake_comparisons': False,
}

rng = random.Random(20261107)
coarse_count = 0
for n in [3, 4]:
    for a in alphas:
        rows = [[F(1)] for _ in range(n)]
        for stage in range(5):
            m = len(rows[0])
            for owners in product(range(n), repeat=m):
                table = [[sum(rows[i][k] for k in range(m) if owners[k] == j)
                          for j in range(n)] for i in range(n)]
                assert max(a * table[i][j] - table[i][i]
                           for i in range(n) for j in range(n)) >= a
                coarse_count += 1
            if stage == 4:
                break
            distinguished = stage % n
            cell = rng.randrange(m)
            left = [F(rng.randint(-30, 30), 3) for _ in range(n)]
            selected = [i for i in range(n) if i != distinguished][:2]
            for i in selected:
                H = sum(abs(rows[i][k]) for k in range(m) if k != cell)
                M = max(F(0), ((1 + a) * H + a) / a - left[i],
                        rows[i][cell] - left[i]) + 1
                left[i] += M
            rows = [row[:cell] + [left[i], row[cell] - left[i]] + row[cell+1:]
                    for i, row in enumerate(rows)]
            assert all(sum(row) == 1 for row in rows)
counts['coarse_allocation_assignments_after_insertions'] = coarse_count

def pulse(mass, pos, neg, owner):
    return mass * ((pos == owner) - (neg == owner))

def correct(table, a, eps):
    n = len(table)
    return all(a * table[i][j] - table[i][i] <= eps
               for i in range(n) for j in range(n))

pulse_count = 0
base_tables = [
    [[F(1, 3)] * 3 for _ in range(3)],
    [[F(10), F(-20), F(11)], [F(-5), F(1), F(5)], [F(3), F(0), F(-2)]],
    [[F(1), F(0), F(0)], [F(1), F(0), F(0)], [F(1), F(0), F(0)]],
]
for a, base in product(alphas, base_tables):
    for eps in [F(0), a / 2, a * F(99, 100)]:
        T = max(sum(abs(x) for x in row) for row in base)
        masses = []
        for _ in range(3):
            M = 2 / a * (T + sum(masses) + eps + 1)
            assert a * M > (1 + a) * (T + sum(masses)) + eps
            masses.append(M)
        for labels in product(range(3), repeat=6):
            pos, neg = labels[:3], labels[3:]
            table = [[base[i][j] + sum(pulse(masses[r], pos[r], neg[r], j)
                                         for r in range(3))
                      for j in range(3)] for i in range(3)]
            assert all(sum(row) == 1 for row in table)
            separated = [r for r in range(3) if pos[r] != neg[r]]
            if separated:
                r = max(separated)
                assert not correct(table, a, eps)
                for i in range(3):
                    if i != pos[r]:
                        assert a * table[i][pos[r]] - table[i][i] > eps
            else:
                assert table == base
            if correct(table, a, eps):
                assert correct(base, a, eps) and not separated
            pulse_count += 1
counts['pure_pulse_owner_pattern_cases'] = pulse_count

count = 0
for a in alphas:
    for h in [0, 1, 5, 100]:
        for eps_ratio in [0, .5, .99]:
            eps = float(a) * eps_ratio
            c = (float(a) - eps) / 4
            for delta in [.0001, .1, .999]:
                log_a = math.log(8 / delta)
                e = c * delta / (24 * (h + 1) * (log_a + 1))
                for Vratio in [1, 1.000001, 10, 1000]:
                    V = c * Vratio
                    L = math.ceil(V * log_a / c)
                    assert 3 * h * e * L / V < delta / 8
                    assert math.exp(-L * c / V) <= delta / 8 * (1 + 1e-12)
                    count += 1
counts['sampling_and_replay_budget_cases_float_smoke_test'] = count

result = {
    'status': 'passed',
    'scope': 'Finite exact-rational probes plus floating-point budget smoke tests; no continuous proof certification.',
    'counts': counts,
}
(out / 'independent_checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
