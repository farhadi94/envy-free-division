#!/usr/bin/env python3
"""Exact rational stress test of the moving-frontier replay interface.

This tests finite deterministic transcript constructions. It is not evidence
of a random-tape-independent hard input for a randomized protocol.
"""

from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from random import Random
import json


def val(knots, row, x):
    for k in range(len(knots) - 1):
        a, b = knots[k:k + 2]
        if a <= x <= b:
            return row[k] + (row[k + 1] - row[k]) * (x - a) / (b - a)
    raise AssertionError((knots, x))


def first_root(knots, row, a, b, t):
    target = val(knots, row, a) + t
    grid = sorted({a, b, *(x for x in knots if a < x < b)})
    for k, x in enumerate(grid):
        y = val(knots, row, x)
        if y == target:
            return x
        if k + 1 < len(grid):
            z = grid[k + 1]
            w = val(knots, row, z)
            if min(y, w) < target < max(y, w):
                return x + (target - y) * (z - x) / (w - y)
    raise AssertionError((a, b, t, target))


def answer(knots, rows, query):
    kind, i, a, b, t = query
    total = val(knots, rows[i], b) - val(knots, rows[i], a)
    if kind == 'Eval':
        return total
    assert min(Q(0), total) <= t <= max(Q(0), total)
    return first_root(knots, rows[i], a, b, t)


def check_invariant(knots, rows, alpha):
    K = 1 + 1 / alpha
    for row in rows:
        assert row[0] == 0 and row[-1] == 1
        assert all(y < 1 for y in row[:-1])
        assert row[-2] < row[-1]
    for c in range(len(knots) - 2):
        increments = [row[c + 1] - row[c] for row in rows]
        positive = [i for i, p in enumerate(increments) if p > 0]
        assert len(positive) <= 1
        if positive:
            j = positive[0]
            assert all(i == j or z <= -K * increments[j]
                       for i, z in enumerate(increments))


def run(seed, n, alpha, counters):
    rng = Random(seed)
    knots = [Q(0), Q(1)]
    rows = [[Q(0), Q(1)] for _ in range(n)]
    history = []
    K = 1 + 1 / alpha
    for step in range(24):
        j = rng.randrange(n)
        a, b = sorted([Q(rng.randrange(17), 16), Q(rng.randrange(17), 16)])
        if step % 6 == 0:
            b = Q(1)
        if step % 11 == 0:
            a = b = Q(1)
        total = val(knots, rows[j], b) - val(knots, rows[j], a)
        kind = 'Eval' if step % 5 == 1 else 'Cut'
        fraction = rng.choice([Q(0), Q(1, 3), Q(1, 2), Q(2, 3), Q(1)])
        t = total if step % 6 == 0 else fraction * total
        query = (kind, j, a, b, t)
        reply = answer(knots, rows, query)
        if kind == 'Cut':
            counters['positive_targets' if t > 0 else
                     'negative_targets' if t < 0 else 'zero_targets'] += 1
            counters['terminal_replies'] += (reply == 1)
            counters['nonzero_starts'] += (a > 0)
        history.append((query, reply))
        l = knots[-2]
        coordinates = [a, b] + ([reply] if kind == 'Cut' else [])
        h = (max([l] + [x for x in coordinates if x < 1]) + 1) / 2
        p = (1 - rows[j][-2]) / (1 - l)
        new_rows = []
        for i, row in enumerate(rows):
            level = val(knots, row, h) if i == j else row[-2] - K * p * (h - l)
            new_rows.append(row[:-1] + [level, Q(1)])
        rows = new_rows
        knots = knots[:-1] + [h, Q(1)]
        check_invariant(knots, rows, alpha)
        for old_query, old_reply in history:
            assert answer(knots, rows, old_query) == old_reply
            counters['replayed_queries'] += 1

    # Arbitrary rational fractional ownership of every resolved cell,
    # realized by interval subdivisions; the remaining tail stays whole.
    for _ in range(40):
        owner = rng.randrange(n)
        shares = []
        for c in range(len(knots) - 2):
            raw = [rng.randrange(1, 10) for _ in range(n)]
            shares.append([Q(x, sum(raw)) for x in raw])
        shares.append([Q(j == owner) for j in range(n)])
        table = [[sum((rows[i][c + 1] - rows[i][c]) * shares[c][j]
                      for c in range(len(shares)))
                  for j in range(n)] for i in range(n)]
        nonowners = [i for i in range(n) if i != owner]
        for i_index, i in enumerate(nonowners):
            for k in nonowners[i_index + 1:]:
                pair_score = (alpha * table[i][owner] - table[i][i] +
                              alpha * table[k][owner] - table[k][k]) / 2
                assert pair_score >= alpha
                counters['weighted_pair_checks'] += 1
        assert max(alpha * table[i][owner] - table[i][i]
                   for i in nonowners) >= alpha
        counters['fragmented_allocations'] += 1
    counters['finite_profiles'] += 1


if __name__ == '__main__':
    counters = dict.fromkeys([
        'positive_targets', 'negative_targets', 'zero_targets',
        'terminal_replies', 'nonzero_starts', 'replayed_queries',
        'weighted_pair_checks', 'fragmented_allocations', 'finite_profiles'
    ], 0)
    for n in [3, 4, 6]:
        for alpha in [Q(1), Q(1, 2), Q(1, 3)]:
            for seed in range(4):
                run(seed, n, alpha, counters)
    receipt = {
        'status': 'passed',
        'arithmetic': 'exact fractions.Fraction throughout',
        'counts': counters,
        'scope': 'Finite deterministic transcript replay and weighted-cell checks only; no randomized lower bound.',
        'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
