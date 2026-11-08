#!/usr/bin/env python3
"""Independent exact-rational stress checks for Appendix G.

These finite checks seek counterexamples to the elementary interfaces. They
are not a formalization of arbitrary adaptive protocols or probability spaces.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def words(counts, prefix=()):
    if not any(counts):
        yield prefix
    for i, count in enumerate(counts):
        if count:
            next_counts = list(counts)
            next_counts[i] -= 1
            yield from words(tuple(next_counts), prefix + (i,))


def integrated_correlation(word, w):
    """Exact E[1_{owner(X)=owner(X+U)}], X continuous, U~Unif[-w,w].

    Each letter owns a half-open cell of length 1/m. Circular correlation
    is linear between the shifts k/m, so the trapezoid integration is exact.
    """
    m = len(word)
    correlation = [
        F(sum(word[j] == word[(j + k) % m] for j in range(m)), m)
        for k in range(m + 1)
    ]
    area = F(0)
    for k in range(m):
        left, right = F(k, m), min(F(k + 1, m), w)
        if right <= left:
            break
        slope = m * (correlation[k + 1] - correlation[k])
        area += correlation[k] * (right - left) + slope * (right - left) ** 2 / 2
    return area / w


ownership_cases = 0
ownership_words = 0
for n, m in [(2, 8), (3, 6), (3, 9), (4, 8)]:
    windows = sorted({F(1, 4*m), F(1, 2*m), F(1, m), F(3, 2*m),
                      F(1, n), F(1, 4), F(1, 2)})
    for word in words((m // n,) * n):
        ownership_words += 1
        for w in windows:
            assert integrated_correlation(word, w) <= 1 / (2 * n * w)
            ownership_cases += 1


def circular_arc(center, h):
    lo, hi = center - h / 2, center + h / 2
    if lo < 0:
        return [(F(0), hi), (lo + 1, F(1))]
    if hi > 1:
        return [(F(0), hi - 1), (lo, F(1))]
    return [(lo, hi)]


def overlap(arc, a, b):
    return sum((max(F(0), min(b, hi) - max(a, lo)) for lo, hi in arc), F(0))


def value(x, y, h, a, b):
    return b - a + (overlap(circular_arc(x, h), a, b)
                    - overlap(circular_arc(y, h), a, b)) / 2


def avoids(arc, endpoints):
    return not any(lo <= t <= hi for lo, hi in arc for t in endpoints)


def cut_root(x, y, h, a, b, target):
    positive, negative = circular_arc(x, h), circular_arc(y, h)
    boundaries = sorted({a, b} | {t for arc in [positive, negative]
                                 for pair in arc for t in pair if a < t < b})
    accumulated = F(0)
    for lo, hi in zip(boundaries, boundaries[1:]):
        middle = (lo + hi) / 2
        density = 1 + F(any(l <= middle <= r for l, r in positive), 2) \
                    - F(any(l <= middle <= r for l, r in negative), 2)
        assert F(1, 2) <= density <= F(3, 2)
        if accumulated + density * (hi - lo) >= target:
            return lo + (target - accumulated) / density
        accumulated += density * (hi - lo)
    raise ValueError("Unavailable target")


replay_cases = 0
normalization_cases = 0
h = F(1, 64)
grid = [F(k, 8) for k in range(9)]
centers = [F(2*k+1, 64) for k in range(32)]
for x, y in product(centers, repeat=2):
    assert value(x, y, h, F(0), F(1)) == 1
    normalization_cases += 1
    positive, negative = circular_arc(x, h), circular_arc(y, h)
    for a, z in product(grid, repeat=2):
        if z < a:
            continue
        if ((a <= x <= z) == (a <= y <= z)
                and avoids(positive, [0, 1, a, z])
                and avoids(negative, [0, 1, a, z])):
            assert value(x, y, h, a, z) == z - a
            if a < 1:
                assert cut_root(x, y, h, a, F(1), z-a) == z
            replay_cases += 1

# Preserve a successful Cut while its bracket total changes in either direction.
for x, y in [(F(3, 5), F(9, 10)), (F(9, 10), F(3, 5))]:
    assert value(x, y, F(1, 32), F(0), F(3, 4)) != F(3, 4)
    assert cut_root(x, y, F(1, 32), F(0), F(3, 4), F(1, 4)) == F(1, 4)

# Include wrapped and partially overlapping pulses explicitly.
wrapped_overlap_cases = 0
for x, y in product([F(0), F(1,128), F(1,64), F(1,4), F(1,2), F(127,128)], repeat=2):
    pulse_width = F(1,16)
    assert value(x, y, pulse_width, F(0), F(1)) == 1
    for a, b in product(grid, repeat=2):
        if a <= b:
            assert abs(value(x, y, pulse_width, a, b) - (b-a)) <= pulse_width/2
    wrapped_overlap_cases += 1

# Compute bundle values directly for fragmented outputs and both orientations.
decoder_cases = 0
for n, m in [(2,8), (3,9), (4,8)]:
    selected_words = [tuple(k % n for k in range(m)),
                      tuple(k // (m//n) for k in range(m))]
    selected_words += list(word for index, word in enumerate(words((m//n,)*n)) if index < 5)
    for word in selected_words:
        for cell_x, cell_y in product(range(m), repeat=2):
            if word[cell_x] == word[cell_y]:
                continue
            x, y, pulse_width = F(2*cell_x+1,2*m), F(2*cell_y+1,2*m), F(1,8*m)
            values = [sum((value(x,y,pulse_width,F(k,m),F(k+1,m))
                           for k in range(m) if word[k] == owner), F(0))
                      for owner in range(n)]
            for observer in range(n):
                assert (max(values) > values[observer]) == (observer != word[cell_x])
                assert (min(values) < values[observer]) == (observer != word[cell_y])
                decoder_cases += 1

# The exact probability that an ordinary interval distinguishes the centers.
separation_cases = 0
for m in [2, 5, 12, 25]:
    for cells in range(m + 1):
        word = (1,) * cells + (0,) * (m - cells)
        for w in [F(1, 100), F(1, 12), F(1, 3), F(1, 2)]:
            # Binary ownership disagreement is precisely interval separation.
            probability = 1 - integrated_correlation(word, w)
            assert probability <= w
            separation_cases += 1

# Algebra at a rational grid, retaining baseline failure and terminal requests.
scalar_cases = 0
for n in [2, 3, 4, 8, 17, 100]:
    for p, w in product([F(1, 100), F(1, 5), F(2, 3), F(1)],
                        [F(1, 500), F(1, 20), F(1, 3), F(1, 2)]):
        A = (1 - F(1, n)) * (1 - 1 / (2*n*w))
        lower = (n*p - 1) / w - F(n-1, 2*n) / w**2
        assert F(n)/w * (p - (1-A)) == lower
        K = F(n)/w * (1-A)
        assert K == 1/w + F(n-1, 2*n) / w**2 and K >= 1
        for s in [p, (1+p)/2, F(1)]:
            for j in [F(0), (1-s)/2, 1-s]:
                q = max(F(0), F(n)/w * (p-s*(1-A)) - j)
                assert 1-s+s*A - w/n*(q+j) <= 1-p
                assert q >= lower
                scalar_cases += 1
        if n*p > 1:
            optimum = F(n-1) / (n*(n*p-1))
            constant = n*(n*p-1)**2 / (2*(n-1))
            assert (optimum <= F(1,2)) == (n*p >= 3-F(2,n))
            assert (n*p-1)/optimum - F(n-1,2*n)/optimum**2 == constant
            assert constant-lower == (n*(n*p-1)*w-(n-1))**2 / (2*n*(n-1)*w**2)

# An infinite-mean endpoint-count distribution still has vanishing width loss.
# P(N=2^k)=1/[k(k+1)] for k>=1; the infinite tail is summed exactly.
heavy_tail_bounds = {}
for m in [4, 16, 64, 256]:
    bound = sum((F(2**k, 2**(m+1)*k*(k+1)) for k in range(1, m+1)), F(0)) \
            + F(1, m+1)
    heavy_tail_bounds[str(m)] = float(bound)
assert all(a > b for a, b in zip(heavy_tail_bounds.values(), list(heavy_tail_bounds.values())[1:]))

result = {
    "status": "passed",
    "arithmetic": "fractions.Fraction exact rational arithmetic",
    "equal_length_owner_words": ownership_words,
    "continuous_owner_collision_checks": ownership_cases,
    "ordinary_interval_separation_checks": separation_cases,
    "normalized_two_pulse_profiles": normalization_cases,
    "exact_eval_and_cut_replay_checks": replay_cases,
    "changed_bracket_total_cut_examples": 2,
    "wrapped_and_overlapping_pulse_profiles": wrapped_overlap_cases,
    "cake_and_chore_decoder_checks": decoder_cases,
    "failure_retention_scalar_checks": scalar_cases,
    "infinite_mean_endpoint_count_loss_examples": heavy_tail_bounds,
    "limitation": "Finite stress checks; not a full proof of continuous randomized adaptive protocols."
}
destination = Path(__file__).with_name("checks_result.json")
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
