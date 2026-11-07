#!/usr/bin/env python3
"""Exact rational checks of prescribed extremal roots, including endpoint targets."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import random


def value(profile, x):
    for (a, fa), (b, fb) in zip(profile, profile[1:]):
        if a <= x <= b:
            return fa + (fb - fa) * (x - a) / (b - a)
    raise ValueError(x)


def roots(profile, a, b, t):
    level = value(profile, a) + t
    candidates = []
    for (l, fl), (r, fr) in zip(profile, profile[1:]):
        u, v = max(l, a), min(r, b)
        if u > v:
            continue
        fu, fv = value(profile, u), value(profile, v)
        if fu == fv:
            if fu == level:
                candidates.extend([u, v])
        elif min(fu, fv) <= level <= max(fu, fv):
            candidates.append(u + (level - fu) * (v - u) / (fv - fu))
    assert candidates
    return min(candidates), max(candidates)


def answer(profile, a, b, t, upward):
    first, last = roots(profile, a, b, t)
    nonnegative = value(profile, b) >= value(profile, a)
    return last if nonnegative == upward else first


def perturb(profile, a, b, root, upward, rng):
    knots = sorted({x for x, _ in profile} | {root} |
                   {(l + r) / 2 for (l, _), (r, _) in zip(profile, profile[1:])})
    protected = {Q(0), Q(1), a, b, root}
    sign = 1 if upward else -1
    return [(x, value(profile, x) +
             (0 if x in protected else sign * rng.randrange(1, 1001))) for x in knots]


def main():
    rng = random.Random(902101)
    checks = 0
    endpoints = 0
    negative_brackets = 0
    zero_brackets = 0
    reflected = 0
    grid = [Q(j, 6) for j in range(7)]
    for _ in range(18):
        profile = list(zip(grid, [Q(0)] + [Q(rng.randrange(-6, 7)) for _ in range(5)] + [Q(1)]))
        for ia, a in enumerate(grid):
            for b in grid[ia:]:
                B = value(profile, b) - value(profile, a)
                for fraction in [Q(0), Q(1, 4), Q(1, 2), Q(3, 4), Q(1)]:
                    t = B * fraction
                    assert min(0, B) <= t <= max(0, B)
                    for upward in [False, True]:
                        root = answer(profile, a, b, t, upward)
                        changed = perturb(profile, a, b, root, upward, rng)
                        assert value(changed, a) == value(profile, a)
                        assert value(changed, b) == value(profile, b)
                        assert value(changed, root) == value(profile, root)
                        assert answer(changed, a, b, t, upward) == root
                        checks += 1
                        endpoints += t in {0, B}
                        negative_brackets += B < 0
                        zero_brackets += B == 0
                    reverse = [(1 - x, 1 - f) for x, f in reversed(profile)]
                    assert min(0, B) <= B - t <= max(0, B)
                    assert answer(reverse, 1 - b, 1 - a, B - t, False) == \
                        1 - answer(profile, a, b, t, True)
                    reflected += 1

    uniform = [(Q(0), Q(0)), (Q(1), Q(1))]
    changed = [(Q(0), Q(0)), (Q(1, 8), Q(1, 8)), (Q(1, 4), Q(5, 4)),
               (Q(3, 8), Q(3, 8)), (Q(1), Q(1))]
    assert roots(uniform, Q(0), Q(1), Q(1, 2))[0] == Q(1, 2)
    assert roots(changed, Q(0), Q(1), Q(1, 2))[0] == Q(1, 6)
    assert value(changed, Q(1, 2)) == Q(1, 2)

    source = Path(__file__)
    result = {
        "status": "passed",
        "arithmetic": "exact fractions; 18 signed net-one piecewise-linear cumulatives",
        "preserved_root_checks": checks,
        "endpoint_target_checks": endpoints,
        "negative_total_bracket_checks": negative_brackets,
        "zero_total_bracket_checks": zero_brackets,
        "reflection_checks": reflected,
        "pure_leftmost_counterexample": {
            "old_first_root": "1/2", "new_first_root": "1/6",
            "old_root_equation_still_true": True,
            "positive_then_negative_pulse_mass": "1",
        },
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "scope": "Finite exact checks of the root interfaces; the continuous root-preservation proof is in Lean. This does not test the complete adaptive probability construction.",
    }
    output = source.with_suffix(".json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
