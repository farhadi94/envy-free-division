"""Independent finite composition diagnostics; no manuscript/author code imports."""

from fractions import Fraction as F
from itertools import permutations, product
import hashlib
import json
from pathlib import Path
import random


stats = {
    "transport_states": 0,
    "positive_residue_states": 0,
    "zero_residue_states": 0,
    "strict_new_target_states": 0,
    "shrink_transfer_cases": 0,
    "identity_first": 0,
    "rotation_first": 0,
    "second_shrink": 0,
}

for n, alphabet in [(3, range(3)), (4, range(2))]:
    for mask in range(1, 1 << n):
        active = [i for i in range(n) if mask >> i & 1]
        frozen = set(range(n)) - set(active)
        for perm in permutations(active):
            f = list(range(n))
            for j, to in zip(active, perm):
                f[j] = to
            for i in range(n):
                for w in product(alphabet, repeat=n):
                    for cake in (True, False):
                        oldg = lambda j: (w[i] - w[j]) if cake else (w[j] - w[i])
                        if any(oldg(j) < 0 for j in range(n)):
                            continue
                        for ab in product(alphabet, repeat=len(active)):
                            b = [0] * n
                            for j, value in zip(active, ab):
                                b[j] = value
                            for newr in alphabet:
                                oldr = newr + sum(b)
                                if cake and i in frozen and any(
                                    oldg(j) < oldr for j in active
                                ):
                                    continue
                                if not cake and i in active and any(
                                    oldg(j) < oldr for j in frozen
                                ):
                                    continue
                                z = [0] * n
                                for j in range(n):
                                    z[f[j]] = w[j] + b[j]
                                newg = lambda j: (z[i] - z[j]) if cake else (z[j] - z[i])
                                # Supply active EF only; derive the global conclusions.
                                if i in active and any(newg(j) < 0 for j in active):
                                    continue
                                assert all(newg(j) >= 0 for j in range(n))
                                if cake and i in frozen:
                                    assert all(newg(j) >= newr for j in active)
                                if not cake and i in active:
                                    assert all(newg(j) >= newr for j in frozen)
                                old = {j for j in range(n) if j != i and oldg(j) >= oldr}
                                new = {j for j in range(n) if j != i and newg(j) >= newr}
                                assert len(new) >= len(old)
                                if newr > 0:
                                    assert all(f[j] != i and f[j] in new for j in old)
                                    stats["positive_residue_states"] += 1
                                    for h in active:
                                        if h != i and h not in old and newg(f[h]) > newr:
                                            assert len(new) >= len(old) + 1
                                            stats["strict_new_target_states"] += 1
                                else:
                                    assert len(new) == n - 1
                                    stats["zero_residue_states"] += 1
                                stats["transport_states"] += 1


def path(adj, a, b):
    queue = [(a, [a])]
    seen = {a}
    for v, prefix in queue:
        if v == b:
            return prefix
        for q in sorted(adj[v]):
            if q not in seen:
                seen.add(q)
                queue.append((q, prefix + [q]))
    raise AssertionError("not strongly connected")


seed = 2026110701
rng = random.Random(seed)
tau, theta = F(1, 8), F(1, 16)
for k in range(3, 9):
    for _ in range(800):
        adj = [{(i + 1) % k} for i in range(k)]
        for i in range(k):
            for j in range(k):
                if i != j and rng.randrange(4) == 0:
                    adj[i].add(j)
        totals = [F(rng.choice([1, 2, 5, 13]), rng.choice([1, 3, 7])) for i in range(k)]
        d = [
            [
                F(0) if i == j else totals[i] * F(rng.choice([0, 0, 1, 2, 7]), 16)
                for j in range(k)
            ]
            for i in range(k)
        ]
        cert = [
            (i, j)
            for i in range(k)
            for j in range(k)
            if i != j and d[i][j] >= theta * totals[i]
        ]
        if not cert:
            continue
        a, j = rng.choice(cert)
        x = [d[i][j] / totals[i] for i in range(k)]
        factors = [(2 / theta) * (8 / tau) ** e for e in range(k)]
        safe = [g for g in factors if all(not (3 * tau / 8 < g * x[i] < 2) for i in range(k))]
        assert safe
        g = safe[0]
        rho = [
            totals[i] * rng.choice([F(3, 8), F(1, 2), F(7, 8), F(1)]) / g
            for i in range(k)
        ]
        large = [d[i][j] >= 2 * rho[i] for i in range(k)]
        small = [d[i][j] <= tau * rho[i] for i in range(k)]
        assert all(large[i] or small[i] for i in range(k)) and large[a] and small[j]
        route = path(adj, a, j)
        b, h = next((u, v) for u, v in zip(route, route[1:]) if large[u] and small[v])
        alpha = list(range(k))
        if h == j:
            stats["identity_first"] += 1
        else:
            route = path(adj, j, h)
            bad = [(u, v) for u, v in zip(route, route[1:]) if d[u][v] > tau * rho[u]]
            if bad:
                b, h = bad[0]
                rho = [r * rng.choice([F(3, 8), F(1, 2), F(1)]) / (2 / tau) for r in rho]
                stats["second_shrink"] += 1
            else:
                for u, v in zip(route, route[1:]):
                    alpha[u] = v
                alpha[h] = j
                stats["rotation_first"] += 1
        assert sorted(alpha) == list(range(k))
        assert all(d[i][alpha[i]] <= tau * rho[i] for i in range(k))
        assert h in adj[b] and b != h and d[b][alpha[h]] >= 2 * rho[b]
        assert all(r > 0 for r in rho)
        stats["shrink_transfer_cases"] += 1

assert all(
    stats[key] > 0
    for key in [
        "identity_first", "rotation_first", "second_shrink", "zero_residue_states",
        "strict_new_target_states",
    ]
)
source = Path(__file__)
print(json.dumps({
    "status": "PASS",
    "seed": seed,
    "counts": stats,
    "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "scope": "Independent integer row transport enumeration and exact rational two-shrink transfer. No author code or earlier backend imported; not a continuous-protocol proof.",
}, indent=2))
