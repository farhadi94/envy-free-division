"""Independent finite stress checks for Appendix F, not a continuous proof.

Only this review's files are written. Fractions avoid tolerance artifacts.
"""
from fractions import Fraction as F
from itertools import permutations, product
from collections import Counter, deque
import json
import random


def check_transport():
    counts = Counter()
    k, i = 3, 0
    for orientation in ("cake", "chores"):
        sign = 1 if orientation == "cake" else -1
        for old in product(range(4), repeat=k):
            if any(sign * (old[i] - old[j]) < 0 for j in range(k)):
                continue
            for additions in product(range(3), repeat=k):
                for residue in range(3):
                    old_residue = sum(additions) + residue
                    targets = {
                        j for j in range(k) if j != i
                        and sign * (old[i] - old[j]) >= old_residue
                    }
                    for f in permutations(range(k)):
                        new = [0] * k
                        for j in range(k):
                            new[f[j]] = old[j] + additions[j]
                        if any(sign * (new[i] - new[j]) < 0 for j in range(k)):
                            continue
                        new_targets = {
                            j for j in range(k) if j != i
                            and sign * (new[i] - new[j]) >= residue
                        }
                        counts[orientation + "_EF_rows"] += 1
                        assert len(new_targets) >= len(targets)
                        if residue:
                            assert all(f[j] != i and f[j] in new_targets for j in targets)
                        else:
                            assert len(new_targets) == k - 1
                            if any(f[j] == i for j in targets):
                                counts[orientation + "_zero_residue_self_images"] += 1
    return dict(counts)


def path(graph, source, target):
    queue = deque([(source, [source])])
    seen = {source}
    while queue:
        v, p = queue.popleft()
        if v == target:
            return p
        for w in sorted(graph[v]):
            if w not in seen:
                seen.add(w)
                queue.append((w, p + [w]))
    raise AssertionError("Graph not strongly connected")


def check_transfer():
    rng = random.Random(472962)
    tau, theta = F(1, 8), F(1, 32)
    ratio, first = 8 / tau, 2 / theta
    counts = Counter()
    for k in range(3, 7):
        pool = [F(0), theta, theta / 64, theta / 4096,
                F(3, 64) / first, F(2) / first, F(1), F(4)]
        for _ in range(2000):
            graph = [{(v + 1) % k} for v in range(k)]
            for v in range(k):
                for w in range(k):
                    if v != w and rng.random() < 0.15:
                        graph[v].add(w)
            d = [[rng.choice(pool) if i != j else F(0)
                  for j in range(k)] for i in range(k)]
            a, j = rng.sample(range(k), 2)
            d[a][j] = rng.choice([theta, 2 * theta, F(1)])
            factors = [first * ratio ** e for e in range(k)]
            forbidden = [sum(F(3, 8) * tau < G * d[i][j] < 2
                             for G in factors) for i in range(k)]
            assert all(c <= 1 for c in forbidden) and forbidden[j] == 0
            G = next(G for G in factors if not any(
                F(3, 8) * tau < G * d[i][j] < 2 for i in range(k)))
            rho = [rng.choice([F(3, 8), F(11, 16), F(1)]) / G
                   for _ in range(k)]
            small = [d[i][j] <= tau * rho[i] for i in range(k)]
            assert not small[a] and small[j]
            assert all(small[i] or d[i][j] >= 2 * rho[i] for i in range(k))
            crossing_path = path(graph, a, j)
            b, h = next((v, w) for v, w in zip(crossing_path, crossing_path[1:])
                        if not small[v] and small[w])
            alpha = list(range(k))
            if h == j:
                branch = "identity_crossing"
            else:
                return_path = path(graph, j, h)
                bad = [(v, w) for v, w in zip(return_path, return_path[1:])
                       if d[v][w] > tau * rho[v]]
                if not bad:
                    branch = "nonidentity_rotation"
                    for v, w in zip(return_path, return_path[1:]):
                        alpha[v] = w
                    alpha[h] = j
                else:
                    branch = "second_shrink"
                    b, h = bad[0]
                    second = 2 / tau
                    assert second <= factors[-1]
                    rho = [r * rng.choice([F(3, 8), F(11, 16), F(1)]) / second
                           for r in rho]
            counts[branch] += 1
            assert sorted(alpha) == list(range(k))
            assert h in graph[b]
            assert all(d[i][alpha[i]] <= tau * rho[i] for i in range(k))
            assert d[b][alpha[h]] >= 2 * rho[b]
    return dict(counts)


def check_parameters():
    checked = []
    for n in (3, 4, 5, 10, 100, 1000):
        s = 2 ** 40 * max(4, n)
        ell = (2 * s - 1).bit_length()
        lam, L = F(s * s, 8), s ** 5 * ell
        q, eta, m = F(1, s ** 8 * ell), F(1, s ** 17 * ell ** 2), s ** 18 * ell ** 2
        tau, N = F(1, 4 * s ** 10 * ell), 1024 * s ** 10 * ell
        eta_R, b = 2 * eta / q, lam / (4 * N)
        theta = tau / (768 * m)
        for k in {3, n}:
            assert 2 * k / eta <= m
            assert k ** 3 * L * eta < F(1, 2)
            assert k ** 2 * L * eta_R <= F(1, 4 * s * s)
            assert 2 * lam * eta_R <= F(1, 4 * s * s)
            assert k ** 2 <= lam / 2
            assert F(k * k, s * s) < F(1, 16)
            assert k * lam * eta_R < F(1, 16)
            assert k ** 3 * L * eta + 3 * q / 2 < F(1, 4)
            assert eta * m == s and q * b * m == F(s * s, 32768)
            assert 2 * tau / q == F(1, 2 * s * s)
            p_mass, p_count, p_parent = 4 * k * eta / q, 2 * q * m / N, q * k ** 3 * L
            # Use the proved ln(2k) <= ell, avoiding floating logarithms.
            p_cycle = F(k * k * (k - 1), L + 1) * (12 * lam * ell + 1)
            p_int = F(16 * k * (k - 1), 1) * (1 + b) / (q * b * (m + 1))
            p_est = 8 * k * eta_R * N / lam
            assert p_mass + p_count + p_parent + p_cycle + p_int + p_est < F(1, 64)
            assert 2 / theta <= s ** 32 and 8 / tau <= s ** 12
            assert 4 * k * k / tau <= s ** 14
            assert k ** 3 * (32 * k * ell) <= m
        checked.append(n)
    return {"original_populations": checked}


if __name__ == "__main__":
    print(json.dumps({"status": "passed", "transport": check_transport(),
                      "transfer": check_transfer(), "parameters": check_parameters(),
                      "scope_limit": "Finite stress checks only; no continuous or probability theorem verified."},
                     indent=2))
