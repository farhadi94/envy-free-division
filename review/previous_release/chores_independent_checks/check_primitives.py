"""Independent rational stress checks; not a proof of the continuous protocol.

Uses no manuscript/Lean implementation. A parent's coordinate is retained
prefix length for Core, or retained suffix length for SubCore. Profiles are
piecewise constant in that coordinate. Persistent records implement the
specified lexicographic insertion, including arbitrary plateau roots.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
import json
import math
import random


@dataclass(eq=False)
class Record:
    x: F
    values: tuple
    virtual: bool = False


class Parent:
    def __init__(self, pid, weights, offsets, mode, bottoms, rng):
        self.pid, self.weights, self.offsets = pid, weights, offsets
        self.mode, self.rng = mode, rng
        self.rows, self.cells = len(weights), len(weights[0])
        self.requests = self.cuts = 0
        empty = Record(F(0), tuple((self.primary(i, F(0)), F(0)) for i in range(self.rows)))
        whole = Record(F(1), tuple((self.primary(i, F(1)), F(1)) for i in range(self.rows)))
        self.records = [empty, whole]
        if mode == "affine":
            self.records.insert(0, Record(F(0), tuple((bottoms[i], F(0)) for i in range(self.rows)), True))
        self.empty, self.whole, self.bottom = empty, whole, self.records[0]

    def raw(self, i, x):
        return sum((w * max(F(0), min(F(1), x * self.cells - j)) for j, w in enumerate(self.weights[i])), F(0))

    def primary(self, i, x):
        q = self.raw(i, x)
        if self.mode == "core":
            return q
        q -= self.offsets[i]
        return max(F(0), q) if self.mode == "clipped" else q

    def rank(self, record):
        return self.records.index(record)

    def trim(self, i, target, cap):
        self.requests += 1
        assert self.bottom.values[i] <= target <= cap.values[i]
        for rec in self.records:
            if rec.values[i] == target:
                assert self.rank(rec) <= self.rank(cap)
                return rec
        j = next(j for j in range(1, len(self.records)) if self.records[j].values[i] > target)
        lo, hi = self.records[j - 1], self.records[j]
        if lo.values[i][0] == target[0] and not lo.virtual:
            x = lo.x
        elif hi.values[i][0] == target[0] and not hi.virtual:
            x = hi.x
        else:
            raw_target = target[0] + (self.offsets[i] if self.mode != "core" else 0)
            roots = []
            acc = F(0)
            for c, w in enumerate(self.weights[i]):
                if w == 0 and acc == raw_target:
                    roots.extend((F(c, self.cells), F(c + 1, self.cells)))
                elif w > 0 and acc <= raw_target <= acc + w:
                    roots.append((c + (raw_target - acc) / w) / self.cells)
                acc += w
            assert roots
            left, right = min(roots), max(roots)
            # Adversarially exercise left, right, and interior plateau roots.
            x = self.rng.choice([left, right, (left + right) / 2])
            assert lo.x <= x <= hi.x
            self.cuts += int(all(r.x != x or r.virtual for r in self.records))
        vals = []
        for row in range(self.rows):
            primary = self.primary(row, x)
            if row == i:
                secondary = target[1]
                assert primary == target[0]
            elif primary == lo.values[row][0] == hi.values[row][0]:
                secondary = (lo.values[row][1] + hi.values[row][1]) / 2
            elif primary == lo.values[row][0]:
                secondary = lo.values[row][1] + 1
            elif primary == hi.values[row][0]:
                secondary = hi.values[row][1] - 1
            else:
                secondary = F(0)
            value = (primary, secondary)
            assert lo.values[row] < value < hi.values[row]
            vals.append(value)
        rec = Record(x, tuple(vals))
        self.records.insert(j, rec)
        assert self.rank(rec) <= self.rank(cap)
        return rec


def check_ef(allocation, agents, caps=None, parents=None, benchmarks=None):
    assert len({p for p, _ in allocation.values()}) == len(agents)
    for i in agents:
        pi, ri = allocation[i]
        assert not ri.virtual
        for j in agents:
            assert ri.values[i] >= allocation[j][1].values[i]
        if benchmarks:
            assert ri.values[i] >= benchmarks[i]
        if caps:
            for p, cap in caps.items():
                if p not in {x[0] for x in allocation.values()}:
                    assert ri.values[i] >= cap.values[i]
            assert parents[pi].rank(ri) <= parents[pi].rank(caps[pi])
    if caps:
        assert any(rec is caps[p] for p, rec in allocation.values())


def subcore(agents, caps, parents, inherited, stats):
    assert len(agents) < len(caps)
    stats["calls"] += 1
    benchmarks = {i: inherited[i][1].values[i] for i in agents}
    for i in agents:
        p, r = inherited[i]
        assert parents[p].rank(r) <= parents[p].rank(caps[p])
        for j in agents:
            assert r.values[i] >= inherited[j][1].values[i]
    allocation = {}
    for t, newcomer in enumerate(agents, 1):
        active = agents[:t]
        favorite = max(caps, key=lambda p: (caps[p].values[newcomer], -p))
        if favorite not in {p for p, _ in allocation.values()}:
            allocation[newcomer] = favorite, caps[favorite]
            continue
        old = allocation.copy()
        contested = {p for p, _ in old.values()}
        uncontested = set(caps) - contested
        beta = {i: max(benchmarks[i], max(caps[p].values[i] for p in uncontested)) for i in active}
        trims = {p: {i: parents[p].trim(i, beta[i], caps[p]) for i in active if caps[p].values[i] >= beta[i]} for p in contested}
        chosen = {}
        for p in sorted(contested):
            assert trims[p]
            lowest = min(parents[p].rank(r) for r in trims[p].values())
            tied = [i for i, r in trims[p].items() if parents[p].rank(r) == lowest]
            inherited_owner = next((i for i in agents if inherited[i][0] == p), None)
            chosen[p] = inherited_owner if inherited_owner in tied else min(tied)
        selected = set(chosen.values())
        allocation = {}
        for p in sorted(chosen):
            i = chosen[p]
            allocation.setdefault(i, (p, trims[p][i]))
        while len(selected) < t - 1:
            recursive_caps = {}
            remaining = {}
            for p in contested:
                remaining[p] = {i: r for i, r in trims[p].items() if i not in selected}
                recursive_caps[p] = min(remaining[p].values(), key=parents[p].rank) if remaining[p] else caps[p]
            allocation = subcore(sorted(selected), recursive_caps, parents, allocation, stats)
            unused = contested - {p for p, _ in allocation.values()}
            available = [p for p in unused if remaining[p]]
            if not available:
                stats["chain_repairs"] += 1
                p = min(unused)
                old_owner = {p: i for i, (p, _) in old.items()}
                chain = [old_owner[p]]
                while chain[-1] in selected:
                    nxt = old_owner[allocation[chain[-1]][0]]
                    assert nxt not in chain
                    chain.append(nxt)
                for i in chain[:-1]:
                    assert old[i][1].values[i] == allocation[i][1].values[i]
                    allocation[i] = old[i]
                available = [old[chain[-1]][0]]
                assert remaining[available[0]]
            p = min(available)
            rec = recursive_caps[p]
            winner = min(i for i, r in remaining[p].items() if r is rec)
            allocation[winner] = p, rec
            selected.add(winner)
        outsider = next(i for i in active if i not in selected)
        p = max(uncontested, key=lambda p: (caps[p].values[outsider], -p))
        allocation[outsider] = p, caps[p]
        check_ef(allocation, active, caps, parents, {i: benchmarks[i] for i in active})
    check_ef(allocation, agents, caps, parents, benchmarks)
    return allocation


def prefix_dp(parents):
    n = len(parents)
    stored = {}
    for size in range(1, n + 1):
        for agents in combinations(range(n), size):
            for pieces in combinations(range(n), size):
                if size == 1:
                    stored[agents, pieces] = {agents[0]: (pieces[0], parents[pieces[0]].whole)}
                    continue
                success = None
                for i in agents:
                    for p in pieces:
                        smaller = stored[tuple(j for j in agents if j != i), tuple(q for q in pieces if q != p)]
                        target = min(rec.values[i] for _, rec in smaller.values())
                        rec = parents[p].whole if parents[p].whole.values[i] <= target else parents[p].trim(i, target, parents[p].whole)
                        trial = dict(smaller, **{})
                        trial[i] = p, rec
                        if all(trial[j][1].values[j] <= trial[h][1].values[j] for j in agents for h in agents):
                            success = trial
                            break
                    if success is not None:
                        break
                assert success is not None, (agents, pieces)
                assert any(r is parents[p].whole for p, r in success.values())
                stored[agents, pieces] = success
    result = stored[tuple(range(n)), tuple(range(n))]
    for i in range(n):
        assert all(result[i][1].values[i] <= result[j][1].values[i] for j in range(n))
    assert sum(p.requests for p in parents.values()) <= n*n*(math.comb(2*n-2, n-1)-1)


def main():
    rng = random.Random(2718281828)
    stats = {"seed": 2718281828, "core_profiles": 0, "subcore_profiles": {"clipped": 0, "affine": 0}, "calls": 0, "chain_repairs": 0, "record_insertions": 0, "cuts": 0}
    # Zeros, exact ties, zero-valued parents and three legal plateau policies.
    for n in range(2, 5):
        for trial in range(60):
            weights = [[[F(rng.choice([0, 0, 0, 1, 1, 2, 4])) for _ in range(4)] for _ in range(n)] for _ in range(n)]
            parents = {p: Parent(p, weights[p], [F(0)]*n, "core", None, rng) for p in range(n)}
            prefix_dp(parents)
            stats["core_profiles"] += 1
            stats["record_insertions"] += sum(len(p.records)-2 for p in parents.values())
            stats["cuts"] += sum(p.cuts for p in parents.values())
    for mode in ["clipped", "affine"]:
        for k in range(1, 6):
            for trial in range(120):
                m = k + rng.choice([1, 1, 2, 4])
                weights = [[[F(rng.choice([0, 0, 1, 1, 2, 5])) for _ in range(5)] for _ in range(k)] for _ in range(m)]
                # Every fourth profile has long masked plateaus.
                if trial % 4 == 0:
                    for p in range(m):
                        for i in range(k):
                            for c in range(5):
                                if c != i % 5:
                                    weights[p][i][c] = F(0)
                offsets = [[F(rng.randrange(int(sum(weights[p][i])) + (1 if mode == "affine" else 7))) for i in range(k)] for p in range(m)]
                bottoms = [-1-max(offsets[p][i] for p in range(m)) for i in range(k)]
                parents = {p: Parent(p, weights[p], offsets[p], mode, bottoms, rng) for p in range(m)}
                caps = {p: parents[p].whole for p in parents}
                inherited = {i: (i, parents[i].bottom) for i in range(k)}
                allocation = subcore(list(range(k)), caps, parents, inherited, stats)
                for i, (_, rec) in allocation.items():
                    assert rec.values[i][0] >= 0
                assert sum(p.requests for p in parents.values()) <= 2**(k+1)-2*k-2
                stats["subcore_profiles"][mode] += 1
                stats["record_insertions"] += sum(len(p.records)-(3 if mode == "affine" else 2) for p in parents.values())
                stats["cuts"] += sum(p.cuts for p in parents.values())
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
