# A moving-frontier lower bound for prescribed first roots

Status: complete candidate argument, awaiting independent review and finite-lemma Lean checks. This is a new round-10 construction, not the bracket-sign selector argument.

## Claim

Fix n≥3, α>0, and ε<α. Let each agent have a signed, nonatomic, finite measure on [0,1], normalized to total1. The oracle answers Eval exactly and every legal bracketed Cut(a,b,t) by the **leftmost** root, where t is between0 and the bracket value. Allow arbitrary finite-union output shares and arbitrary query-free endpoints. For every measurable randomized protocol, every finite query horizon q, and every δ>0, there is a fixed profile of piecewise-constant densities for which

    P[the protocol returns an allocation satisfying
      α v_i(A_j) − v_i(A_i) ≤ ε for all i,j
      within q queries] ≤ δ.

The profile is fixed before the random tape is sampled. It has finitely many constant-density pieces and finite total variation. The number of pieces and total variation may depend on the protocol,q,δ. Consequently any protocol correct with probability at least p>0 on every profile has no uniform finite bound on expected queries. Pure rightmost follows by reflection with at most a factor2 overhead per Cut (one Eval to determine the bracket value, then the reflected Cut).

For the usual multiplicative conclusion use 0<α≤1 and the paper's already proved equivalence on positive-net profiles. Additive ε<1 follows by α=1. Exact EF is α=1,ε=0. There is no claim here for a common total-variation ceiling.

## 1. Profile class

Maintain a frontier ℓ<1. The resolved region [0,ℓ] is partitioned into finitely many intervals, and all densities are constant on each interval. Put K=1+1/α. Each resolved density vector d=(d_1,…,d_n) satisfies one of:

1. all d_i≤0; or
2. exactly one d_j=p>0, and d_i≤−Kp for every i≠j.

Every row has total1. On the tail (ℓ,1], every row has a strictly positive constant density. The cumulative functions F_i additionally satisfy

    F_i(x)<1 for all x<1, and F_i(1)=1.                 (barrier)

The initial profile is uniform density1 with ℓ=0 and no resolved cells.

## 2. Tail obstruction, with arbitrary earlier fragmentation

Suppose an allocation gives the whole tail to agent c. Let x_{J,k} be the fraction of resolved cell J assigned to k; these fractions exist for arbitrary measurable shares and sum to1 on each cell. Define

    E_c = (1/(n−1)) Σ_{i≠c} [α v_i(A_c)−v_i(A_i)].

Giving the entire domain to c makes E_c=α. Moving a fraction x of cell J from c to a different owner k subtracts

    x |J|/(n−1) · [α Σ_{i≠c} d_i + d_k].              (coefficient)

The bracketed coefficient is nonpositive. If every row is nonpositive, this is immediate. If the sole positive row is c, every term in the coefficient is nonpositive. If it is k, use another nonowner h (n≥3):

    α Σ_{i≠c} d_i+d_k ≤ (α+1)p−αKp=0.

If it is some j distinct from c,k, then

    α Σ_{i≠c} d_i+d_k ≤ αp−(α+1)Kp≤0.

Therefore E_c≥α. At least one nonowner i has αv_i(A_c)−v_i(A_i)≥α>ε. Thus no permitted approximation can leave the tail intact. Earlier resolved cells may be divided into arbitrarily many parts; this obstruction does not rely on coarse whole-cell allocations.

## 3. One-row refinement

Given a profile and an agent j, choose ℓ<r<1. Keep the entire density of row j unchanged. On (ℓ,r], every other row receives constant density −K d_j, where d_j>0 is row j's old tail density. On (r,1], give each other row its unique constant density restoring its total to1. This restoring density is positive because its cumulative value at r is

    F_i(ℓ)−K d_j(r−ℓ)<1.

The new resolved cell has the required density vector, and the remaining tail is positive. The barrier is preserved: row j is unchanged; every other row decreases from a value below1 and then increases linearly to1.

For a terminal output refinement, no row must be fixed: set every density on (ℓ,r] to−1 and again restore each total by a positive constant density on (r,1]. This creates an all-negative resolved cell and preserves the barrier.

All updates have finitely many pieces and finite real densities.

## 4. Replay of arbitrary legal first-root queries

A query is protected when all its interval endpoints and its returned root, if any, belong to [0,ℓ]∪{1}. Any later refinement keeps all cumulative values on [0,ℓ] and at1 unchanged. Thus all Eval values, Cut bracket values, and Cut legality are preserved.

Consider an old legal Cut with leftmost reply z. If z≤ℓ, the entire interval from its starting point to z is unchanged, so z remains the first root. If z=1, its bracket endpoint is1. The target absolute cumulative level is F_i(1)=1. The barrier says that this level is attained nowhere before1. Hence z=1 remains the first root after every refinement.

This includes zero targets and full-bracket targets. A zero target's first root is its starting point. An old root1 cannot have a negative target: its starting cumulative is strictly below1 unless the bracket is the degenerate point1. The degenerate query is unchanged directly. No assumption is made about the sign of other legal targets or bracket values.

When handling a new query to row j, first compute its answer on the current profile. The one-row refinement leaves row j unchanged everywhere, so this query and its answer remain valid. Choose the new frontier beyond its finitely many coordinates below1, making the query protected for every subsequent refinement.

## 5. Deterministic finite-transcript adversary

At each answered query, apply the one-row update after choosing a new frontier beyond every query coordinate below1. All earlier protected replies replay. If the protocol outputs a finite-union allocation, advance once more beyond every output endpoint below1 using the all-negative update. The remaining tail is assigned whole, so Section2 forces a violation. This rules out a uniform finite worst-case query bound for a deterministic protocol. It does not rule out a protocol that terminates after an input-dependent finite number of queries, and by itself it would not establish a fixed-input randomized result.

## 6. Fixed-input batch capture

Fix a random-tape probability space and the query cap q. For each fixed input, use the measurable kth-call descriptors supplied by the protocol model. If a kth real call exists, its descriptor records the query, its answered response, and the queried row. If it does not exist, use a virtual dummy descriptor Eval(1,0,0). This is an analytical description of a fixed-input execution, not an executable procedure that detects nontermination. The capped output is the protocol's actual output if it is made using at most q real calls, including the entire query-free continuation after its qth answer. It is ⊥ otherwise, including internal nonreturn and executions that request a (q+1)st call. These descriptors and finite output endpoint data are measurable under the paper's stated protocol assumptions. A valid-row, valid-interval Cut with an illegal target is processed as a terminal failed query attempt: its descriptor records the queried row and bracket endpoints, so the one-row update preserves its illegality and later frozen endpoints preserve its bracket value. Geometrically malformed or invalid-row calls are profile-independent terminal failures. Malformed or incomplete output encodings are also terminal failures; the tail obstruction is invoked only for valid complete finite-union allocations. This convention is unnecessary if the protocol model already requires every query to be legal on every execution.

An identical finite real transcript and the same tape determine the same intervening internal behavior. Consequently, preserving a real call and all previous answers preserves its successor behavior, while an absent next call remains absent. Virtual dummy calls do not change the actual computation. These facts justify the analytical q-stage replay even for tapes that fail, stop early, or never return.

Let H be a measurable set of tapes already captured on a current profile. Maintain the following certificates for every tape in H:

- its capped execution is ⊥ or outputs an allocation violating the desired inequality;
- every coordinate below1 among the first q answered queries or failed attempts lies at or left of the current frontier;
- every endpoint below1 of a returned allocation lies at or left of the frontier.

Any subsequent refinement preserves the capped execution. For returned allocations it also preserves every bundle value: the tail lies within one share, the refinement has total0 on that tail in every row, and everything earlier is unchanged. Thus captured failures never disappear.

To capture more tapes, take S to be the complement of H, of mass u>0. Work on its executions on the current profile. At stage k≤q, partition the current surviving S by its next queried row, assigning dummy halted paths to row1. Some class has mass at least 1/n of the current surviving set. Restrict to that row j; a virtual dummy descriptor imposes no new query-replay requirement. Each tape has finitely many current-query coordinates below1; their maximum is strictly below1. By continuity from below of probability, some fixed r∈(ℓ,1) places all those coordinates at or left of r on a subset of at least half that class. Keep that subset and perform the one-row refinement for j. The already answered queries of these tapes are protected, and the new query's row is unchanged. Thus their first k answers replay exactly. Their surviving mass is at least u/(2n)^k.

After q stages, take a second coordinate quantile for the finite endpoints of returned outputs (⊥ tapes need no endpoints), retaining at least half the surviving mass. Advance to that fixed frontier using the all-negative update. Every retained allocation now leaves the tail intact, and Section2 shows that it fails. Add these tapes to H. The new captured mass is at least

    γu, where γ = 1/[2(2n)^q] >0.                    (gain)

At every step the profile and the chosen measurable tape sets are selected from the fixed tape distribution, not from the tape subsequently used to execute the final input. This is a deterministic construction of one fixed profile from the protocol and its tape law.

Starting from H empty, after B batches the uncaptured mass is at most (1−γ)^B. Choose finite B with (1−γ)^B≤δ. The final profile is a finite refinement of the initial one, so has finitely many pieces and finite total variation; its captured mass at least1−δ fails within the query horizon. This proves the claim without an infinite-limit profile or an input selected after seeing the algorithm's actual random tape.

## 7. Expected queries and rightmost roots

If a protocol has success probability at least p on every input, apply the finite-horizon claim with δ<p. On the constructed fixed input, successful runs exceeding q have probability at least p−δ. Therefore

    E[Q] ≥ (q+1)(p−δ).

Taking arbitrarily large finite q rules out a uniform finite expected-query bound. No claim is made that every individual profile causes infinite expectation.

For reflection x↦1−x, a root of a Cut(a,b,t) corresponds to a root in the reflected bracket with target B−t, where B is the bracket value. The largest original root corresponds to the smallest reflected root. An Eval obtains B, followed by the reflected first-root Cut. This gives a simulation with at most2 queries per original Cut, preserves all legal target cases, and transfers nonexistence of any uniform finite bound to prescribed rightmost roots.

## Exact finite experiments

`experiments/coordinated_family_lp.py` exhaustively enumerates rational vertices for the initial one-, two-, and three-step cyclic families and each of the three possible whole-tail owners. All nine instances are infeasible for exact EF even with arbitrary fractional allocation of earlier cells. `coordinated_family_dual.py` checks longer families numerically and identifies the envy margin1. These are discovery checks; the symbolic certificate above is the proof.

## Current limits and verification plan

The decisive obligations are the continuous first-root replay lemma, the finite density-coefficient inequality, and the measurable finite-batch construction. The preservation agent owns the continuous Lean interfaces. This agent will formalize the finite coefficient/weighted-envy obstruction. The complete randomized measure-space construction is a written proof, not currently a complete Lean development. Independent review is pending.
