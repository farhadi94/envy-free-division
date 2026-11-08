# Independent targeted audit of randomized upper composition

Reviewer: `cross_disciplinary`. This is a new correctness audit, not a
reaffirmation of an earlier acceptance. The manuscript and Lean sources were
read only. The specific concerns were potential monotonicity at zero residues,
whole-bundle transport, and the two-shrink transfer; the audit also checks the
primitive and probability interfaces needed to compose them.
Independence here means a separate agent's derivation and tests; it is not a
claim of human peer review.

## Verdict and snapshot

**ACCEPT the written randomized upper composition at the reviewed source
snapshot.** No mathematical counterexample or unresolved composition gap was
found. The source is
[`upper_proof.tex`](../../paper/sections/upper_proof.tex), SHA-256
`66955a399e1eaa71abf7df7f92662b23ba37b57e67998ee59482b75a4634fec9`.
It is unchanged in the final [submission snapshot](../final_snapshot.json),
SHA-256 `b446afd3d9512f9e684bfb406fdc46324c4b01fa3b46e470bc74596b2b1c7f6b`.
The 71-page final PDF has SHA-256
`fca21e71706d17b07a0fc272bbeabcd0e7ace0317d228ef48c7527d778f64295`.
The [final audit receipt](upper_independent_receipt.json) pins these artifacts
and the supporting reviewed files. **There are no unresolved required findings
in this targeted audit.** An intervening mathematical source change requires a
delta review.

The verdict covers the actual written primitive-to-completion argument. It does
not describe the continuous allocation protocol as Lean-formalized. The new
finite transport and general probability modules were also read directly, with
the distinct scopes recorded below. Their local build/axiom receipts and the
coordinator's passed aggregate verification record have been inspected. The
aggregate record pins the reviewed modules and reports 31 modules, 815 authored
and 1,373 total theorem declarations. This reviewer did not run that verifier.
The final model's explicit measurable-transcript convention and the main upper
theorem's nonanticipating-root qualification agree with the proof's use of
fresh random choices. No human review or full Lean formalization is inferred.

## Primitive interfaces and conditioning

I reread the physical Repair construction, its quantitative assumptions,
Snapshot's three branches and contrast proof, the one-sided refinement, and the
prescribed Shrink proof. The completion proof does not assume its own conclusion
as a primitive precondition.

* **Repair:** its endowments need only satisfy
  `g_ij(W) >= -tau mu_i(B)` among active agents. It requires a positive buffer for
  each of those agents, but no bound on the old endowments' absolute values and
  no global EF hypothesis against frozen agents. On acceptance it moves whole
  endowments, adds disjoint subsets of the buffer, and spends at most one
  quarter of that buffer in every active row. The seed and reserve payments are
  both included in these additions. Its literal complement is the new residue.
  The assigned-shortfall/regret sum bounds the nonnegative credits even when
  the old endowments have large values. The payment induction leaves all rows
  positive before each reached correction, including a correction that rejects.
* **Snapshot:** it acts only on the current residue, independently of the old
  total bundles. Its partial return is active EF and has a positive remaining
  residue in every active row. The certificate is row-relative:
  `g_ab(X) >= theta mu_a(T)`. The zero sampled-disagreement branch uses actual
  complete EF checks, not cell agreement as a claim about the entire measures.
  The large-disagreement branch retains a third empty label because the caller
  invokes it only for `k >= 3`.
* **Snapshot's probability composition:** the common interpolation event is
  bounded before conditioning on a favorable table. The repeated candidate
  witness bound holds after each candidate history. Once a checked input has
  been chosen, the inner Repair is fresh and the contrast-success bound is
  conditional on that complete history. The proof combines the unconditional
  table/candidate exception with this fresh bound; it does not claim a uniform
  interpolation estimate conditional on a selected good table. Likewise the
  contrast proof uses `Pr(S and G) >= 1/2 - Pr(G fails)`, rather than conditioning
  on successful Repair. These are valid uses of the stated probability bounds.
* **Shrink:** the one-sided carve gives a positive buffer between
  `mu_i(U)/(2G)` and `mu_i(U)/G` in every row, with endowment loss within the
  Repair tolerance. Quarter spending therefore leaves the two-sided bracket
  `3 mu_i(U)/(8G) <= mu_i(U') <= mu_i(U)/G`. Every retry includes a newly charged
  carve and inner Repair. The factor is fixed before that retry's randomness.

The ordinary finite-union prefix routine uses cached component totals and at
most one individual Cut for a strict residual target. The refinement and
circular constructions therefore do not assume an uncharged union or mixture
Cut. Arbitrary plateau roots do not change the nonnegative median bound. In the
circular constructions, nonunique target levels and their fixed circular shifts
are countable; fresh continuous targets avoid them almost surely. The argument
allows cutter-null intervals to have value for other observers. Endpoint records
are retained for all original observers, including frozen ones.

Rejection changes the query history and the available records, but commits no
candidate allocation. Logical sampling grids may ignore previously recorded
joins. Thus discarded endpoints neither become free oracle calls nor force an
unbudgeted new coarse-cell count. Each new trial's conditional guarantee is
stated after the entire preceding history, including rejected work.

## Independent derivation of the two-shrink transfer

At the saved anchor, all active residue values are positive. Snapshot gives
nonnegative losses `d_ij = g_ij(X)`, diagonal zero, and a certificate in column
`j`. Set `x_i = d_ij/mu_i(T)`. This normalization is separate for each row;
the proof never substitutes a common residue value.

The unsafe interval for `G x_i` is `(3 tau/8, 2)`, of multiplicative width
`16/(3 tau)`, strictly smaller than the adjacent factor ratio `8/tau`. A
positive row can therefore forbid at most one of the `k` proposed factors.
The diagonal row forbids none. A safe factor exists. After the first Shrink,
the lower residue bound converts `G x_i <= 3 tau/8` into
`d_ij <= tau rho_i`, and the upper bound converts `G x_i >= 2` into
`d_ij >= 2 rho_i`. The certificate row is large and row `j` is small.

A saved-graph path from the certificate row to `j` contains a large-to-small
edge `i -> h`. If `h=j`, identity is the required transfer. Otherwise use a
simple path `j=u_0 -> ... -> u_t=h`. If its edge losses are all small, assigning
each `u_r` label `u_(r+1)` and assigning `h` label `j` is a permutation. All
own losses are small, including the closing loss at `h`, while the comparison
from `i` to the label now held by `h` remains large. If a path edge `p -> q`
instead has loss greater than `tau rho_p`, shrink the current residue by
`2/tau` and use identity. Then the unchanged snapshot loss exceeds twice the
new row-`p` residue. No shrink follows a nonidentity transfer. The stated
`G_max` contains both factors.

For both cake and chores, adding the old EF bundles and the EF shrinking pieces
under their owners gives the exact identity

```text
g_ir(D) = g_ir(W) + g_ir(H) + d_i,alpha(r) - d_i,alpha(i).
```

It proves the final Repair input tolerance and the witness margin
`g_bh(D) >= (2-tau) rho_b`. The intermediate endowments `D` need not be
globally EF. The concrete protocol neither commits them nor performs a zero-row
exit on them.

## Whole-label transport, frozen agents, and zero residues

Let the final Repair assign old label `j` to `f(j)`, with `f` the identity on
frozen labels. The physical construction gives

```text
Z_f(j) = W_j union B_j,
sum_j mu_i(B_j) + mu_i(U') = mu_i(U),
```

where the additions are disjoint, and `B_j` is empty for frozen labels. This
is a partition identity for every original observer, not merely for active
ones or under an approximate value table.

Before global EF is claimed, active EF permits comparison of observer `i` to
the active recipient `f(i)`. Consequently own value is at least
`mu_i(W_i)+mu_i(B_i)` for cake, and own cost is at most that amount for chores.
For frozen observers this is equality. These inequalities prove global EF and
the guards without circularity:

* For cake, active own value does not fall; a frozen observer loses at most
  `mu_f(B_j)` when comparing with the moved old label `j`. Its old guard and
  physical balance leave margin at least `mu_f(U')`.
* For chores, frozen observers see only nonnegative additions to old active
  bundles. An active observer's own cost can increase, but by at most
  `mu_i(B_i)`. Its old guard therefore leaves margin at least `mu_i(U')`
  toward every frozen agent.

This distinction matters: chore own cost is **not** asserted to be
nonincreasing. The needed upper bound includes the additions attached to its
old label.

For any old proper target `j`, the same inequalities give a new margin toward
`f(j)` of at least the new row residue. If this residue is positive, the image
cannot be the observer itself, since a self-margin is zero; injectivity then
preserves the proper-target count. If the residue is zero, that image argument
alone is invalid. The proof instead uses the already established global EF to
saturate the row's target count at `n-1`. This covers frozen rows as well.

The witness has margin at least `(7/4-tau) rho_b > rho_b` after final Repair,
because the entire final addition is worth at most `rho_b/4`. Its new residue
is at least `3 rho_b/4 > 0`. Thus `f(h)` is proper and, since `h` was not an
old target at the saved anchor, is outside the injective image of every old
target. That row's count strictly increases. Temporary additive Snapshot and
Shrink allocations are not used as comparison anchors for this argument.

At a committed state, sink-SCC freezing adds exactly the necessary directional
guards, changes no material, and leaves the full original-population potential
unchanged. A zero-value cake observer can freeze because its new guard is zero.
A zero-cost chore observer may receive the entire residue as an EF allocation
of that residue. The additive-composition argument protects frozen observers
in both cases. One- and two-agent completions use original owners and preserve
the same invariant. Positive intermediate residue brackets exclude an active
zero row inside a pending iteration.

## Almost-sure completion and costs

Each nontrivial iteration starts with an unsaturated potential bounded by
`n(n-1)`. A nonterminal iteration increases it by at least one; a terminal
iteration also starts unsaturated. Freezing does not reset this potential.
There are therefore at most `n(n-1)` reached nontrivial iterations over the
whole run.

For a request with uniform conditional acceptance at least `p`, fresh retries
give `Pr(N>r | start history) <= (1-p)^r` by iterated conditioning. The tail
sum yields `E[N | start history] <= 1/p` and finite return almost surely.
Independence between attempts or requests is unnecessary. The request's input
is fixed while retrying, although the root policy can react to all earlier
queries. The actual draws and policies must satisfy the paper's measurable,
nonanticipating model.

There are one Snapshot, at most two Shrinks, and one final Repair per
nontrivial iteration. Conditional expectation at the reached request histories
gives at most `4 + 3(64/63) = 148/21 < 8` full trials. Each full trial costs
at most `6m` Cuts and `12nm` queries, including its inner Repair and failed
work. Summing over reached iterations gives the stated
`48 n(n-1)m` and `96 n^2(n-1)m` bounds, plus initial totals and the final base.
All internal finite-trial computations terminate under the uncharged exact-real
computation model.

The optional failure-reporting cap uses only fresh full-trial boundaries. At
such a boundary the same saved-anchor argument bounds the expected remaining
trials. Iterated conditional Markov bounds in blocks of length `16n(n-1)`
therefore apply. A partially exposed trial must be charged before invoking a
fresh-start probability guarantee, as the manuscript states. This is not a
deterministic exact-success protocol.

## Independent finite checks and formal boundary

The [from-scratch finite checks](upper_independent_checks.py) and their
[result](upper_independent_checks.json) import no author implementation or
earlier test backend. Integer row-table enumeration checked 68,093 admissible transport
states for three and four original agents in both preference directions. The
only new-state fairness hypothesis supplied was active-active EF. The checks
derived global EF, both frozen guards, and target monotonicity, including
37,309 positive-residue states, 30,784 zero-residue states, and 13,380 available
strict-new-target comparisons. Such nonnegative finite tables have a direct
nonatomic realization on disjoint constant-density cells.

Separate exact-rational fixtures checked 4,798 two-shrink transfers with three
through eight active agents, unequal row totals and strongly connected graphs.
They exercised 3,453 first-shrink identity cases, 298 nonidentity rotations,
and 1,047 second shrinks. Every resulting permutation, row-relative loss
bound, positive residue and saved-graph witness was checked. The deterministic
fixture seed was `2026110701`. These checks support, and do not replace, the
universal derivations above.

I directly read the frozen `QueryProbability.lean` source at SHA-256
`c050c1da43d681952b4529a783dbb11efcf42ab70e26d27665c20cc37ea47241`
and its [scope note](probability_formalization.md). Its actual measurable
extended-natural survival indicators give the tail-sum integral. The explicit
survival-mass contraction yields the geometric integral bound, and strict
contraction implies almost-sure finite waiting. Instantiating a fixed-history
law with `r=3/4` or `r=1/64` matches the written request bounds. Neither finite
expectation nor summability is assumed. The separately supplied pointwise cost
cap is integrated in `expected_cost_le_of_attempt_budget`. **This scoped
probability interface is accepted.**

The protocol must still derive the survival contraction by iterated
conditioning, prove measurability and finite internal work, and sum over the
bounded number of reached anchored iterations. Those steps were checked in the
written proof above, and are not claimed as part of this Lean module.
I also directly read `GlobalCompletion.lean`, SHA-256
`dab3c06a639377d8415d43286e4406212dfd47f1ccee938ee80886307ea0e54d`,
the relevant imported `R4GlobalPotential` transport/cardinality proofs, and the
final [module receipt and scope](upper_formalization.md).
`ConcreteStep` contains nonnegative snapshot, shrinking and payment tables,
the two permutations, actual sum identities, active EF certificates,
small-own-loss/large-snapshot inequalities, and quarter spending. Its fields
do not assume global EF, a transported target, the post-Repair witness, or
potential growth. `wholeAddition` reconstructs the transport and physical value
balance using both permutations. `concrete_step_composition` then derives the
global invariant and strict saved-anchor progress. The zero-row theorem uses
derived global EF, while the positive-row theorem separately proves that target
images remain proper.

The event layer proves that a freeze with an actually removed agent decreases
the active count, that a concrete continuation increases the target potential,
and that finite runs preserve validity. `finite_run_with_terminal_bound`
handles the terminal iteration without an extra population factor, from the
explicit missing-target premise. The finite-atom construction derives its sum
identity from unique ownership. `finite_global_completion` composes a finite
run with a separately supplied complete active-EF terminal allocation.
**This finite certificate interface is accepted.**

The small-own-loss and large-snapshot inequalities are outputs of the
handwritten two-shrink argument, not a Lean construction of that argument.
Likewise the event sequence, physical interval allocation, full coverage of
null fragments, terminal allocation and their oracle realization remain caller
obligations. Neither new module is taken to formalize a conditional history
kernel or the complete continuous protocol. Their local compile/axiom receipts
are distinct from this semantic interface audit.
