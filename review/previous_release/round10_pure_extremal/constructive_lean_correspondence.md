# Independent Lean-to-proof correspondence review

Status: **ACCEPT** for the finite statements and their mapping to the paper. No required finding.

Source: `lean/CoordinatedFamily.lean`  
SHA-256: `407fd0a322ab1298f1c2a52b6ff9de391256a0cdafcb055c478bc6bd4022b451`

This review inspects the actual assumptions and conclusions of all seven authored theorems. The coordinator requested no duplicate compile; compilation and axiom checking remain the author's separate build receipt.

## Mapping

Choose any two distinct agents a and b different from the owner c of the final interval; this choice exists for n≥3. For each resolved constant-density cell, multiply the two selected densities by the nonnegative cell length. The resulting signed cell values satisfy `PairCellCondition`:

* If neither selected row is the cell's unique positive row, both values are nonpositive.
* If a is the positive row, b is at most −(1+1/α) times a, and conversely.
* The factor `(1+α)/α` in Lean equals the paper's `1+1/α` because α>0.

`nonpositive_pair_coefficients`, `dominated_pair_coefficients`, and `cell_condition_coefficients` derive the three nonpositive coefficients needed for redistributing a cell. They do not assume the desired envy conclusion.

In `cell_transfer_nonpositive`, x and y are fractions assigned to the two selected nonowners, z is the fraction assigned to c, and r is the total fraction assigned to any remaining agents. Their sum is one. Only x,y,r≥0 is needed for the algebra; omitting z≥0 makes this scalar lemma stronger and does not weaken its applicability to actual allocations.

`two_nonowners_envy_sum` sums the cell inequalities. The selected observer's own value is Σ a_k x_k, and c's value to that observer is `1−Σ a_k(1−z_k)`: normalization to total one and allocation of the entire final interval to c give exactly this expression. Thus the displayed sum is the two selected signed envy gaps, and it is at least 2α.

`two_nonowners_force_violation` deduces that one selected gap exceeds ε whenever ε<α. The final `cell_condition_force_violation` theorem composes the original cell-condition assumptions all the way to that disjunction; the coefficient lemmas are genuine dependencies.

The paper averages over all nonowners, whereas the Lean file uses any chosen pair. These are different sufficient finite certificates for the same tail-obstruction lemma. The pair certificate is valid for any n≥3 and does not require selecting a different pair for each cell.

## Explicit limits

The file does not construct the selected physical agents, measurable share fractions, constant-density interval measures, or the formula expressing normalized bundle values as finite sums. These are the stated mathematical interpretation of its finite data. It also does not formalize continuous frontier updates, first-root replay, probability quantiles, tape capture, or the expected-query theorem; the header expressly excludes them. Claiming finite tail-obstruction coverage is accurate. Claiming complete mechanization of the mixed lower bound would not be accurate.
