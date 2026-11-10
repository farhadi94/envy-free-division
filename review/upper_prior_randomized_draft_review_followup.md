# Follow-up receipt: randomized draft review repairs

Date: 2026-11-10. This is a targeted follow-up to `randomized_draft_deep_review.md`, not a replacement for that report or final whole-paper acceptance. No drafts, Lean sources, or earlier reports were edited by this reviewer. No compiler was run.

## Result

**D1–D3 and C1–C3 are closed in the reviewed draft revisions.** I read the revised passages in context and checked the exact replacement log against both preserved pre-review drafts. Each logged replacement had one occurrence, each intermediate before/after SHA-256 matched, and sequential replay reproduced the current draft files exactly. There were no unlogged changes in either draft relative to its preserved pre-review copy under that replay.

| Finding | Follow-up assessment |
|---|---|
| D1: finite-cell maximum | Closed. The main proof defines the finite retained family `\mathcal P_R`, maximizes `A_{ij}` over that family, and explicitly restricts the envelope's `E` to the same family. The preceding positive retained-mass argument supplies a nonempty retained domain. |
| D2: degenerate determinant selection | Closed. The overview maximizes determinant first and total mass second, and allows repeated cells. This retains the rank-one/zero-determinant safeguard already proved in the appendix. |
| D3: rounding preservation | Closed. The overview now specifies fixed zero/one coordinates for real recipients and includes supported rounding and trimming. It no longer claims preservation of every unused-color coordinate. |
| C1: original normalization | Closed. The selection vectors are explicitly `(nu_i(E),nu_j(E))`, normalized on the original buffer. The text distinguishes the guarantee under later normalizations from invariance of the selected pair itself. |
| C2: actual finite selector | Closed. The proof permits enumeration of finite ownership tables and selection of the first valid table, with existence furnished by the floating/rounding proof and measurability by finite selection. This matches the formal selector's role. |
| C3: two-grid deletion condition | Closed. The overview now distinguishes an unprotected inserted point in the augmented run from survival of its parent in the original run. |

I found no new issue introduced by these local replacements. The original deep review's scope limits remain in force: this follow-up does not independently recheck the complete paper, all imported lemmas, or the end-to-end compilation status.

## Deferred documentation item

The parent reports that the stale application example in `RefinedUpperFirstBad.lean` (`b=1/7`, `B=7a/6`) will be updated after the running build. That comment remains a separate documentation item; the reviewed parameterized theorem and actual `b=1/4`, `B=4a/3` instantiation do not depend on the comment. This receipt does not claim that the comment repair or subsequent clean build has happened.

## Source identities

SHA-256 values at this follow-up:

| File | SHA-256 |
|---|---|
| `randomized_paper_revision.tex` | `f828537bb1a6aa0e7dc11cf9c8ae0914849842fec9bf1b59ad447f5038b23fd6` |
| `randomized_overview_revision.tex` | `84d5f25961cad32d2304bc91108cf33a15635c98193048d35cad8c07603266c6` |
| `randomized_paper_revision.pre_deep_review.tex` | `d184e5abe8609642b031bcf3b278dc3bce2884cc582aa0dea1d36262bef780c5` |
| `randomized_overview_revision.pre_deep_review.tex` | `7490e454bf985779f7afdb3ea190c8c41c427d6b575f92cd6cb031ad59bf95f0` |
| `randomized_draft_review_repairs.json` | `23ffd22df0a693829922a398043ab9971f84cca7007469b82f2c64465de1d7e3` |
| `randomized_draft_deep_review.md` | `d86b1c09ae7d1dbb4e13e628597ee8d6094ca546f143c7bc451b5b2f72887ade` |
