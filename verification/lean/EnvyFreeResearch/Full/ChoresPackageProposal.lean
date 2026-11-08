import EnvyFreeResearch.Full.ChoresPackageMaterial
import EnvyFreeResearch.ChoreComposition

/-! A donor proposal's finite cost table is realized by actual complementary
pieces. The original gap, rather than a current or truncated gap, supplies
the affine credit and deficit identities. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PackageGeometry
open Set MeasureTheory ChoreComposition
open scoped Classical

variable {Agent Root : Type*}

def proposalPiece (parent : Agent → Set ℝ) (equalizer : Agent → Agent → Set ℝ)
    (proposal : Proposal Agent Root) (removed : Set ℝ) (p : Agent) : Set ℝ :=
  if proposal.execute then
    if p = proposal.label then parent p \ removed else equalizer p (proposal.owner p)
  else equalizer p (proposal.before.owner p)

theorem proposal_piece_subset (parent : Agent → Set ℝ) (equalizer : Agent → Agent → Set ℝ)
    (hsub : ∀ p j, equalizer p j ⊆ parent p) (proposal : Proposal Agent Root) (removed : Set ℝ) (p : Agent) :
    proposalPiece parent equalizer proposal removed p ⊆ parent p := by
  unfold proposalPiece
  split
  · split
    · exact sdiff_subset
    · exact hsub _ _
  · exact hsub _ _

theorem proposal_piece_measurable (parent : Agent → Set ℝ) (equalizer : Agent → Agent → Set ℝ)
    (hparent : ∀ p, MeasurableSet (parent p)) (hequalizer : ∀ p j, MeasurableSet (equalizer p j))
    (proposal : Proposal Agent Root) (removed : Set ℝ) (hremoved : MeasurableSet removed) (p : Agent) :
    MeasurableSet (proposalPiece parent equalizer proposal removed p) := by
  unfold proposalPiece
  split
  · split
    · exact (hparent p).diff hremoved
    · exact hequalizer _ _
  · exact hequalizer _ _

theorem physical_complement_credit (μ : Measure ℝ) [IsFiniteMeasure μ]
    (parent removed : Set ℝ) (hsub : removed ⊆ parent) (hm : MeasurableSet removed) (baseline : ℝ) :
    baseline-μ.real (parent \ removed) = μ.real removed-(μ.real parent-baseline) := by
  rw [measureReal_sdiff hsub hm]
  ring

theorem proposal_piece_value (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (parent : Agent → Set ℝ) (equalizer : Agent → Agent → Set ℝ)
    (proposal : Proposal Agent Root) (removed : Set ℝ)
    (hsub : removed ⊆ parent proposal.label) (hm : MeasurableSet removed)
    (hequalizer : ∀ i p j, proposal.before.equalizerCost i p j = (cost i).real (equalizer p j))
    (hutility : ∀ i, proposal.utility i =
      (cost i).real removed-((cost i).real (parent proposal.label)-proposal.before.baseline i))
    (i p : Agent) :
    proposal.output.cost i p = (cost i).real (proposalPiece parent equalizer proposal removed p) := by
  cases he : proposal.execute with
  | false => simpa only [Proposal.output,proposalPiece,he,Bool.false_eq_true,ite_false,
      Frame.allocation] using hequalizer i p (proposal.before.owner p)
  | true =>
    by_cases hp : p = proposal.label
    · subst p
      simp only [Proposal.output,proposalPiece,he,ite_true]
      rw [hutility i,measureReal_sdiff hsub hm]
      ring
    · simpa only [Proposal.output,proposalPiece,he,ite_true,ite_eq_right hp] using
        hequalizer i p (proposal.owner p)

theorem proposal_baseline (proposal : Proposal Agent Root) :
    proposal.output.baseline = proposal.before.baseline := by
  cases he : proposal.execute <;> simp [Proposal.output,he,Frame.allocation]

/-- The executed payment equals the actual recipient's cost reduction on
the actual retained complementary piece; zero executions retain the old
physical equalizer. -/
theorem actual_proposal_credit (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (parent : Agent → Set ℝ) (equalizer : Agent → Agent → Set ℝ)
    (proposal : Proposal Agent Root) (hgood : proposal.Good) (removed : Set ℝ)
    (hsub : removed ⊆ parent proposal.label) (hm : MeasurableSet removed)
    (hequalizer : ∀ i p j, proposal.before.equalizerCost i p j = (cost i).real (equalizer p j))
    (hutility : ∀ i, proposal.utility i =
      (cost i).real removed-((cost i).real (parent proposal.label)-proposal.before.baseline i))
    (i p : Agent) :
    (if proposal.output.owner p = i then
      proposal.before.baseline i-(cost i).real (proposalPiece parent equalizer proposal removed p) else 0) =
      proposal.payment i p := by
  rw [← proposal_piece_value cost parent equalizer proposal removed hsub hm hequalizer hutility i p,
    ← proposal_baseline proposal]
  exact ChoreComposition.proposal_credit proposal hgood i p

theorem actual_proposal_debit_bound (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (parent : Agent → Set ℝ) (equalizer : Agent → Agent → Set ℝ)
    (proposal : Proposal Agent Root) (hgood : proposal.Good) (removed : Set ℝ)
    (hsub : removed ⊆ parent proposal.label) (hm : MeasurableSet removed)
    (hequalizer : ∀ i p j, proposal.before.equalizerCost i p j = (cost i).real (equalizer p j))
    (hutility : ∀ i, proposal.utility i =
      (cost i).real removed-((cost i).real (parent proposal.label)-proposal.before.baseline i))
    (i j p : Agent) :
    (if proposal.output.owner p = j then
      max 0 (proposal.before.baseline i-(cost i).real (proposalPiece parent equalizer proposal removed p)) else 0) ≤
      proposal.before.reserve i j p+proposal.extra i j p := by
  rw [← proposal_piece_value cost parent equalizer proposal removed hsub hm hequalizer hutility i p,
    ← proposal_baseline proposal]
  exact ChoreComposition.proposal_debit_bound proposal hgood i j p

end EnvyFreeResearch.Full.Chores.PackageGeometry
