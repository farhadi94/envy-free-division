import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalPendingShrink
import EnvyFreeResearch.Full.RefinedUpperShrinkCorrectness
import EnvyFreeResearch.Full.RefinedUpperShrinkRestart
import EnvyFreeResearch.Full.UpperPopulationExtension

/-! Actual accepted and rejected Shrink actions on the pending physical state. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows UpperCircularStage
variable {n : ℕ}

def Pending.shrinkResult (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :=
  RefinedUpperShrink.execute policy hk chores (enumerate p.anchor.active) p.buffer G tape

def Pending.acceptShrink (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) : Pending n :=
  let result := p.shrinkResult policy hk chores G tape
  p.addShrink (extendPieces p.anchor.active result.1 result.2.1.history) result.2.1

theorem acceptShrink_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 3 ≤ p.anchor.active.card) (chores : Bool)
    (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (G : ℝ) (hG : 1 ≤ G)
    (hmax : G ≤ (2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1))
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by omega) chores G tape).2.2=false) :
    (p.acceptShrink policy (by omega) chores G tape).Physical μ whole := by
  have facts := RefinedUpperShrink.success_facts μ policy hpolicy hk (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive G hG hmax chores tape haccept
  let r := p.shrinkResult policy (by omega) chores G tape
  have hr : WellFormed μ r.2.1 := facts.1.residue_wellFormed
  have hh := RefinedUpperShrink.program_cost policy (by omega : 2 ≤ p.anchor.active.card) chores
    (enumerate p.anchor.active) (enumerate_injective _) p.buffer G hG tape
  obtain ⟨tr,_,htrace,_,_⟩ := hh
  apply pending_addShrink_physical μ whole p hp _ r.2.1
  · exact extendPieces_wellFormed μ _ _ _ hr.2.2.1 facts.1.allocation_wellFormed
  · exact hr
  · exact extendPieces_pairwise _ _ _ facts.1.allocation_disjoint
  · intro j
    by_cases hj : j ∈ p.anchor.active
    · obtain ⟨i,rfl⟩ := enumerate_preimage _ j hj
      rw [extendPieces_apply]
      exact facts.1.residue_disjoint i
    · rw [extendPieces_frozen _ _ _ _ hj]
      exact empty_disjoint _
  · rw [extendPieces_domain]
    exact facts.2.1
  · change p.buffer.history ⊆ (RefinedUpperShrink.execute policy _ chores _ _ G tape).2.1.history
    rw [htrace]
    exact List.subset_append_left _ _
  · intro j
    change (extendPieces p.anchor.active r.1 r.2.1.history j).history ⊆ r.2.1.history
    have he : ∀ i, (r.1 i).history = r.2.1.history := facts.1.common_history
    rw [extendPieces_history _ _ _ he j]
  · intro j hj
    rw [extendPieces_frozen _ _ _ _ hj]
    rfl

theorem refreshShrink_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 3 ≤ p.anchor.active.card) (chores : Bool)
    (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (G : ℝ) (hG : 1 ≤ G)
    (hmax : G ≤ (2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1))
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    (p.refresh (p.shrinkResult policy (by omega) chores G tape).2.1.history).Physical μ whole := by
  apply pending_refresh_physical μ whole p hp
  · exact RefinedUpperShrink.final_history_truthful μ hk chores (enumerate p.anchor.active)
      (enumerate_injective _) p.buffer hp.buffer_wf hpositive G hG hmax policy hpolicy tape
  · obtain ⟨trace,_,hh,_,_⟩ := RefinedUpperShrink.program_cost policy (by omega : 2 ≤ p.anchor.active.card)
      chores (enumerate p.anchor.active) (enumerate_injective _) p.buffer G hG tape
    change p.buffer.history ⊆ (RefinedUpperShrink.execute policy _ chores _ _ G tape).2.1.history
    rw [hh]
    exact List.subset_append_left _ _

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
