import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionFactor
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionCommit

/-! The selected bad saved edge leads to the prescribed second Shrink.
Its actual residue bound makes the identity transfer a valid commit. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows GlobalCompletion
open RefinedUpperGlobal.Transfer
variable {n : ℕ}

theorem secondFactor_range (p : Pending n) (hk : 2≤p.anchor.active.card) :
    1≤2/RefinedUpperRepair.nearError n ∧ 2/RefinedUpperRepair.nearError n ≤
      (2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1) := by
  have hn := hk.trans (active_size_bound _)
  have ht := RefinedUpperShrink.nearError_positive n
  exact ⟨(le_div_iff₀ ht).mpr (by linarith [transfer_tau_le_one hn]),
    second_factor_at_most_last hk (RefinedUpperShrinkPrecision.theta_positive n) (transfer_theta_le_one hn)
      ht (transfer_tau_le_one hn)⟩

theorem selected_shrink_cached (p : Pending n) (direction : Direction)
    (b h : Fin p.anchor.active.card)
    (hv : Selection.Valid (RefinedUpperRepair.nearError n) (p.selectionData direction) (.shrink b h)) :
    let next := p.transferCandidate (.shrink b h)
    next.anchor.edge direction next.witness next.target ∧
    RefinedUpperRepair.nearError n*total next.buffer next.witness <
      next.snapshotGap direction next.witness next.target :=
  ⟨(localGraph_iff p direction b h).mp hv.1,hv.2⟩

theorem commit_after_actual_secondShrink
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hp : p.Physical μ whole) (policy : UpperCircularStage.Policy n)
    (hpolicy : UpperCircularStage.Admissible (Chores.measureProfile μ) policy)
    (hk : 3≤p.anchor.active.card) (chores : Bool)
    (hpositive : ∀ i, 0<(μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (hedge : p.anchor.edge (if chores then .chore else .cake) p.witness p.target)
    (hbad : RefinedUpperRepair.nearError n*total p.buffer p.witness <
      p.snapshotGap (if chores then .chore else .cake) p.witness p.target)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by omega) chores (2/RefinedUpperRepair.nearError n) tape).2.2=false) :
    let next := p.acceptShrink policy (by omega) chores (2/RefinedUpperRepair.nearError n) tape
    Selection.Valid (RefinedUpperRepair.nearError n) (next.selectionData (if chores then .chore else .cake))
      (.commit (Equiv.refl _) (activeIndex p.anchor.active p.witness) (activeIndex p.anchor.active p.target)) := by
  let direction : Direction := if chores then .chore else .cake
  let G := 2/RefinedUpperRepair.nearError n
  let next := p.acceptShrink policy (by omega : 2≤p.anchor.active.card) chores G tape
  have hGrange := secondFactor_range p (by omega : 2≤p.anchor.active.card)
  have hf := RefinedUpperShrink.success_facts μ policy hpolicy hk (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive G hGrange.1 hGrange.2 chores tape haccept
  have hnext := acceptShrink_physical μ whole p hp policy hpolicy hk chores hpositive G hGrange.1 hGrange.2 tape haccept
  have hv : Selection.Valid (RefinedUpperRepair.nearError n) (p.selectionData direction)
      (.shrink (activeIndex p.anchor.active p.witness) (activeIndex p.anchor.active p.target)) := by
    constructor
    · apply (localGraph_iff _ _ _ _).mpr
      simpa only [enumerate_activeIndex _ _ hedge.1,enumerate_activeIndex _ _ hedge.2.1] using hedge
    · simpa only [Pending.selectionData,Pending.localBuffer,Pending.localGap,
        enumerate_activeIndex _ _ hedge.1,enumerate_activeIndex _ _ hedge.2.1] using hbad
  have hpos (i : Fin p.anchor.active.card) : 0≤next.localBuffer i := by
    change 0≤total next.buffer _
    rw [total_correct μ _ hnext.buffer_wf]
    exact measureReal_nonneg
  have hup (i : Fin p.anchor.active.card) : next.localBuffer i≤RefinedUpperRepair.nearError n*p.localBuffer i/2 := by
    have hh := (hf.2.2 i).2
    change (μ _).real (domain next.buffer.cells) ≤ (μ _).real (domain p.buffer.cells)/G at hh
    change total next.buffer _≤RefinedUpperRepair.nearError n*total p.buffer _/2
    rw [total_correct μ _ hnext.buffer_wf,total_correct μ _ hp.buffer_wf]
    calc
      _ ≤ _ := hh
      _ = _ := by dsimp [G]; field_simp
  exact Selection.second_commit_valid (RefinedUpperRepair.nearError n) (p.selectionData direction) next.localBuffer
    _ _ hv (RefinedUpperShrink.nearError_positive n).le hpos (localGap_self p direction) hup

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
