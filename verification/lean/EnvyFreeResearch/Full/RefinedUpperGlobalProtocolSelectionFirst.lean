import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionFactor
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionCommit

/-! The actual accepted Shrink execution supplies the hypotheses of the
finite transfer search; no candidate certificate is postulated. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows GlobalCompletion
open RefinedUpperGlobal.Transfer
variable {n : ℕ}

theorem selectTransfer_after_actual_firstShrink
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hp : p.Physical μ whole) (policy : UpperCircularStage.Policy n)
    (hpolicy : UpperCircularStage.Admissible (Chores.measureProfile μ) policy)
    (hk : 3≤p.anchor.active.card) (chores : Bool)
    (hpositive : ∀ i, 0<(μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (hX : ActiveEF (if chores then .chore else .cake) (value μ p.snapshot) p.anchor.active)
    (hw : p.witness ∈ p.anchor.active) (hj : p.target ∈ p.anchor.active)
    (hcert : RefinedUpperShrinkPrecision.theta n*total p.buffer p.witness ≤
      p.snapshotGap (if chores then .chore else .cake) p.witness p.target)
    (hreach : ∀ i j, Relation.ReflTransGen
      (fun a b => p.localGraph (if chores then .chore else .cake) a b=true) i j)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by omega) chores
      (p.firstFactor (if chores then .chore else .cake)) tape).2.2=false) :
    let next := p.acceptShrink policy (by omega) chores
      (p.firstFactor (if chores then .chore else .cake)) tape
    ∃ c, next.selectTransfer (if chores then .chore else .cake)=some c ∧
      Selection.Valid (RefinedUpperRepair.nearError n) (next.selectionData (if chores then .chore else .cake)) c := by
  let direction : Direction := if chores then .chore else .cake
  let G := p.firstFactor direction
  let next := p.acceptShrink policy (by omega : 2≤p.anchor.active.card) chores G tape
  have hGrange := firstFactor_range p (by omega : 2≤p.anchor.active.card) direction
  have hf := RefinedUpperShrink.success_facts μ policy hpolicy hk (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive G hGrange.1 hGrange.2 chores tape haccept
  have hnext := acceptShrink_physical μ whole p hp policy hpolicy hk chores hpositive G hGrange.1 hGrange.2 tape haccept
  have hr (i : Fin p.anchor.active.card) : 0<p.localBuffer i := by
    change 0<total p.buffer _
    rw [total_correct μ _ hp.buffer_wf]
    exact hpositive i
  have hd (i j : Fin p.anchor.active.card) : 0≤p.localGap direction i j := by
    change 0 ≤ GlobalCompletion.margin direction (fun a b => total (p.snapshot b) a) _ _
    rw [pending_snapshot_margin_cache μ whole p hp]
    exact hX _ (enumerate_mem _ i) _ (enumerate_mem _ j)
  have hlo (i : Fin p.anchor.active.card) : 3*p.localBuffer i/(8*G) ≤ next.localBuffer i := by
    change 3*total p.buffer _/(8*G) ≤ total next.buffer _
    rw [total_correct μ _ hp.buffer_wf,total_correct μ _ hnext.buffer_wf]
    exact (hf.2.2 i).1
  have hup (i : Fin p.anchor.active.card) : next.localBuffer i≤p.localBuffer i/G := by
    change total next.buffer _≤total p.buffer _/G
    rw [total_correct μ _ hnext.buffer_wf,total_correct μ _ hp.buffer_wf]
    exact (hf.2.2 i).2
  have hpos (i : Fin p.anchor.active.card) : 0<next.localBuffer i :=
    (div_pos (mul_pos (by norm_num) (hr i)) (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hGrange.1))).trans_le (hlo i)
  have hc : RefinedUpperShrinkPrecision.theta n*p.localBuffer (activeIndex p.anchor.active p.witness) ≤
      p.localGap direction (activeIndex p.anchor.active p.witness) (activeIndex p.anchor.active p.target) := by
    simpa only [Pending.localBuffer,Pending.localGap,enumerate_activeIndex _ _ hw,
      enumerate_activeIndex _ _ hj] using hcert
  exact Selection.select_after_first_shrink (p.localGraph direction) (p.localGap direction) p.localBuffer
    (RefinedUpperShrinkPrecision.theta n) (RefinedUpperRepair.nearError n)
    (activeIndex p.anchor.active p.witness) (activeIndex p.anchor.active p.target)
    (RefinedUpperShrinkPrecision.theta_positive n) (RefinedUpperShrink.nearError_positive n)
    (transfer_tau_le_one ((by omega : 2≤p.anchor.active.card).trans (active_size_bound _)))
    hr hd (localGap_self p direction) hc hreach next.localBuffer hpos hlo hup

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
