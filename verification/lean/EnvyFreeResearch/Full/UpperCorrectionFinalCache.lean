import EnvyFreeResearch.Full.UpperCorrectionRecording
import EnvyFreeResearch.Full.UpperCorrectionStageProgram
import EnvyFreeResearch.Full.UpperPreparedEnvelopeMean
import EnvyFreeResearch.Full.UpperCorrectionDisjoint

/-! Cached states for each actual accepted payment, using its final complete
history. Sorting and empty-carrier removal issue no queries and preserve
literal endpoint ownership and every zero-valued nonempty fragment. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionFinalCache

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperEndpointCache
  UpperCorrectionLoop UpperCorrectionTrace UpperCorrectionPieces UpperCircularStage
  UpperCorrectionRecording UpperCorrectionSetup UpperCorrectionSupply UpperCorrectionOutcome
  UpperCorrectionAccepted UpperCorrectionDisjoint UpperPreparedEnvelopeMean UpperCorrectionStageProgram

variable {n k m : ℕ} [Nonempty (Fin k)]

def paymentState (result : Result n k) (j : Fin k) : State n :=
  UpperComponentAssembly.state (result.1 j) result.2.1.history

theorem paymentState_domain (result : Result n k) (j : Fin k) :
    domain (paymentState result j).cells = domain (result.1 j) :=
  UpperComponentAssembly.assemble_domain _

theorem paymentState_history (result : Result n k) (j : Fin k) :
    (paymentState result j).history = result.2.1.history := rfl

theorem paymentState_measurable {X : Type} [MeasurableSpace X] (result : X → Result n k)
    (hresult : Measurable result) (j : Fin k) : Measurable (fun x => paymentState (result x) j) :=
  UpperComponentAssembly.state_measurable.comp
    (((measurable_pi_apply j).comp (measurable_fst.comp hresult)).prodMk
      (state_history_measurable.comp (measurable_fst.comp (measurable_snd.comp hresult))))

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (hinj : Function.Injective active)
  (reserve : State n) (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam N : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : (k : ℝ)^2 ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
  (tape : Fin k → UpperCircular.Circle)

include hpolicy hinj heta hlam hsize hmargin hc in
theorem stage_recording :
    let final := (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2
    WellFormed μ final.current ∧ reserve.history ⊆ final.current.history ∧
      RecordedEndpoints final.accepted final.current.history := by
  let Inv := Safe μ (UpperRawPayments.activeSet active) (domain reserve.cells)
    (fun i => 7 / 8 * (μ i).real (domain reserve.cells)) (tasks active reserve cuts t eta lam)
  have hstart : Inv 0 (startState active reserve cuts t eta) :=
    start_safe μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated hc.positive hinj
      (domain reserve.cells) Subset.rfl t eta lam heta hlam hc.small hc.sum hmargin
  have hstep (i : Fin k) (state : LoopState n) (start : UpperCircular.Circle) (hs : Inv i.castSucc state) :
      Inv i.succ (step policy state (tasks active reserve cuts t eta lam i, start)).2 :=
    tasks_safe_step μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone hc.separated hc.positive
      policy hpolicy (domain reserve.cells) t eta lam heta hc.small hc.targets hc.sum hsize i state start hs
  have hready (i : Fin k) (state : LoopState n) (hs : Inv i.castSucc state) :
      WellFormed μ state.current ∧ (state.stopped = false →
        0 < (μ (tasks active reserve cuts t eta lam i).owner).real (domain state.current.cells)) := by
    refine ⟨hs.1, fun _ => ?_⟩
    have hmass := safe_mass μ (UpperRawPayments.activeSet active) (domain reserve.cells) _
      (tasks active reserve cuts t eta lam) i.castSucc state hs
      (fun j a _ => tasks_budget_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
        hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum hsize j a)
      (active i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) (hc.positive i)).trans hmass
  have h := run_recorded μ policy hpolicy (tasks active reserve cuts t eta lam) Inv hstep hready
    (startState active reserve cuts t eta) tape hstart (by simp [RecordedEndpoints, startState, initial, endpoints])
  exact ⟨h.1.1, h.2.1, h.2.2⟩

include hc in
theorem wholeAtoms_recorded (j : Fin k) :
    RecordedHistory (wholeAtoms active reserve cuts t eta j) reserve.history := by
  intro i p hp
  obtain ⟨c, hc', hp⟩ := hp
  exact hc.wellFormed.2.2.2 i p ⟨c, (List.mem_filter.mp hc').1, hp⟩

include hc in
theorem output_components
    (hrun : (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false)
    (j : Fin k) : DisjointComponents (output policy active reserve cuts t eta lam tape j) := by
  have hstart := UpperPendingExclusion.remove_wellFormed μ reserve hc.wellFormed cuts (whole active reserve cuts t eta)
  have hl : (corrections policy active reserve cuts t eta lam tape).length = k :=
    (successful_outputs policy (tasks active reserve cuts t eta lam)
      (startState active reserve cuts t eta).current tape hrun).1
  have hj := getD_mem (corrections policy active reserve cuts t eta lam tape) [] j.val (by rw [hl]; exact j.isLt)
  apply UpperComponentAssembly.append_disjoint
  · exact hc.wellFormed.2.1.filter _
  · exact payments_components_disjoint _ hstart.2.1 _ _ hj
  · rw [wholeAtoms_domain active reserve cuts hc.zero hc.monotone hc.separated]
    exact (pending_disjoint_current μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated
      t eta (startState active reserve cuts t eta).current Subset.rfl j).mono_right
        (payments_domain_subset _ _ _ hj)

include hpolicy hinj heta hlam hsize hmargin hc in
theorem paymentState_wellFormed
    (hrun : (run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false)
    (j : Fin k) : WellFormed μ (paymentState (executeStage policy active reserve cuts t eta lam tape) j) := by
  have hfinal := stage_recording μ policy hpolicy active hinj reserve cuts t eta lam N heta hlam hsize hmargin selected hc tape
  have hstart := UpperPendingExclusion.remove_wellFormed μ reserve hc.wellFormed cuts (whole active reserve cuts t eta)
  have hl : (corrections policy active reserve cuts t eta lam tape).length = k :=
    (successful_outputs policy (tasks active reserve cuts t eta lam)
      (startState active reserve cuts t eta).current tape hrun).1
  have hj := getD_mem (corrections policy active reserve cuts t eta lam tape) [] j.val (by rw [hl]; exact j.isLt)
  apply UpperComponentAssembly.state_wellFormed μ _ _
    (output_components μ policy active reserve cuts t eta lam N selected hc tape hrun j) hfinal.1.2.2.1
  apply UpperComponentAssembly.append_recorded
  · exact recordedHistory_mono _ (wholeAtoms_recorded μ active reserve cuts t eta N selected hc j) hfinal.2.1
  · exact payments_recordedHistory _ _ _
      (recordedHistory_mono _ hstart.2.2.2 hfinal.2.1) hfinal.2.2 _ hj

end EnvyFreeResearch.Full.UpperCorrectionFinalCache
