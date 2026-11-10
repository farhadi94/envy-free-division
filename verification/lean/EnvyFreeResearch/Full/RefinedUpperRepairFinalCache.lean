import EnvyFreeResearch.Full.RefinedUpperRepairFinalCacheRecording
import EnvyFreeResearch.Full.RefinedUpperCorrectionDisjoint
import EnvyFreeResearch.Full.RefinedUpperCorrectionOutputMeasurable
import EnvyFreeResearch.Full.UpperPreparedEnvelopeMean
import EnvyFreeResearch.Full.UpperComponentAssembly

/-! Cached states for each actual accepted payment, using its final complete
history. Sorting and empty-carrier removal issue no queries and preserve
literal endpoint ownership and every zero-valued nonempty fragment. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.RefinedUpperRepairFinalCache

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperEndpointCache
  UpperCorrectionLoop UpperCorrectionTrace UpperCorrectionPieces UpperCircularStage
  UpperCorrectionRecording RefinedUpperCorrectionSetup UpperCorrectionSupply RefinedUpperCorrectionOutcome
  RefinedUpperCorrectionAccepted RefinedUpperCorrectionDisjoint UpperPreparedEnvelopeMean UpperStageMeasurable

variable {n k m r : ℕ} [Nonempty (Fin k)]

abbrev Result (n k : ℕ) := (Fin k → List Component) × State n × Bool

def executeStage (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (tape : Fin k → Fin r → UpperCircular.Circle) : Result n k :=
  let final := (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam)
    (startState active reserve cuts t eta) tape).2
  (output policy active reserve cuts t eta lam tape, final.current, final.stopped)

theorem executeStage_output (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (tape : Fin k → Fin r → UpperCircular.Circle) :
    (executeStage policy active reserve cuts t eta lam tape).1 =
      output policy active reserve cuts t eta lam tape := rfl

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
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 4 * (k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (selected : Finset (Fin (m + 1))) (hc : Checks μ active reserve cuts t eta selected N)
  (tape : Fin k → Fin r → UpperCircular.Circle)

include hpolicy hinj heta hlam hsize hmargin hc in
theorem stage_recording :
    let final := (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2
    WellFormed μ final.current ∧ reserve.history ⊆ final.current.history ∧
      RecordedEndpoints final.accepted final.current.history := by
  let job := tasks active reserve cuts t eta lam
  let floor := fun i => 7 / 8 * (μ i).real (domain reserve.cells)
  have hstart : Safe μ (RefinedUpperRawPayments.activeSet active) (domain reserve.cells) floor job 0
      (startState active reserve cuts t eta) :=
    start_safe μ active reserve hc.wellFormed cuts hc.zero hc.monotone hc.separated hc.positive hinj
      (domain reserve.cells) Subset.rfl t eta lam heta hlam hc.small hc.sum hmargin
  have hfloor : ∀ i ∈ RefinedUpperRawPayments.activeSet active, 0 < floor i := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact mul_pos (by norm_num) (hc.positive j)
  have hbudget : ∀ j i, i ∈ RefinedUpperRawPayments.activeSet active → 0 ≤ budget (job j) i := by
    intro j i _
    exact tasks_budget_nonneg μ active reserve hc.wellFormed cuts hc.zero hc.one hc.monotone
      hc.separated hc.positive t eta lam heta hc.small hc.targets hc.sum hsize j i
  have h := RefinedUpperRepairFinalCache.run_recorded μ policy hpolicy
    (RefinedUpperRawPayments.activeSet active) (domain reserve.cells) floor hfloor job
    (RefinedUpperRawPayments.jobs_owner active (total reserve) (table active reserve cuts) t eta lam)
    (RefinedUpperRawPayments.jobs_checked active (total reserve) (table active reserve cuts) t eta lam)
    hbudget (startState active reserve cuts t eta) tape hstart
    (by simp [RecordedEndpoints, startState, initial, endpoints])
  exact ⟨h.1.1, h.2.1, h.2.2⟩

include hc in
theorem wholeAtoms_recorded (j : Fin k) :
    RecordedHistory (wholeAtoms active reserve cuts t eta j) reserve.history := by
  intro i p hp
  obtain ⟨c, hc', hp⟩ := hp
  exact hc.wellFormed.2.2.2 i p ⟨c, (List.mem_filter.mp hc').1, hp⟩

include hc in
theorem output_components
    (hrun : (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false)
    (j : Fin k) : DisjointComponents (output policy active reserve cuts t eta lam tape j) := by
  have hstart := UpperPendingExclusion.remove_wellFormed μ reserve hc.wellFormed cuts (whole active reserve cuts t eta)
  have hl : (corrections policy active reserve cuts t eta lam tape).length = k :=
    (RefinedUpperBatchLoop.successful_outputs policy (tasks active reserve cuts t eta lam)
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
    (hrun : (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false)
    (j : Fin k) : WellFormed μ (paymentState (executeStage policy active reserve cuts t eta lam tape) j) := by
  have hfinal := stage_recording μ policy hpolicy active hinj reserve cuts t eta lam N heta hlam hsize hmargin selected hc tape
  have hstart := UpperPendingExclusion.remove_wellFormed μ reserve hc.wellFormed cuts (whole active reserve cuts t eta)
  have hl : (corrections policy active reserve cuts t eta lam tape).length = k :=
    (RefinedUpperBatchLoop.successful_outputs policy (tasks active reserve cuts t eta lam)
      (startState active reserve cuts t eta).current tape hrun).1
  have hj := getD_mem (corrections policy active reserve cuts t eta lam tape) [] j.val (by rw [hl]; exact j.isLt)
  apply UpperComponentAssembly.state_wellFormed μ _ _
    (output_components μ policy active reserve cuts t eta lam N selected hc tape hrun j) hfinal.1.2.2.1
  apply UpperComponentAssembly.append_recorded
  · exact recordedHistory_mono _ (wholeAtoms_recorded μ active reserve cuts t eta N selected hc j) hfinal.2.1
  · exact payments_recordedHistory _ _ _
      (recordedHistory_mono _ hstart.2.2.2 hfinal.2.1) hfinal.2.2 _ hj

end EnvyFreeResearch.Full.RefinedUpperRepairFinalCache
