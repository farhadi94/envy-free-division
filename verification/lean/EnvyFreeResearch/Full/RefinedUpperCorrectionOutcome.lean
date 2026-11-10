import EnvyFreeResearch.Full.RefinedUpperCorrectionAccepted
import EnvyFreeResearch.Full.RefinedUpperBatchVerification
import EnvyFreeResearch.Full.RefinedUpperRetrySupply

/-! Concrete successful finite correction outputs and their physical values. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.RefinedUpperCorrectionOutcome

open UpperRecordedDomain UpperDomainDifference UpperGridCells UpperLogicalCells
  UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply RefinedUpperRawPayments
  RefinedUpperCorrectionSetup UpperCircularStage RefinedUpperCorrectionAccepted UpperCorrectionPieces
  UpperCorrectionTrace RefinedUpperBatchVerification

variable {n k m r : ℕ} [Nonempty (Fin k)]

def corrections (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    List (List Component) :=
  payments (startState active reserve cuts t eta).current.cells
    (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.accepted

def output (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle)
    (j : Fin k) : List Component :=
  wholeAtoms active reserve cuts t eta j ++ (corrections policy active reserve cuts t eta lam tape)[j.val]?.getD []

def Correct (μ : Fin n → Measure ℝ) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (j : Fin k) (correction : List Component) : Prop :=
  (μ (active j)).real (domain (wholeAtoms active reserve cuts t eta j ++ correction)) =
    t j * (μ (active j)).real (domain reserve.cells) ∧
  ∀ i, |(μ (active i)).real (domain (wholeAtoms active reserve cuts t eta j ++ correction)) /
    (μ (active i)).real (domain reserve.cells) - t j| ≤ lam * UpperPayments.cellGap (table active reserve cuts) i j

omit [Nonempty (Fin k)] in
theorem forall₂_getD {α β : Type*} (P : α → β → Prop) {r : ℕ} (f : Fin r → α)
    (out : List β) (fallback : β) (h : List.Forall₂ P (List.ofFn f) out) (i : Fin r) :
    P (f i) (out[i.val]?.getD fallback) := by
  induction r generalizing out with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    rw [List.ofFn_succ] at h
    obtain ⟨b, tail, hhead, htail, rfl⟩ := List.forall₂_cons_left_iff.mp h
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hhead
    · simpa using ih (fun j => f j.succ) tail htail j


variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (active : Fin k → Fin n) (hinj : Function.Injective active)
  (reserve : State n) (hreserve : WellFormed μ reserve)
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
  (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells))
  (t : Fin k → ℝ) (eta lam : ℝ) (heta : 0 ≤ eta)
  (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
  (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j < 1 / 16) (hsize : 4 * (k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)

include hinj hreserve hzero hone hmono hsep hpositive heta hsmall ht hsum hsize hmargin

/-- Success of the real stopped loop gives each actual reconstructed payment
its exact owner mass and all checked normalized physical inequalities. -/
theorem successful_correct (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (tape : Fin k → Fin r → UpperCircular.Circle)
    (hrun : (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false) :
    List.Forall₂ (Correct μ active reserve cuts t eta lam) (List.ofFn (fun j : Fin k => j))
      (corrections policy active reserve cuts t eta lam tape) := by
  let origin := startState active reserve cuts t eta
  let job := tasks active reserve cuts t eta lam
  let Inv (time : Fin (k + 1)) (state : LoopState n) :=
    Safe μ (activeSet active) (domain reserve.cells) (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      job time state ∧ domain state.current.cells ⊆ domain origin.current.cells
  let P (task : Job n) (corr : List Component) :=
    Correct μ active reserve cuts t eta lam (Function.invFun active task.owner) corr
  have hstart : Inv 0 origin := ⟨start_safe μ active reserve hreserve cuts hzero hmono hsep hpositive hinj
    (domain reserve.cells) Subset.rfl t eta lam heta ((show (0 : ℝ) ≤ 4*k by positivity).trans hsize) hsmall hsum hmargin, Subset.rfl⟩
  have hbudget (j : Fin k) (i : Fin n) : 0 ≤ budget (job j) i :=
    tasks_budget_nonneg μ active reserve hreserve cuts hzero hone hmono hsep hpositive
      t eta lam heta hsmall ht hsum hsize j i
  have hfloor (i : Fin n) (hi : i ∈ activeSet active) :
      0 < (7:ℝ) / 8 * (μ i).real (domain reserve.cells) := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact mul_pos (by norm_num) (hpositive j)
  have hretry (i : Fin k) (state : LoopState n) (start : UpperCircular.Circle)
      (hs : Inv i.castSucc state) (_ : state.stopped = false)
      (hr : (step policy state (job i, start)).1 = true) :
      Inv i.castSucc (RefinedUpperCorrectionRetries.reopen (step policy state (job i, start)).2) := by
    have hf := RefinedUpperCorrectionReady.deficit_fits μ active reserve hreserve cuts hzero hone
      hmono hsep hpositive t eta lam heta hsmall ht hsum hsize (domain reserve.cells) i state hs.1
    have hw := step_wellFormed μ policy hpolicy state hs.1.1 (job i, start)
      (fun _ => hf.1.trans_lt hf.2)
    have he := RefinedUpperBatchUnroll.step_rejected policy state (job i) start hr
    refine ⟨⟨hw, ?_, ?_⟩, ?_⟩
    · simpa only [RefinedUpperCorrectionRetries.reopen, he.1] using hs.1.2.1
    · simpa only [RefinedUpperCorrectionRetries.reopen, he.1] using hs.1.2.2
    · simpa only [RefinedUpperCorrectionRetries.reopen, he.1] using hs.2
  have hpreserve (i : Fin k) (state : LoopState n) (packet : Fin r → UpperCircular.Circle)
      (hs : Inv i.castSucc state) :
      Inv i.succ (RefinedUpperCorrectionRetries.batch policy (job i) state packet) := by
    refine ⟨?_, (RefinedUpperRetryTrace.batch_domain_subset policy (job i) state packet).trans hs.2⟩
    exact RefinedUpperRetrySupply.batch_safe μ policy hpolicy (activeSet active) (domain reserve.cells)
      (fun i => 7/8*(μ i).real (domain reserve.cells)) hfloor job
      (jobs_owner active (total reserve) (table active reserve cuts) t eta lam)
      (jobs_checked active (total reserve) (table active reserve cuts) t eta lam)
      (fun j i _ => hbudget j i) i state hs.1 r packet
  have hlocal (i : Fin k) (state : LoopState n) (start : UpperCircular.Circle)
      (hs : Inv i.castSucc state) (_ : state.stopped = false)
      (haccept : accepts (job i) state.current (execute policy state.current (job i).owner (job i).deficit start).2 = true) :
      P (job i) (take state.current.cells (descriptor policy state.current (job i).owner (job i).deficit start)) := by
    have hindex : Function.invFun active (job i).owner = i := Function.leftInverse_invFun hinj i
    change Correct μ active reserve cuts t eta lam (Function.invFun active (job i).owner) _
    rw [hindex]
    exact ⟨completed_exact μ active reserve hreserve cuts hzero hone hmono hsep hpositive
      t eta lam heta hsmall ht hsum hsize policy hpolicy (domain reserve.cells) i state hs.1 hs.2 start,
      completed_error μ active hinj reserve hreserve cuts hzero hone hmono hsep hpositive
        t eta lam heta hsmall ht hsum hsize policy hpolicy (domain reserve.cells) i state hs.1 hs.2 start haccept⟩
  obtain ⟨records, hrecords, _, hproperties⟩ := run_success_properties policy job Inv hretry hpreserve P hlocal origin tape hstart hrun
  have heq : (RefinedUpperBatchLoop.run policy job origin tape).2.accepted = records := by
    simpa only [origin, startState, initial, List.nil_append] using hrecords
  change List.Forall₂ _ _ (payments origin.current.cells (RefinedUpperBatchLoop.run policy job origin tape).2.accepted)
  rw [heq]
  have hindexed : List.Forall₂ (fun j corr => P (job j) corr) (List.ofFn (fun j : Fin k => j))
      (payments origin.current.cells records) := by
    rw [← List.forall₂_map_left_iff, List.map_ofFn]
    exact hproperties
  have hinverse (j : Fin k) : Function.invFun active (active j) = j := Function.leftInverse_invFun hinj j
  simpa only [P, job, tasks, recordedJobs, jobs, hinverse] using hindexed

/-- Values of the actual finite-index output function, including the literal
component list selected by each recipient index. -/
theorem output_values (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (tape : Fin k → Fin r → UpperCircular.Circle)
    (hrun : (RefinedUpperBatchLoop.run policy (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape).2.stopped = false)
    (j : Fin k) :
    (μ (active j)).real (domain (output policy active reserve cuts t eta lam tape j)) =
      t j * (μ (active j)).real (domain reserve.cells) ∧
    ∀ i, |(μ (active i)).real (domain (output policy active reserve cuts t eta lam tape j)) /
      (μ (active i)).real (domain reserve.cells) - t j| ≤ lam * UpperPayments.cellGap (table active reserve cuts) i j := by
  have h := successful_correct μ active hinj reserve hreserve cuts hzero hone hmono hsep hpositive
    t eta lam heta hsmall ht hsum hsize hmargin policy hpolicy tape hrun
  exact forall₂_getD _ _ _ [] h j

end EnvyFreeResearch.Full.RefinedUpperCorrectionOutcome
