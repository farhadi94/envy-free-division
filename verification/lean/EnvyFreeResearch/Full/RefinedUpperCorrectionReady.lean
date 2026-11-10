import EnvyFreeResearch.Full.RefinedUpperCorrectionSetup
import EnvyFreeResearch.Full.UpperAggregateInterpolationSupply
import EnvyFreeResearch.Full.UpperCorrections

/-! The concrete reserve setup discharges aggregate preparation facts and
pays the exact original-unit deficit at every reached correction. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.RefinedUpperCorrectionReady

open UpperRecordedDomain UpperDomainDifference UpperGridCells UpperLogicalCells
  UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply RefinedUpperRawPayments
  RefinedUpperCorrectionSetup UpperAggregateInterpolation UpperCircularStage

variable {n k m : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (active : Fin k → Fin n) (hinj : Function.Injective active)
  (reserve : State n) (hreserve : WellFormed μ reserve)
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
  (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells))
  (t : Fin k → ℝ) (eta lam : ℝ) (heta : 0 ≤ eta)
  (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
  (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j < 1 / 16) (hsize : 4 * (k : ℝ) ≤ lam)

include hinj hreserve hzero hone hmono hsep hpositive heta hsmall ht hsum hsize

/-- All fields of the aggregate preparation interface are supplied by the
actual normalized-cache/floating/rounding/filtering implementation. -/
theorem preparationFacts (buffer : Set ℝ) (hsub : domain reserve.cells ⊆ buffer)
    (q : ℝ) (hreserveMass : ∀ i, q / 2 * (μ (active i)).real buffer ≤
      (μ (active i)).real (domain reserve.cells))
    (hmargin : (k : ℝ) * lam * eta < 1 / 16) :
    PreparationFacts μ (activeSet active) buffer q (tasks active reserve cuts t eta lam)
      (startState active reserve cuts t eta).current (domain reserve.cells)
      (pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta) := by
  have hlam : 0 ≤ lam := (show (0 : ℝ) ≤ 4 * k by positivity).trans hsize
  refine ⟨UpperPendingExclusion.remove_wellFormed μ reserve hreserve cuts _, hsub,
    UpperPendingExclusion.remove_domain reserve hreserve.2.1 cuts hzero hmono hsep _,
    tasks_previous_physical μ active reserve hreserve cuts hzero hmono hsep hpositive hinj t eta lam,
    ?_, ?_, jobs_checked active (total reserve) (table active reserve cuts) t eta lam, ?_⟩
  · intro i hi
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    have hscale : 0 < total reserve (active r) := by rw [total_correct μ reserve hreserve]; exact hpositive r
    have h := jobs_cap_sum active (total reserve) (table active reserve cuts) t eta lam heta hlam
      (table_nonneg μ active reserve hreserve cuts hzero hmono hsep hpositive) hsmall hsum hmargin (active r) hscale
    simpa only [tasks, recordedJobs, total_correct μ reserve hreserve] using h
  · intro i hi
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    exact hreserveMass r
  · intro j i _
    exact tasks_budget_nonneg μ active reserve hreserve cuts hzero hone hmono hsep hpositive
      t eta lam heta hsmall ht hsum hsize j i

omit hinj in
/-- The clipping in the physical executor is inactive at every reached safe
state, because the actual normalized rounded deficit fits the raw supply. -/
theorem deficit_fits (buffer : Set ℝ) (time : Fin k) (state : LoopState n)
    (hsafe : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) time.castSucc state) :
    0 ≤ (tasks active reserve cuts t eta lam time).deficit ∧
      (tasks active reserve cuts t eta lam time).deficit <
        (μ (active time)).real (domain state.current.cells) := by
  have hscale (i : Fin n) : 0 ≤ total reserve i := by
    rw [total_correct μ reserve hreserve]
    exact measureReal_nonneg
  have hdef := jobs_deficit_bounds active (total reserve) hscale (table active reserve cuts) t eta lam heta
    (table_nonneg μ active reserve hreserve cuts hzero hmono hsep hpositive) hsmall
    (table_normalized μ active reserve hreserve cuts hzero hone hmono hsep hpositive) ht (by linarith) time
  have htarget : t time < 1 / 16 :=
    (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ time)).trans_lt hsum
  have hsupply := safe_mass μ (activeSet active) buffer _ (tasks active reserve cuts t eta lam)
    time.castSucc state hsafe
    (fun j i _ => tasks_budget_nonneg μ active reserve hreserve cuts hzero hone hmono hsep hpositive
      t eta lam heta hsmall ht hsum hsize j i)
    (active time) (Finset.mem_image.mpr ⟨time, Finset.mem_univ _, rfl⟩)
  have hm := mul_lt_mul_of_pos_right htarget (hpositive time)
  have hupper := hdef.2.1
  rw [total_correct μ reserve hreserve] at hupper
  refine ⟨hdef.1, ?_⟩
  change (jobs active (total reserve) (table active reserve cuts) t eta lam time).deficit < _
  nlinarith [hupper]

omit hinj in
theorem exact_deficit (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (buffer : Set ℝ) (time : Fin k) (state : LoopState n)
    (hsafe : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) time.castSucc state) (start : UpperCircular.Circle) :
    (μ (active time)).real (payment policy state.current (active time)
      (tasks active reserve cuts t eta lam time).deficit start) =
        t time * (μ (active time)).real (domain reserve.cells) -
          (μ (active time)).real
            (pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta time) := by
  have hf := deficit_fits μ active reserve hreserve cuts hzero hone hmono hsep hpositive
    t eta lam heta hsmall ht hsum hsize buffer time state hsafe
  have hpos : 0 < (μ (active time)).real (domain state.current.cells) := hf.1.trans_lt hf.2
  rw [payment_exact μ policy hpolicy state.current hsafe.1 (active time) hpos _ hf.1 hf.2.le]
  have h := jobs_owner_deficit μ active _ (cell_measurable _ (domain_measurable _) _)
    (cells_disjoint _ _ hmono) (total reserve) (table active reserve cuts)
    (table_scaled μ active reserve hreserve cuts hzero hmono hsep hpositive) t eta lam time
  simpa only [tasks, recordedJobs, total_correct μ reserve hreserve] using h

end EnvyFreeResearch.Full.RefinedUpperCorrectionReady
