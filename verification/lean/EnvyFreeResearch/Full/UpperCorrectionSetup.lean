import EnvyFreeResearch.Full.UpperPendingExclusion

/-!
# Concrete initialization of corrections from the recorded reserve

The normalized cache, whole-payment selector, original-unit jobs and literal
remaining state are all computed from one recorded reserve. Their physical
identities initialize and preserve the actual-loop supply invariant.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperCorrectionSetup

open UpperRecordedDomain UpperDomainDifference UpperGridCells UpperLogicalCells
  UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply UpperRawPayments

variable {n k m : ℕ}

def table (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (i : Fin k) (e : Fin (m + 1)) : ℝ :=
  cachedMass reserve cuts (active i) e / total reserve (active i)

def whole (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (t : Fin k → ℝ) (eta : ℝ) : Fin k → Finset (Fin (m + 1)) :=
  UpperPayments.allocation (table active reserve cuts) t eta

def startState (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (t : Fin k → ℝ) (eta : ℝ) : LoopState n :=
  initial (UpperPendingExclusion.remove reserve cuts (whole active reserve cuts t eta))

variable [Nonempty (Fin k)]

def tasks (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (t : Fin k → ℝ) (eta lam : ℝ) : Fin k → Job n :=
  recordedJobs active reserve (table active reserve cuts) t eta lam

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (active : Fin k → Fin n) (reserve : State n) (hreserve : WellFormed μ reserve)
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
  (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells))

include hreserve hzero hmono hsep

omit [Nonempty (Fin k)] in
theorem table_correct (i : Fin k) (e : Fin (m + 1)) :
    table active reserve cuts i e = (μ (active i)).real (cell (domain reserve.cells) cuts e) /
      (μ (active i)).real (domain reserve.cells) := by
  rw [table, cachedMass_correct μ reserve hreserve cuts hzero hmono hsep, total_correct μ reserve hreserve]

include hpositive in
omit [Nonempty (Fin k)] in
theorem table_nonneg (i : Fin k) (e : Fin (m + 1)) : 0 ≤ table active reserve cuts i e := by
  rw [table_correct μ active reserve hreserve cuts hzero hmono hsep]
  exact div_nonneg measureReal_nonneg (hpositive i).le

include hone hpositive in
omit [Nonempty (Fin k)] in
theorem table_normalized (i : Fin k) : ∑ e, table active reserve cuts i e = 1 := by
  simp_rw [table_correct μ active reserve hreserve cuts hzero hmono hsep]
  rw [← Finset.sum_div, cell_mass_sum (μ (active i)) (domain reserve.cells) (domain_measurable _)
    cuts hmono (by rw [hzero, hone]; exact domain_subset_unit _)]
  exact div_self (hpositive i).ne'

include hpositive in
omit [Nonempty (Fin k)] in
theorem table_scaled (i : Fin k) (e : Fin (m + 1)) :
    table active reserve cuts i e * total reserve (active i) =
      (μ (active i)).real (cell (domain reserve.cells) cuts e) := by
  rw [total_correct μ reserve hreserve, table_correct μ active reserve hreserve cuts hzero hmono hsep,
    div_mul_cancel₀ _ (hpositive i).ne']

include hone hpositive in
/-- All arithmetic budgets come from the actual floating/rounding result and
recorded reserve scale, rather than from assumed physical payments. -/
theorem tasks_budget_nonneg (t : Fin k → ℝ) (eta lam : ℝ)
    (heta : 0 ≤ eta) (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
    (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j < 1 / 16) (hsize : (k : ℝ)^2 ≤ lam)
    (j : Fin k) (i : Fin n) : 0 ≤ budget (tasks active reserve cuts t eta lam j) i := by
  apply jobs_budget_nonneg active (total reserve) _ _ _ _ _ heta
    (table_nonneg μ active reserve hreserve cuts hzero hmono hsep hpositive) hsmall
    (table_normalized μ active reserve hreserve cuts hzero hone hmono hsep hpositive) ht
    (by linarith) hsize
  intro r
  rw [total_correct μ reserve hreserve]
  exact measureReal_nonneg

include hpositive in
theorem tasks_previous_physical (hinj : Function.Injective active) (t : Fin k → ℝ) (eta lam : ℝ)
    (j : Fin k) (i : Fin n) (hi : i ∈ activeSet active) :
    (tasks active reserve cuts t eta lam j).previous i =
      (μ i).real (pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta j) := by
  exact jobs_previous_physical μ active hinj _
    (cell_measurable _ (domain_measurable _) _) (cells_disjoint _ _ hmono) (total reserve)
    (table active reserve cuts) (table_scaled μ active reserve hreserve cuts hzero hmono hsep hpositive)
    t eta lam j i hi

include hpositive in
/-- The actual filtered initial state satisfies the time-zero potential. -/
theorem start_safe (hinj : Function.Injective active) (buffer : Set ℝ)
    (hsub : domain reserve.cells ⊆ buffer) (t : Fin k → ℝ) (eta lam : ℝ)
    (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
    (hsum : ∑ j, t j < 1 / 16) (hmargin : (k : ℝ) * lam * eta < 1 / 16) :
    Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) 0 (startState active reserve cuts t eta) := by
  apply safe_initial μ (activeSet active) buffer (domain reserve.cells) hsub
    (tasks active reserve cuts t eta lam)
    (pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta)
    (UpperPendingExclusion.remove reserve cuts (whole active reserve cuts t eta))
    (UpperPendingExclusion.remove_wellFormed μ reserve hreserve _ _)
  · exact UpperPendingExclusion.remove_domain reserve hreserve.2.1 cuts hzero hmono hsep _
  · exact tasks_previous_physical μ active reserve hreserve cuts hzero hmono hsep hpositive hinj t eta lam
  · intro i hi
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    have hscale : 0 < total reserve (active r) := by rw [total_correct μ reserve hreserve]; exact hpositive r
    have h := jobs_cap_sum active (total reserve) (table active reserve cuts) t eta lam heta hlam
      (table_nonneg μ active reserve hreserve cuts hzero hmono hsep hpositive) hsmall hsum hmargin (active r) hscale
    simpa only [tasks, recordedJobs, total_correct μ reserve hreserve] using h

include hone hpositive in
theorem tasks_safe_step (policy : UpperCircularStage.Policy n)
    (hpolicy : UpperCircularStage.Admissible (Chores.measureProfile μ) policy)
    (buffer : Set ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (heta : 0 ≤ eta) (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
    (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j < 1 / 16) (hsize : (k : ℝ)^2 ≤ lam)
    (time : Fin k) (state : LoopState n) (draw : UpperCircular.Circle)
    (hsafe : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) time.castSucc state) :
    Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) time.succ
      (step policy state (tasks active reserve cuts t eta lam time, draw)).2 := by
  apply safe_step μ policy hpolicy (activeSet active) buffer _ _ _
    (jobs_owner active (total reserve) (table active reserve cuts) t eta lam)
    (jobs_checked active (total reserve) (table active reserve cuts) t eta lam)
    (fun j i _ => tasks_budget_nonneg μ active reserve hreserve cuts hzero hone hmono hsep hpositive
      t eta lam heta hsmall ht hsum hsize j i) time state draw hsafe
  intro i hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  exact mul_pos (by norm_num) (hpositive r)

end Correctness

section Measurability

variable {X : Type*} [MeasurableSpace X]

omit [Nonempty (Fin k)] in
theorem table_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (hreserve : Measurable reserve)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (i : Fin k) (e : Fin (m + 1)) :
    Measurable (fun z => table active (reserve z) (cuts z) i e) :=
  (cachedMass_measurable reserve cuts hreserve hcuts (active i) e).div
    (total_measurable reserve (fun _ => active i) hreserve measurable_const)

omit [Nonempty (Fin k)] in
theorem whole_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (t : X → Fin k → ℝ) (eta : X → ℝ)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) :
    Measurable (fun z => whole active (reserve z) (cuts z) (t z) (eta z)) :=
  UpperPayments.allocation_measurable _ t eta (table_measurable active reserve cuts hreserve hcuts) ht heta

omit [Nonempty (Fin k)] in
theorem startState_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (t : X → Fin k → ℝ) (eta : X → ℝ)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) :
    Measurable (fun z => startState active (reserve z) (cuts z) (t z) (eta z)) :=
  loop_mk_measurable _ _ _
    (UpperPendingExclusion.remove_measurable reserve cuts _ hreserve hcuts
      (fun j => (measurable_pi_apply j).comp (whole_measurable active reserve cuts t eta hreserve hcuts ht heta)))
    measurable_const measurable_const

theorem tasks_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (t : X → Fin k → ℝ) (eta lam : X → ℝ)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (hlam : Measurable lam) :
    Measurable (fun z => tasks active (reserve z) (cuts z) (t z) (eta z) (lam z)) :=
  recordedJobs_measurable active reserve _ t eta lam hreserve
    (table_measurable active reserve cuts hreserve hcuts) ht heta hlam

end Measurability

end EnvyFreeResearch.Full.UpperCorrectionSetup
