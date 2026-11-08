import EnvyFreeResearch.Full.UpperCorrectionReady
import EnvyFreeResearch.Full.UpperCorrectionPieces

/-! Physical exact owner payments and every checked normalized error for an
actual accepted correction, realized as finite recorded component lists. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperCorrectionAccepted

open UpperRecordedDomain UpperDomainDifference UpperGridCells UpperLogicalCells
  UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSupply UpperRawPayments
  UpperCorrectionSetup UpperCircularStage UpperCorrectionReady UpperWholePaymentsPhysical

variable {n k m : ℕ} [Nonempty (Fin k)]

def wholeAtoms (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (t : Fin k → ℝ) (eta : ℝ) (j : Fin k) : List Component :=
  reserve.cells.filter (UpperPendingExclusion.selected cuts (fun _ : Unit => whole active reserve cuts t eta j))

def correctionAtoms (policy : Policy n) (state : State n) (job : Job n) (start : UpperCircular.Circle) :
    List Component := UpperCorrectionPieces.take state.cells (descriptor policy state job.owner job.deficit start)

def completedAtoms (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ)
    (state : State n) (j : Fin k) (start : UpperCircular.Circle) : List Component :=
  wholeAtoms active reserve cuts t eta j ++ correctionAtoms policy state (tasks active reserve cuts t eta lam j) start

omit [Nonempty (Fin k)] in
theorem wholeAtoms_domain (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
    (t : Fin k → ℝ) (eta : ℝ) (j : Fin k) :
    domain (wholeAtoms active reserve cuts t eta j) =
      pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta j := by
  rw [wholeAtoms, UpperPendingExclusion.selected_domain]
  simp_rw [logicalAtoms_domain _ _ hzero hmono hsep]
  change (⋃ _ : Unit, pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta j) = _
  simp only [iUnion_const]

theorem correctionAtoms_domain (policy : Policy n) (state : State n) (job : Job n)
    (start : UpperCircular.Circle) :
    domain (correctionAtoms policy state job start) = payment policy state job.owner job.deficit start :=
  UpperCorrectionPieces.take_domain _ _

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (active : Fin k → Fin n) (hinj : Function.Injective active)
  (reserve : State n) (hreserve : WellFormed μ reserve)
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
  (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) reserve.cells)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain reserve.cells))
  (t : Fin k → ℝ) (eta lam : ℝ) (heta : 0 ≤ eta)
  (hsmall : ∀ i e, table active reserve cuts i e ≤ eta)
  (ht : ∀ j, 0 ≤ t j) (hsum : ∑ j, t j < 1 / 16) (hsize : (k : ℝ)^2 ≤ lam)

include hreserve hzero hmono hsep

omit [Nonempty (Fin k)] in
theorem pending_disjoint_current (state : State n)
    (hsub : domain state.cells ⊆ domain (startState active reserve cuts t eta).current.cells) (j : Fin k) :
    Disjoint (pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta j) (domain state.cells) := by
  have heq := UpperPendingExclusion.remove_domain reserve hreserve.2.1 cuts hzero hmono hsep
    (whole active reserve cuts t eta)
  apply Set.disjoint_left.mpr
  intro x hxY hxS
  have hx := hsub hxS
  change x ∈ domain (UpperPendingExclusion.remove reserve cuts (whole active reserve cuts t eta)).cells at hx
  rw [heq] at hx
  exact hx.2 (mem_iUnion.mpr ⟨j, hxY⟩)

include hone hpositive heta hsmall ht hsum hsize in
theorem completed_exact (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (buffer : Set ℝ) (j : Fin k) (state : LoopState n)
    (hsafe : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) j.castSucc state)
    (hsub : domain state.current.cells ⊆ domain (startState active reserve cuts t eta).current.cells)
    (start : UpperCircular.Circle) :
    (μ (active j)).real (domain (completedAtoms policy active reserve cuts t eta lam state.current j start)) =
      t j * (μ (active j)).real (domain reserve.cells) := by
  have hdis := pending_disjoint_current μ active reserve hreserve cuts hzero hmono hsep t eta state.current hsub j
  have hpay := UpperCorrectionReady.exact_deficit μ active reserve hreserve cuts hzero hone hmono hsep hpositive
    t eta lam heta hsmall ht hsum hsize policy hpolicy buffer j state hsafe start
  rw [completedAtoms, domain_append, wholeAtoms_domain active reserve cuts hzero hmono hsep,
    correctionAtoms_domain, measureReal_union
      (hdis.mono_right (payment_subset policy state.current _ _ start))
      (payment_measurableSet policy state.current _ _ start)]
  change (μ (active j)).real (pending _ _ _ _ _) +
    (μ (active j)).real (payment policy state.current (active j) _ start) = _
  rw [hpay]
  ring

include hinj hpositive heta hsmall ht hsum hsize hone in
/-- Every cached accepted inequality is the normalized physical inequality
for the literal completed output, in each checked original observer row. -/
theorem completed_error (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (buffer : Set ℝ) (j : Fin k) (state : LoopState n)
    (hsafe : Safe μ (activeSet active) buffer (fun i => 7 / 8 * (μ i).real (domain reserve.cells))
      (tasks active reserve cuts t eta lam) j.castSucc state)
    (hsub : domain state.current.cells ⊆ domain (startState active reserve cuts t eta).current.cells)
    (start : UpperCircular.Circle)
    (haccept : accepts (tasks active reserve cuts t eta lam j) state.current
      (execute policy state.current (active j) (tasks active reserve cuts t eta lam j).deficit start).2 = true)
    (i : Fin k) :
    |(μ (active i)).real (domain (completedAtoms policy active reserve cuts t eta lam state.current j start)) /
      (μ (active i)).real (domain reserve.cells) - t j| ≤
        lam * UpperPayments.cellGap (table active reserve cuts) i j := by
  have hf := UpperCorrectionReady.deficit_fits μ active reserve hreserve cuts hzero hone hmono hsep hpositive
    t eta lam heta hsmall ht hsum hsize buffer j state hsafe
  have hp : 0 < (μ (active j)).real (domain state.current.cells) := hf.1.trans_lt hf.2
  have hcheck := (accepts_physical_iff μ policy hpolicy state.current hsafe.1
    (tasks active reserve cuts t eta lam j) hp start).mp haccept (active i)
    (jobs_checked active (total reserve) (table active reserve cuts) t eta lam j _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  rw [tasks_previous_physical μ active reserve hreserve cuts hzero hmono hsep hpositive hinj t eta lam j _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)] at hcheck
  have hdesired : (tasks active reserve cuts t eta lam j).desired (active i) =
      t j * (μ (active i)).real (domain reserve.cells) := by
    simp only [tasks, recordedJobs, jobs, total_correct μ reserve hreserve]
  have htolerance : (tasks active reserve cuts t eta lam j).tolerance (active i) =
      lam * UpperPayments.cellGap (table active reserve cuts) i j *
        (μ (active i)).real (domain reserve.cells) := by
    simp only [tasks, recordedJobs, jobs, Function.leftInverse_invFun hinj i,
      total_correct μ reserve hreserve]
  rw [hdesired, htolerance] at hcheck
  have hdis := pending_disjoint_current μ active reserve hreserve cuts hzero hmono hsep t eta state.current hsub j
  have hm : (μ (active i)).real (domain (completedAtoms policy active reserve cuts t eta lam state.current j start)) =
      (μ (active i)).real (pending (cell (domain reserve.cells) cuts) (table active reserve cuts) t eta j) +
        (μ (active i)).real (payment policy state.current (active j)
          (tasks active reserve cuts t eta lam j).deficit start) := by
    rw [completedAtoms, domain_append, wholeAtoms_domain active reserve cuts hzero hmono hsep,
      correctionAtoms_domain, measureReal_union (hdis.mono_right (payment_subset policy state.current _ _ start))
        (payment_measurableSet policy state.current _ _ start)]
    rfl
  rw [hm]
  have heq (v : ℝ) : v / (μ (active i)).real (domain reserve.cells) - t j =
      (v - t j * (μ (active i)).real (domain reserve.cells)) / (μ (active i)).real (domain reserve.cells) := by
    field_simp [(hpositive i).ne']
  rw [heq, abs_div, abs_of_pos (hpositive i)]
  exact (div_le_iff₀ (hpositive i)).mpr hcheck

end EnvyFreeResearch.Full.UpperCorrectionAccepted
