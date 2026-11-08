import EnvyFreeResearch.Full.UpperCorrectionLoop

/-!
# Remaining-mass invariant for the actual stopped correction loop

The potential keeps the budgets of unattempted jobs. Acceptance consumes at
most its target plus tolerance minus the already allocated whole-cell mass.
This cancellation avoids charging the whole-cell payment a second time.
All statements use the original, unnormalized oracle measures.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperCorrectionSupply

open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperRecordedDomain

abbrev Circle := UpperCircular.Circle

variable {n m : ℕ}

def budget (job : Job n) (observer : Fin n) : ℝ :=
  job.desired observer + job.tolerance observer - job.previous observer

def tailBudget (jobs : Fin m → Job n) (time : ℕ) (observer : Fin n) : ℝ :=
  ∑ j, if time ≤ j.val then budget (jobs j) observer else 0

theorem tailBudget_nonneg (jobs : Fin m → Job n) (time : ℕ) (observer : Fin n)
    (hbudget : ∀ j, 0 ≤ budget (jobs j) observer) : 0 ≤ tailBudget jobs time observer := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> first | exact hbudget j | exact le_rfl

theorem tailBudget_zero (jobs : Fin m → Job n) (observer : Fin n) :
    tailBudget jobs 0 observer = ∑ j, budget (jobs j) observer := by
  simp [tailBudget]

theorem tailBudget_last (jobs : Fin m → Job n) (observer : Fin n) :
    tailBudget jobs m observer = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  simp [Nat.not_le.mpr j.isLt]

theorem tailBudget_succ (jobs : Fin m → Job n) (time : Fin m) (observer : Fin n) :
    tailBudget jobs time.val observer = budget (jobs time) observer +
      tailBudget jobs (time.val + 1) observer := by
  have hpoint (j : Fin m) :
      (if time.val ≤ j.val then budget (jobs j) observer else 0) =
        (if j = time then budget (jobs j) observer else 0) +
        (if time.val + 1 ≤ j.val then budget (jobs j) observer else 0) := by
    by_cases heq : j = time
    · subst j
      simp
    · have hne : j.val ≠ time.val := fun h => heq (Fin.ext h)
      by_cases hle : time.val ≤ j.val
      · have hs : time.val + 1 ≤ j.val := by omega
        simp [heq, hle, hs]
      · have hs : ¬ time.val + 1 ≤ j.val := by omega
        simp [heq, hle, hs]
  simp_rw [tailBudget, hpoint, Finset.sum_add_distrib]
  simp

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

/-- The time-dependent invariant is about the actual recorded state. -/
def Safe (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (jobs : Fin m → Job n) (time : Fin (m + 1)) (state : LoopState n) : Prop :=
  WellFormed μ state.current ∧ domain state.current.cells ⊆ buffer ∧
    ∀ i ∈ active, floor i + tailBudget jobs time.val i < (μ i).real (domain state.current.cells)

theorem safe_mass (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (jobs : Fin m → Job n) (time : Fin (m + 1)) (state : LoopState n)
    (hsafe : Safe μ active buffer floor jobs time state)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i) (i : Fin n) (hi : i ∈ active) :
    floor i < (μ i).real (domain state.current.cells) := by
  have h := tailBudget_nonneg jobs time.val i (fun j => hbudget j i hi)
  linarith [hsafe.2.2 i hi]

/-- The actual acceptance check supplies the decrement bound. -/
theorem accepted_decrement (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (state : State n) (hstate : WellFormed μ state) (job : Job n)
    (hpositive : 0 < (μ job.owner).real (domain state.cells)) (start : Circle)
    (haccept : accepts job state (execute policy state job.owner job.deficit start).2 = true)
    (i : Fin n) (hi : job.checked i = true) :
    (μ i).real (domain state.cells) - budget job i ≤
      (μ i).real (domain (execute policy state job.owner job.deficit start).2.cells) := by
  have h := (accepts_physical_iff μ policy hpolicy state hstate job hpositive start).mp haccept i hi
  have hpayment := observedPayment_correct μ policy hpolicy state hstate job.owner hpositive job.deficit start i
  have hnext := execute_wellFormed μ policy hpolicy state hstate job.owner hpositive job.deficit start
  unfold observedPayment at hpayment
  rw [total_correct μ state hstate i, total_correct μ _ hnext i] at hpayment
  have hupper := (le_abs_self _).trans h
  unfold budget
  linarith

/-- Every branch preserves supply: rejected proposals retain all answers but
restore the domain, and stopped states make no transaction. -/
theorem safe_step (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Finset (Fin n)) (buffer : Set ℝ) (floor : Fin n → ℝ)
    (hfloor : ∀ i ∈ active, 0 < floor i) (jobs : Fin m → Job n)
    (howner : ∀ j, (jobs j).owner ∈ active)
    (hchecked : ∀ j i, i ∈ active → (jobs j).checked i = true)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (time : Fin m) (state : LoopState n) (start : Circle)
    (hsafe : Safe μ active buffer floor jobs time.castSucc state) :
    Safe μ active buffer floor jobs time.succ (step policy state (jobs time, start)).2 := by
  have hpositive : 0 < (μ (jobs time).owner).real (domain state.current.cells) :=
    (hfloor _ (howner time)).trans
      (safe_mass μ active buffer floor jobs time.castSucc state hsafe hbudget _ (howner time))
  have hwf := step_wellFormed μ policy hpolicy state hsafe.1 (jobs time, start) (fun _ => hpositive)
  refine ⟨hwf, ?_, ?_⟩
  · by_cases hstop : state.stopped = true
    · rw [step_stopped policy state (jobs time, start) hstop]
      exact hsafe.2.1
    · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
      simp only [step, hopen, Bool.false_eq_true, ite_false]
      split_ifs
      · have hsub : domain (execute policy state.current (jobs time).owner (jobs time).deficit start).2.cells ⊆
            domain state.current.cells := by rw [execute_domain]; exact Set.sdiff_subset
        exact hsub.trans hsafe.2.1
      · exact hsafe.2.1
  · intro i hi
    have hold := hsafe.2.2 i hi
    have hsplit := tailBudget_succ jobs time i
    have hnonneg := hbudget time i hi
    change floor i + tailBudget jobs (time.val + 1) i < _
    change floor i + tailBudget jobs time.val i < _ at hold
    by_cases hstop : state.stopped = true
    · rw [step_stopped policy state (jobs time, start) hstop]
      dsimp only
      linarith
    · have hopen : state.stopped = false := Bool.eq_false_iff.mpr hstop
      simp only [step, hopen, Bool.false_eq_true, ite_false]
      split_ifs with haccept
      · have hdecr := accepted_decrement μ policy hpolicy state.current hsafe.1 (jobs time)
          hpositive start haccept i (hchecked time i hi)
        dsimp only
        linarith
      · dsimp only
        linarith

/-- Initialization is derived from literal exclusion of the actual pending
whole-cell payments and their exact physical cached masses. -/
theorem safe_initial (active : Finset (Fin n)) (buffer reserve : Set ℝ)
    (hreserve : reserve ⊆ buffer) (jobs : Fin m → Job n) (pending : Fin m → Set ℝ)
    (state : State n) (hstate : WellFormed μ state)
    (hdomain : domain state.cells = reserve \ ⋃ j, pending j)
    (hprevious : ∀ j i, i ∈ active → (jobs j).previous i = (μ i).real (pending j))
    (hcap : ∀ i ∈ active, (∑ j, ((jobs j).desired i + (jobs j).tolerance i)) < (μ i).real reserve / 8) :
    Safe μ active buffer (fun i => 7 / 8 * (μ i).real reserve) jobs 0 (initial state) := by
  refine ⟨hstate, ?_, ?_⟩
  · change domain state.cells ⊆ buffer
    rw [hdomain]
    exact Set.sdiff_subset.trans hreserve
  · intro i hi
    change 7 / 8 * (μ i).real reserve + tailBudget jobs 0 i < (μ i).real (domain state.cells)
    have hdiff := le_measureReal_sdiff (μ := μ i) (s₁ := reserve) (s₂ := ⋃ j, pending j)
    have hunion := measureReal_iUnion_fintype_le (μ := μ i) pending
    have hprev : (∑ j, (jobs j).previous i) = ∑ j, (μ i).real (pending j) :=
      Finset.sum_congr rfl (fun j _ => hprevious j i hi)
    have hsplit : tailBudget jobs 0 i = (∑ j, ((jobs j).desired i + (jobs j).tolerance i)) -
        ∑ j, (jobs j).previous i := by
      simp [tailBudget_zero, budget, Finset.sum_sub_distrib]
    rw [hdomain]
    linarith [hcap i hi]

/-- The reserve preparation check implies the raw lower bound used in the
conditional endpoint-law domination. -/
theorem raw_supply (active : Finset (Fin n)) (buffer reserve : Set ℝ)
    (jobs : Fin m → Job n) (time : Fin (m + 1)) (state : LoopState n)
    (hsafe : Safe μ active buffer (fun i => 7 / 8 * (μ i).real reserve) jobs time state)
    (hbudget : ∀ j i, i ∈ active → 0 ≤ budget (jobs j) i)
    (q : ℝ) (hq : 0 ≤ q) (hreserve : ∀ i ∈ active, q / 2 * (μ i).real buffer ≤ (μ i).real reserve)
    (i : Fin n) (hi : i ∈ active) :
    q / 4 * (μ i).real buffer ≤ (μ i).real (domain state.current.cells) := by
  have h := safe_mass μ active buffer _ jobs time state hsafe hbudget i hi
  have hm : 0 ≤ (μ i).real buffer := measureReal_nonneg
  have hqr : 0 ≤ q * (μ i).real buffer := mul_nonneg hq hm
  nlinarith [hreserve i hi]

end EnvyFreeResearch.Full.UpperCorrectionSupply
