import EnvyFreeResearch.Full.UpperRepresentativeSupply
import EnvyFreeResearch.Full.UpperRecordedParents
import EnvyFreeResearch.Full.UpperWitnessExtraction

/-!
# Representative supply from the actual logical-cell cache

A normalized finite row and small parent-fiber sums force an available cell.
This proves completion of the existing deterministic representative loop for
logical cells, without requiring each logical cell to be one interval.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRepresentativeSupply UpperRepresentatives UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperCommonGrid Chores

variable {Cell Parent Row : Type*} [Fintype Cell] [DecidableEq Parent]

theorem table_available_nonempty (weights : Cell → ℝ) (parent : Cell → Parent)
    (removed : Finset Parent) (eta : ℝ) (cells : List Cell) (hlisted : ∀ c, c ∈ cells)
    (hnormalized : ∑ c, weights c = 1)
    (hsmall : ∀ p ∈ removed, (∑ c, if parent c = p then weights c else 0) ≤ eta)
    (hbudget : (removed.card : ℝ) * eta < 1) : available parent removed cells ≠ [] := by
  intro hempty
  have hcover (c : Cell) : parent c ∈ removed := by
    by_contra hnot
    have hm := (mem_available parent removed cells c).mpr ⟨hlisted c, hnot⟩
    simp [hempty] at hm
  have hsum : (∑ c, weights c) = ∑ p ∈ removed, ∑ c, if parent c = p then weights c else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    simp [hcover c]
  have hle : (1 : ℝ) ≤ (removed.card : ℝ) * eta := by
    rw [← hnormalized, hsum]
    calc
      _ ≤ ∑ _p ∈ removed, eta := Finset.sum_le_sum hsmall
      _ = _ := by simp
  linarith

/-- Completion is derived from the finite table, not assumed for any round. -/
theorem table_run_completes (weights : Cell → ℝ) (parent : Cell → Parent)
    (eta : ℝ) (heta : 0 ≤ eta) (cells : List Cell) (hlisted : ∀ c, c ∈ cells)
    (hnormalized : ∑ c, weights c = 1)
    (hsmall : ∀ p, (∑ c, if parent c = p then weights c else 0) ≤ eta)
    (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (jobs : List (Row × Row)) (removed : Finset Parent)
    (hbudget : ((removed.card + 2 * jobs.length : ℕ) : ℝ) * eta < 1) :
    ∃ pairs final, run values parent cells jobs removed = some (pairs, final) ∧
      pairs.length = jobs.length ∧ removed ⊆ final ∧ final.card ≤ removed.card + 2 * jobs.length := by
  induction jobs generalizing removed with
  | nil => exact ⟨[], removed, rfl, rfl, Subset.rfl, by simp⟩
  | cons job jobs ih =>
    have hcurrent : (removed.card : ℝ) * eta < 1 := by
      have hle : (removed.card : ℝ) ≤ ((removed.card + 2 * (job :: jobs).length : ℕ) : ℝ) := by
        exact_mod_cast (by omega : removed.card ≤ removed.card + 2 * (job :: jobs).length)
      exact (mul_le_mul_of_nonneg_right hle heta).trans_lt hbudget
    have havailable := table_available_nonempty weights parent removed eta cells hlisted
      hnormalized (fun p _ => hsmall p) hcurrent
    obtain ⟨first, last, hselect, _, _, _⟩ := select_spec (values job.1) (values job.2)
      (available parent removed cells) havailable (fun c _ => hnonneg _ c) (fun c _ => hnonneg _ c)
    have hcard := addParents_card_le parent (first, last) removed
    have hnext : (((addParents parent (first, last) removed).card + 2 * jobs.length : ℕ) : ℝ) * eta < 1 := by
      have hle : (((addParents parent (first, last) removed).card + 2 * jobs.length : ℕ) : ℝ) ≤
          ((removed.card + 2 * (job :: jobs).length : ℕ) : ℝ) := by
        exact_mod_cast (by simp only [List.length_cons]; omega :
          (addParents parent (first, last) removed).card + 2 * jobs.length ≤
            removed.card + 2 * (job :: jobs).length)
      exact (mul_le_mul_of_nonneg_right hle heta).trans_lt hbudget
    obtain ⟨pairs, final, hrun, hlength, hsubset, hfinal⟩ := ih _ hnext
    refine ⟨(first, last) :: pairs, final, ?_, ?_, ?_, ?_⟩
    · simp [UpperRepresentativeSupply.run, hselect, hrun]
    · simp [hlength]
    · exact (removed_subset_addParents parent (first, last) removed).trans hsubset
    · simp only [List.length_cons]
      omega

/-- Joint measurability also allows the parent map to depend on the actual
sampled grid. Its finite range is handled explicitly. -/
theorem table_run_measurable [Fintype Parent] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    [MeasurableSpace Parent] [MeasurableSingletonClass Parent]
    {X : Type*} [MeasurableSpace X] (parent : X → Cell → Parent)
    (hparent : ∀ c, Measurable (fun x => parent x c)) (cells : List Cell) (jobs : List (Row × Row))
    (values : X → Row → Cell → ℝ) (hvalues : ∀ r c, Measurable (fun x => values x r c))
    (removed : X → Finset Parent) (hremoved : Measurable removed) :
    Measurable (fun x => run (values x) (parent x) cells jobs (removed x)) := by
  have hfamily : Measurable (fun p : X × (Cell → Parent) => run (values p.1) p.2 cells jobs (removed p.1)) :=
    measurable_from_prod_countable_left (fun assign => UpperRepresentativeSupply.run_measurable assign cells jobs values hvalues removed hremoved)
  exact hfamily.comp (measurable_id.prodMk (measurable_pi_iff.mpr hparent))

variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]

/-- The actual recorded merged-grid table supplies every requested round;
no physical-component count enters this logical-cell parent budget. -/
theorem recorded_run_completes (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Agent × I) (jobs : List (Agent × Agent))
    (removed : Finset (Fin (count (Agent := Agent) q + 1)))
    (hbudget : ((removed.card + 2 * jobs.length : ℕ) : ℝ) * (1 / (q + 1 : ℝ)) < 1) :
    ∃ pairs final, run (UpperGridCache.table policy active origin q m draw)
      (UpperRecordedParents.parent policy active origin q m draw)
      (List.ofFn (fun i : Fin (count (Agent := Agent) q + m + 1) => i)) jobs removed = some (pairs, final) ∧
      pairs.length = jobs.length ∧ removed ⊆ final ∧ final.card ≤ removed.card + 2 * jobs.length := by
  let a : Agent := Classical.choice inferInstance
  apply table_run_completes (UpperGridCache.table policy active origin q m draw a) _ _
    (by positivity) _ (fun c => List.mem_ofFn.mpr ⟨c, rfl⟩)
    (UpperGridCache.table_normalized μ policy hpolicy active origin hgood hpositive q m draw a)
    (UpperRecordedParents.parent_cache_small μ policy hpolicy active origin hgood hpositive q m draw a)
    _ (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw) jobs removed hbudget

end EnvyFreeResearch.Full.UpperLogicalPreparation
