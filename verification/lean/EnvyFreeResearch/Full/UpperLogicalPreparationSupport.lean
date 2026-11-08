import EnvyFreeResearch.Full.UpperLogicalPreparationState

/-!
# Exact support and count of retained logical cells

The cache retains the full fixed finite grid type. Unretained logical cells
are proved literally empty. The retained count is exactly a weighted sum of
independent coarse-parent labels, so physical component counts never enter.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval ENNReal

namespace EnvyFreeResearch.Full.UpperLogicalPreparation

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperGridCells
  UpperLogicalCells UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperCommonGrid Chores

variable {n m : ℕ}

theorem cell_restrict (R B : Set ℝ) (hsub : R ⊆ B) (cuts : Fin (m + 2) → ℝ) (e : Fin (m + 1)) :
    cell R cuts e = R ∩ cell B cuts e := by
  unfold cell
  split_ifs <;> ext x <;> simp only [mem_union, mem_inter_iff, mem_empty_iff_false]
  all_goals
    have hb : x ∈ R → x ∈ B := fun hx => hsub hx
    tauto

theorem cell_selectedUnion (B : Set ℝ) (cuts : Fin (m + 2) → ℝ) (hmono : Monotone cuts)
    (selected : Finset (Fin (m + 1))) (e : Fin (m + 1)) :
    cell (selectedUnion (cell B cuts) selected) cuts e = if e ∈ selected then cell B cuts e else ∅ := by
  have hsub : selectedUnion (cell B cuts) selected ⊆ B := by
    intro x hx
    obtain ⟨d, _, hd⟩ := (mem_selectedUnion _ _ x).mp hx
    exact cell_subset B cuts d hd
  rw [cell_restrict _ B hsub]
  by_cases he : e ∈ selected
  · simp only [he, ite_true]
    apply inter_eq_right.mpr
    intro x hx
    exact (mem_selectedUnion _ _ x).mpr ⟨e, he, hx⟩
  · simp only [he, ite_false]
    apply Set.Subset.antisymm ?_ (empty_subset _)
    intro x hx
    obtain ⟨d, hd, hxd⟩ := (mem_selectedUnion _ _ x).mp hx.1
    have hne : d ≠ e := fun h => he (h ▸ hd)
    exact Set.disjoint_left.mp (cells_disjoint B cuts hmono hne) hxd hx.2

theorem retained_cell (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (selected : Finset (Fin (m + 1))) (e : Fin (m + 1)) :
    cell (domain (retain state cuts selected).cells) cuts e =
      if e ∈ selected then cell (domain state.cells) cuts e else ∅ := by
  rw [retain_domain state cuts hzero hmono hsep selected]
  exact cell_selectedUnion _ cuts hmono selected e

variable {Fine Parent : Type*} [Fintype Fine] [Fintype Parent]

def parentCounts (parent : Fine → Parent) (p : Parent) : ℝ :=
  ∑ e, if parent e = p then 1 else 0

theorem parentCounts_nonnegative (parent : Fine → Parent) (p : Parent) : 0 ≤ parentCounts parent p := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

theorem parentCounts_sum (parent : Fine → Parent) :
    (∑ p, parentCounts parent p) = (Fintype.card Fine : ℝ) := by
  unfold parentCounts
  rw [Finset.sum_comm]
  simp

/-- The selected fine-cell count is the actual weighted Bernoulli sum over
coarse parents, including all zero-mass logical indices. -/
theorem reserveCells_card (parent : Fine → Parent) (theta : I) (labels : Parent → I) :
    ((reserveCells parent theta labels).card : ℝ) =
      UpperReserve.reserveValue (parentCounts parent) theta labels := by
  unfold UpperReserve.reserveValue parentCounts
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (e : Fine) :
      (∑ p : Parent, (if parent e = p then (1 : ℝ) else 0) * UpperReserve.mark theta (labels p)) =
        if labels (parent e) ≤ theta then 1 else 0 := by
    simp only [ite_mul, one_mul, zero_mul]
    simp [UpperReserve.mark, Set.indicator_apply]
  simp_rw [hterm]
  simp only [reserveCells, ← Finset.sum_boole]

/-- Derived from the fresh parent-label product law, not from a count-tail
assumption. The fixed full grid has `card Fine` logical indices. -/
theorem reserveCells_count_probability (parent : Fine → Parent) (theta : I) (cap : ℝ) (hcap : 0 < cap) :
    UpperReserve.labelLaw {labels | cap < ((reserveCells parent theta labels).card : ℝ)} ≤
      ENNReal.ofReal ((theta : ℝ) * Fintype.card Fine / cap) := by
  simp_rw [reserveCells_card]
  simpa only [parentCounts_sum] using
    UpperReserve.reserve_count_probability (parentCounts parent) theta cap hcap (parentCounts_nonnegative parent)

variable {Agent : Type*} [Fintype Agent]

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem reserveState_cell (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) (e : Fin (count (Agent := Agent) q + m + 1)) :
    cell (domain (reserveState policy active origin q m draw theta labels).cells)
      (UpperGridMerge.cuts policy active origin q m draw) e =
        if e ∈ reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels then
          UpperGridMerge.logicalCells policy active origin q m draw e else ∅ := by
  rw [reserveState, retained_cell _ _
    (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
    (grid_monotone _) (UpperGridCache.aligned_separated policy active origin q m draw),
    UpperGridCache.aligned_domain]
  split_ifs <;> rfl

theorem reserveState_cell_empty (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) (e : Fin (count (Agent := Agent) q + m + 1))
    (he : e ∉ reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels) :
    cell (domain (reserveState policy active origin q m draw theta labels).cells)
      (UpperGridMerge.cuts policy active origin q m draw) e = ∅ := by
  rw [reserveState_cell μ policy hpolicy active origin hgood hpositive q m draw theta labels e, ite_eq_right he]

/-- Every original observer's cache agrees exactly with the selected logical
cell mass, including zero outside the selected reserve index set. -/
theorem reserveState_cachedMass (q m : ℕ) (draw : Fin m → Agent × I) (theta : I)
    (labels : Fin (count (Agent := Agent) q + 1) → I) (i : Fin n)
    (e : Fin (count (Agent := Agent) q + m + 1)) :
    cachedMass (reserveState policy active origin q m draw theta labels)
      (UpperGridMerge.cuts policy active origin q m draw) i e =
        if e ∈ reserveCells (UpperRecordedParents.parent policy active origin q m draw) theta labels then
          (μ i).real (UpperGridMerge.logicalCells policy active origin q m draw e) else 0 := by
  rw [cachedMass_correct μ _ (reserveState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw theta labels)
    _ (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1
    (grid_monotone _) (reserveState_separated policy active origin q m draw theta labels),
    reserveState_cell μ policy hpolicy active origin hgood hpositive q m draw theta labels e]
  split_ifs <;> simp

end Correctness

end EnvyFreeResearch.Full.UpperLogicalPreparation
