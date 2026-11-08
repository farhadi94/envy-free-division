import EnvyFreeResearch.Full.UpperGridParents
import EnvyFreeResearch.Full.UpperGridCache

/-!
# Coarse parents and conserved cache mass for the actual sampled grid

The actual finite parent map preserves literal cells. Grouping the computed
fine-cell table by parent recovers the coarse-cell masses exactly, supplying
the small-parent budget used by representative selection and reserve labels.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperRecordedParents

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRecordedQuantiles UpperCommonGrid UpperGridParents UpperLogicalCells Chores

variable {n : ℕ} {Agent : Type*} [Fintype Agent]

def parent (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
    (draw : Fin m → Agent × I) : Fin (count (Agent := Agent) q + m + 1) → Fin (count (Agent := Agent) q + 1) :=
  UpperGridParents.parent (UpperRecordedQuantiles.cuts policy active origin q)
    (UpperGridMerge.cuts policy active origin q m draw)

/-- A finite partition refining another partition conserves the literal
parent sets, including every owned null endpoint. -/
theorem fiber_union_eq {Fine Parent : Type*} [DecidableEq Parent] (fine : Fine → Set ℝ) (coarse : Parent → Set ℝ)
    (assign : Fine → Parent) (hcover : (⋃ i, fine i) = ⋃ p, coarse p)
    (hdisjoint : Pairwise (fun p q => Disjoint (coarse p) (coarse q)))
    (hsub : ∀ i, fine i ⊆ coarse (assign i)) (p : Parent) :
    (⋃ i, if assign i = p then fine i else ∅) = coarse p := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hp : assign i = p
    · simpa only [hp] using hsub i (by simpa only [hp, ite_true] using hi)
    · simp only [hp, ite_false, mem_empty_iff_false] at hi
  · intro hx
    have hf : x ∈ ⋃ i, fine i := by rw [hcover]; exact mem_iUnion.mpr ⟨p, hx⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hf
    have hp : assign i = p := by
      by_contra hn
      exact Set.disjoint_left.mp (hdisjoint hn) (hsub i hi) hx
    exact mem_iUnion.mpr ⟨i, by simpa only [hp, ite_true] using hi⟩

theorem fiber_mass_sum {Fine Parent : Type*} [Fintype Fine] [DecidableEq Parent] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (fine : Fine → Set ℝ) (coarse : Parent → Set ℝ) (assign : Fine → Parent)
    (hfmeas : ∀ i, MeasurableSet (fine i))
    (hfdisjoint : Pairwise (fun i j => Disjoint (fine i) (fine j)))
    (hcover : (⋃ i, fine i) = ⋃ p, coarse p)
    (hcdisjoint : Pairwise (fun p q => Disjoint (coarse p) (coarse q)))
    (hsub : ∀ i, fine i ⊆ coarse (assign i)) (p : Parent) :
    (∑ i, if assign i = p then μ.real (fine i) else 0) = μ.real (coarse p) := by
  let fiber (i : Fine) : Set ℝ := if assign i = p then fine i else ∅
  have hsubf (i : Fine) : fiber i ⊆ fine i := by dsimp [fiber]; split_ifs <;> simp
  have hd : Pairwise (fun i j => Disjoint (fiber i) (fiber j)) :=
    fun i j hij => (hfdisjoint hij).mono (hsubf i) (hsubf j)
  have hm (i : Fine) : MeasurableSet (fiber i) := by
    dsimp [fiber]
    split_ifs
    · exact hfmeas i
    · exact MeasurableSet.empty
  calc
    _ = ∑ i, μ.real (fiber i) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [fiber]
      split_ifs <;> simp
    _ = μ.real (⋃ i, fiber i) := (measureReal_iUnion_fintype hd hm).symm
    _ = μ.real (coarse p) := congrArg μ.real (fiber_union_eq fine coarse assign hcover hcdisjoint hsub p)

section Correctness

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Agent → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))

include hpolicy hgood hpositive

theorem parent_fits (q m : ℕ) (draw : Fin m → Agent × I) (i : Fin (count (Agent := Agent) q + m + 1)) :
    Fits (UpperRecordedQuantiles.cuts policy active origin q) (UpperGridMerge.cuts policy active origin q m draw)
      i (parent policy active origin q m draw i) := by
  have hc := UpperRecordedQuantiles.cuts_endpoints μ policy hpolicy active origin hgood hpositive q
  have hf := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw
  exact UpperGridParents.parent_fits _ _ (grid_monotone _) (grid_monotone _) hc.1 hf.1 hc.2 hf.2
    (UpperGridInterior.coarse_zero_only μ policy hpolicy active origin hgood hpositive q)
    (UpperGridMerge.contains_coarse μ policy hpolicy active origin hgood hpositive q m draw) i

theorem cell_subset_parent (q m : ℕ) (draw : Fin m → Agent × I)
    (i : Fin (count (Agent := Agent) q + m + 1)) :
    UpperGridMerge.logicalCells policy active origin q m draw i ⊆
      UpperRecordedQuantiles.logicalCells policy active origin q (parent policy active origin q m draw i) :=
  UpperGridParents.cell_subset_parent _ _ _
    (UpperRecordedQuantiles.cuts_endpoints μ policy hpolicy active origin hgood hpositive q).1
    (UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive q m draw).1 i _
    (parent_fits μ policy hpolicy active origin hgood hpositive q m draw i)

theorem parent_union (q m : ℕ) (draw : Fin m → Agent × I) (p : Fin (count (Agent := Agent) q + 1)) :
    (⋃ i, if parent policy active origin q m draw i = p then
      UpperGridMerge.logicalCells policy active origin q m draw i else ∅) =
      UpperRecordedQuantiles.logicalCells policy active origin q p := by
  have hc := UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q
  have hf := UpperGridMerge.logical_partition μ policy hpolicy active origin hgood hpositive q m draw
  exact fiber_union_eq _ _ _ (hf.2.2.trans hc.2.2.symm) hc.1
    (cell_subset_parent μ policy hpolicy active origin hgood hpositive q m draw) p

/-- The actual normalized fine-cell cache conserves each coarse parent's
mass, so the number of physical components never enters the parent budget. -/
theorem parent_cache_mass (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent)
    (p : Fin (count (Agent := Agent) q + 1)) :
    (∑ i, if parent policy active origin q m draw i = p then
      UpperGridCache.table policy active origin q m draw a i else 0) =
      (μ (active a)).real (UpperRecordedQuantiles.logicalCells policy active origin q p) /
        (μ (active a)).real (domain origin.cells) := by
  have hc := UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q
  have hf := UpperGridMerge.logical_partition μ policy hpolicy active origin hgood hpositive q m draw
  have hm := fiber_mass_sum (μ (active a)) _ _ (parent policy active origin q m draw)
    hf.2.1 hf.1 (hf.2.2.trans hc.2.2.symm) hc.1
    (cell_subset_parent μ policy hpolicy active origin hgood hpositive q m draw) p
  calc
    _ = ∑ i, (if parent policy active origin q m draw i = p then
        (μ (active a)).real (UpperGridMerge.logicalCells policy active origin q m draw i) else 0) /
        (μ (active a)).real (domain origin.cells) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs
      · exact UpperGridCache.table_correct μ policy hpolicy active origin hgood hpositive q m draw a i
      · simp
    _ = _ := by rw [← Finset.sum_div, hm]

theorem parent_cache_small (q m : ℕ) (draw : Fin m → Agent × I) (a : Agent)
    (p : Fin (count (Agent := Agent) q + 1)) :
    (∑ i, if parent policy active origin q m draw i = p then
      UpperGridCache.table policy active origin q m draw a i else 0) ≤ 1 / (q + 1 : ℝ) := by
  rw [parent_cache_mass μ policy hpolicy active origin hgood hpositive]
  exact UpperRecordedQuantiles.logical_cells_small μ policy hpolicy active origin hgood hpositive q a p

end Correctness

section Measurability

variable [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem parent_measurable (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Agent → Fin n) (q m : ℕ) (i : Fin (count (Agent := Agent) q + m + 1)) :
    Measurable (fun p : State n × (Fin m → Agent × I) => parent policy active p.1 q m p.2 i) :=
  UpperGridParents.parent_measurable _ _
    (fun c => (measurable_pi_apply c).comp ((UpperRecordedQuantiles.cuts_measurable policy hpolicy active q).comp measurable_fst))
    (fun c => (measurable_pi_apply c).comp (UpperGridMerge.cuts_measurable policy hpolicy active q m)) i

end Measurability

end EnvyFreeResearch.Full.UpperRecordedParents
