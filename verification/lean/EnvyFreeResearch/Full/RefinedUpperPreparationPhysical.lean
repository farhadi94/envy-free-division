import EnvyFreeResearch.Full.RefinedUpperPreparationWeights
import EnvyFreeResearch.Full.UpperLogicalIsolationCore

/-! The newly selected witnesses and threshold seeds are actual disjoint
pieces outside the retained buffer, with an explicit original-unit budget. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRepairJobs UpperRecordedQuantiles UpperLogicalIsolation
  UpperSeedMatrix UpperBatchPermutation Chores
open scoped Classical unitInterval BigOperators
variable {n k : ℕ}

def witnesses (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) : Job k → Fin L → Set ℝ :=
  fun j a => UpperGridMerge.logicalCells policy active origin q m draw
    (dataChosen active origin (UpperGridMerge.prepare policy active origin q m draw) L j a)

def seedSystem (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (pi : Equiv.Perm (Fin k)) :
    SeedSystem (Fin k) (jobCount k-1) L :=
  system hk (permutedWeights (dataWeights active origin (UpperGridMerge.prepare policy active origin q m draw) L) pi)

def seedCells (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (pi : Equiv.Perm (Fin k)) :
    Fin (jobCount k-1+1) → Fin L → Set ℝ :=
  permutedCells hk (witnesses policy active origin q m L draw) pi

section Correctness
variable [Nonempty (Fin k)]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem witnesses_disjoint (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2*(jobCount k*L) < q+1) :
    Pairwise (fun p r : Job k × Fin L => Disjoint
      (witnesses policy active origin q m L draw p.1 p.2)
      (witnesses policy active origin q m L draw r.1 r.2)) := by
  have hs := dataResult_spec μ policy hpolicy active origin hgood hpositive q m L draw hbudget
  exact picked_cells_disjoint _
    (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw)
    _ _ _ _ _ (UpperRecordedParents.cell_subset_parent μ policy hpolicy active origin hgood hpositive q m draw)
    (UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q).1
    UpperPreparedIsolation.rows ∅ _ _ hs.1 hs.2.1 0

theorem witnesses_retained_disjoint (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2*(jobCount k*L) < q+1) (j : Job k) (a : Fin L) :
    Disjoint (witnesses policy active origin q m L draw j a)
      (domain (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L).cells) := by
  have hs := dataResult_spec μ policy hpolicy active origin hgood hpositive q m L draw hbudget
  let data := UpperGridMerge.prepare policy active origin q m draw
  let final := (dataResult active origin data L).2
  have hp : UpperRecordedParents.parent policy active origin q m draw (dataChosen active origin data L j a) ∈ final :=
    picked_parent_mem_final _ (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw)
      _ _ _ UpperPreparedIsolation.rows ∅ _ final hs.1 hs.2.1 0 (j,a)
  rw [dataRetained_execute,retainedState_domain μ policy hpolicy active origin hgood hpositive]
  apply Set.disjoint_iUnion_right.mpr
  intro p
  change Disjoint _ (if p ∉ final then UpperRecordedQuantiles.logicalCells policy active origin q p else ∅)
  by_cases hpr : p ∈ final
  · simp only [hpr,not_true_eq_false,ite_false,disjoint_empty]
  · rw [if_pos hpr]
    have hne : UpperRecordedParents.parent policy active origin q m draw (dataChosen active origin data L j a) ≠ p :=
      fun he => hpr (he ▸ hp)
    exact ((UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q).1 hne).mono_left
      (UpperRecordedParents.cell_subset_parent μ policy hpolicy active origin hgood hpositive q m draw _)

theorem seedCells_disjoint (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2*(jobCount k*L) < q+1) (pi : Equiv.Perm (Fin k)) :
    Seeds.DisjointCells (seedCells hk policy active origin q m L draw pi) :=
  permutedCells_disjoint hk _ (witnesses_disjoint μ policy hpolicy active origin hgood hpositive q m L draw hbudget) pi

theorem seedCells_measurable (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (j : Fin (jobCount k-1+1)) (a : Fin L) :
    MeasurableSet (seedCells hk policy active origin q m L draw pi j a) :=
  (UpperGridMerge.logical_partition μ policy hpolicy active origin hgood hpositive q m draw).2.1 _

theorem seedCells_subset (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (j : Fin (jobCount k-1+1)) (a : Fin L) :
    seedCells hk policy active origin q m L draw pi j a ⊆ domain origin.cells :=
  UpperLogicalCells.cell_subset _ _ _

theorem seeds_raw_spending (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (i : Fin k) :
    (μ (active i)).real (seedUnion (seedSystem hk policy active origin q m L draw pi)
      (seedCells hk policy active origin q m L draw pi) threshold) ≤
      ((jobCount k : ℝ)*L/(q+1 : ℝ)) * (μ (active i)).real (domain origin.cells) := by
  have hcap : ∀ j a, (μ (active i)).real (seedCells hk policy active origin q m L draw pi j a) ≤
      (1/(q+1 : ℝ)) * (μ (active i)).real (domain origin.cells) := by
    intro j a
    exact (div_le_iff₀ (hpositive i)).mp
      (UpperGridMerge.logical_cells_small μ policy hpolicy active origin hgood hpositive q m draw i _)
  have h := seedUnion_mass_le (μ (active i)) (seedSystem hk policy active origin q m L draw pi)
    (seedCells hk policy active origin q m L draw pi) _ hcap threshold
  have hc : jobCount k-1+1 = jobCount k := by have := jobCount_positive hk; omega
  rw [hc] at h
  convert h using 1; ring

end Correctness
end EnvyFreeResearch.Full.RefinedUpperPreparation
