import EnvyFreeResearch.Full.UpperLogicalIsolationData
import EnvyFreeResearch.Full.UpperLogicalIsolationCore

/-! Actual logical witness cells, permuted seed unions, and original-unit spending. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperLogicalIsolation
open UpperLogicalPreparation UpperLogicalPreparationGuard UpperRecordedDomain UpperCorrectionExecution
  UpperCircularStage UpperStageMeasurable UpperRecordedQuantiles UpperWitnessExtraction UpperRepairJobs
  UpperRepresentativeSupply UpperSeedMatrix UpperBatchPermutation Chores
variable {n k L : ℕ}

def witnesses (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I) : Job k → Fin L → Set ℝ :=
  fun j a => UpperGridMerge.logicalCells policy active origin q m draw
    (chosenCell policy active origin q m L draw theta labels j a)

def seedSystem (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I)
    (pi : Equiv.Perm (Fin k)) : SeedSystem (Fin k) (jobCount k - 1) L :=
  system hk (permutedWeights (weights policy active origin q m L draw theta labels) pi)

def seedCells (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I)
    (pi : Equiv.Perm (Fin k)) : Fin (jobCount k - 1 + 1) → Fin L → Set ℝ :=
  permutedCells hk (witnesses policy active origin q m L draw theta labels) pi

def cachedMatrix (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I) (theta : I) (labels : Parent k q → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) : Fin k → Fin k → ℝ :=
  UpperSeedMatrix.matrix (seedSystem hk policy active origin q m L draw theta labels pi)
    (oldMatrix active old (reserveState policy active origin q m draw theta labels)) threshold

section Correctness
variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ a, 0 < (μ (active a)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem witnesses_disjoint (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1) (theta : I) (labels : Parent k q → I) :
    Pairwise (fun p r : Job k × Fin L =>
      Disjoint (witnesses policy active origin q m L draw theta labels p.1 p.2)
        (witnesses policy active origin q m L draw theta labels r.1 r.2)) := by
  obtain ⟨final, hexec, hlength, _⟩ := representativePairs_spec μ policy hpolicy active origin hgood hpositive q m L draw hbudget
  exact picked_cells_disjoint _ (UpperGridCache.table_nonneg μ policy hpolicy active origin hgood hpositive q m draw)
    _ _ _ _ _ (UpperRecordedParents.cell_subset_parent μ policy hpolicy active origin hgood hpositive q m draw)
    (UpperRecordedQuantiles.logical_partition μ policy hpolicy active origin hgood hpositive q).1
    UpperPreparedIsolation.rows ∅ _ final hexec hlength 0

theorem witnesses_reserve_disjoint (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1) (theta : I) (cap : ℝ) (labels : Parent k q → I)
    (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true) (j : Job k) (a : Fin L) :
    Disjoint (witnesses policy active origin q m L draw theta labels j a)
      (domain (reserveState policy active origin q m draw theta labels).cells) := by
  obtain ⟨final, hexec, hlength, _⟩ := representativePairs_spec μ policy hpolicy active origin hgood hpositive q m L draw hbudget
  exact passing_witness_disjoint μ policy hpolicy active origin hgood hpositive q m draw UpperPreparedIsolation.rows
    _ theta cap labels hpass _ final hexec hlength (j, a)

theorem seedCells_disjoint (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1) (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k)) :
    Seeds.DisjointCells (seedCells hk policy active origin q m L draw theta labels pi) :=
  permutedCells_disjoint hk _ (witnesses_disjoint μ policy hpolicy active origin hgood hpositive q m L draw hbudget theta labels) pi

theorem seedCells_measurable (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k)) (j : Fin (jobCount k - 1 + 1)) (a : Fin L) :
    MeasurableSet (seedCells hk policy active origin q m L draw theta labels pi j a) :=
  (UpperGridMerge.logical_partition μ policy hpolicy active origin hgood hpositive q m draw).2.1 _

theorem seedCells_subset (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k)) (j : Fin (jobCount k - 1 + 1)) (a : Fin L) :
    seedCells hk policy active origin q m L draw theta labels pi j a ⊆ domain origin.cells :=
  UpperLogicalCells.cell_subset _ _ _

/-- The exact total seed budget is in original-buffer units, uniformly in
labels, permutation, thresholds, and later rejection decisions. -/
theorem seeds_raw_spending (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (i : Fin k) :
    (μ (active i)).real (seedUnion (seedSystem hk policy active origin q m L draw theta labels pi)
      (seedCells hk policy active origin q m L draw theta labels pi) threshold) ≤
      ((jobCount k : ℝ) * L / (q + 1 : ℝ)) * (μ (active i)).real (domain origin.cells) := by
  have hcap : ∀ j a, (μ (active i)).real (seedCells hk policy active origin q m L draw theta labels pi j a) ≤
      (1 / (q + 1 : ℝ)) * (μ (active i)).real (domain origin.cells) := by
    intro j a
    exact (div_le_iff₀ (hpositive i)).mp
      (UpperGridMerge.logical_cells_small μ policy hpolicy active origin hgood hpositive q m draw i _)
  have h := seedUnion_mass_le (μ (active i)) (seedSystem hk policy active origin q m L draw theta labels pi)
    (seedCells hk policy active origin q m L draw theta labels pi) _ hcap threshold
  have hc : jobCount k - 1 + 1 = jobCount k := by have := jobCount_positive hk; omega
  rw [hc] at h
  convert h using 1; ring

theorem seeds_avoid_reserve (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1) (theta : I) (cap : ℝ) (labels : Parent k q → I)
    (hpass : guard policy active origin q m (requests k L) theta cap draw labels = true)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    Disjoint (seedUnion (seedSystem hk policy active origin q m L draw theta labels pi)
      (seedCells hk policy active origin q m L draw theta labels pi) threshold)
      (domain (reserveState policy active origin q m draw theta labels).cells) :=
  seedUnion_disjoint _ _ _ (fun _j a =>
    witnesses_reserve_disjoint μ policy hpolicy active origin hgood hpositive q m L draw hbudget theta cap labels hpass _ a) threshold

/-- The cached weight is the real mass for the actually normalized observer
measure; the construction contains no valuation query. -/
theorem seedSystem_physical (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (j : Fin (jobCount k - 1 + 1)) (a : Fin L) (i : Fin k) :
    (seedSystem hk policy active origin q m L draw theta labels pi).weight j a i =
      (ENNReal.ofReal (1 / (μ (active i)).real (domain (reserveState policy active origin q m draw theta labels).cells)) •
        μ (active i)).real (seedCells hk policy active origin q m L draw theta labels pi j a) := by
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (by positivity)]
  change weights policy active origin q m L draw theta labels _ a i = _
  rw [weights_physical μ policy hpolicy active origin hgood hpositive]
  change _ = 1 / _ * (μ (active i)).real (UpperGridMerge.logicalCells policy active origin q m draw _)
  simp only [permuteJob]
  ring

/-- Literal old endowments and freshly selected logical seeds give exactly
the matrix supplied to assignment optimization. -/
theorem packages_physical (hk : 2 ≤ k) (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (i c : Fin k) :
    (μ (active i)).real (Seeds.package (seedSystem hk policy active origin q m L draw theta labels pi)
      (seedCells hk policy active origin q m L draw theta labels pi) (fun c => domain (old c).cells) threshold c) /
      (μ (active i)).real (domain (reserveState policy active origin q m draw theta labels).cells) =
      cachedMatrix hk policy active origin old q m L draw theta labels pi threshold i c := by
  have h := normalized_package_mass (fun i => μ (active i))
    (fun i => (μ (active i)).real (domain (reserveState policy active origin q m draw theta labels).cells))
    (fun _ => measureReal_nonneg) (seedSystem hk policy active origin q m L draw theta labels pi)
    (seedCells hk policy active origin q m L draw theta labels pi)
    (seedCells_measurable μ policy hpolicy active origin hgood hpositive hk q m L draw theta labels pi)
    (seedCells_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget theta labels pi)
    (fun c => domain (old c).cells)
    (fun c j a => (holdbuffer c).mono_right
      (seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw theta labels pi j a))
    (fun j a r => weights_physical μ policy hpolicy active origin hgood hpositive q m L draw theta labels _ a r)
    threshold i c
  have holdEq := funext (fun r => funext (fun d => oldMatrix_physical μ policy hpolicy active origin hgood hpositive
    old hold q m draw theta labels r d))
  exact h.trans (congrArg (fun oldTable => UpperSeedMatrix.matrix
    (seedSystem hk policy active origin q m L draw theta labels pi) oldTable threshold i c) holdEq.symm)

theorem packages_disjoint (hk : 2 ≤ k) (old : Fin k → State n)
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    Pairwise (fun i j => Disjoint
      (Seeds.package (seedSystem hk policy active origin q m L draw theta labels pi)
        (seedCells hk policy active origin q m L draw theta labels pi) (fun c => domain (old c).cells) threshold i)
      (Seeds.package (seedSystem hk policy active origin q m L draw theta labels pi)
        (seedCells hk policy active origin q m L draw theta labels pi) (fun c => domain (old c).cells) threshold j)) :=
  Seeds.packages_disjoint _ _
    (seedCells_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget theta labels pi)
    _ holdpair (fun c j a => (holdbuffer c).mono_right
      (seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw theta labels pi j a)) threshold

end Correctness
end EnvyFreeResearch.Full.UpperLogicalIsolation
