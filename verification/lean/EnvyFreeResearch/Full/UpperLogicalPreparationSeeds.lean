import EnvyFreeResearch.Full.UpperSeedMatrix
import EnvyFreeResearch.Full.UpperLogicalPreparationWitness

/-!
# Literal seed unions on logical finite-union cells

Threshold selection and assignment matrices are realized by the actual
logical cell sets. No contiguous-component representation is required.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperLogicalPreparation.Seeds

open UpperSeeds UpperSeedMatrix

variable {L : ℕ}

def physicalSeed (cells : Fin L → Set ℝ) (gamma : Fin L → ℝ)
    (threshold : Fin (L + 1)) : Set ℝ :=
  ⋃ a, if kept gamma threshold a then cells a else ∅

theorem physicalSeed_subset (cells : Fin L → Set ℝ) (gamma : Fin L → ℝ)
    (threshold : Fin (L + 1)) : physicalSeed cells gamma threshold ⊆ ⋃ a, cells a := by
  intro x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨a, ?_⟩
  by_cases h : kept gamma threshold a
  · simpa only [h, ite_true] using ha
  · simp only [h, ite_false, mem_empty_iff_false] at ha

theorem physicalSeed_measurable (cells : Fin L → Set ℝ) (hmeas : ∀ a, MeasurableSet (cells a)) (gamma : Fin L → ℝ)
    (threshold : Fin (L + 1)) : MeasurableSet (physicalSeed cells gamma threshold) := by
  apply MeasurableSet.iUnion
  intro a
  by_cases h : kept gamma threshold a
  · simpa only [h, ite_true] using hmeas a
  · simp only [h, ite_false]
    exact MeasurableSet.empty

theorem physicalSeed_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (cells : Fin L → Set ℝ) (hmeas : ∀ a, MeasurableSet (cells a)) (gamma : Fin L → ℝ) (threshold : Fin (L + 1))
    (hdisjoint : Pairwise (fun a b => Disjoint (cells a) (cells b))) :
    μ.real (physicalSeed cells gamma threshold) =
      ∑ a, if kept gamma threshold a then μ.real (cells a) else 0 := by
  unfold physicalSeed
  rw [measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · intro a b hab
    dsimp only [Function.onFun]
    split_ifs <;> simp [hdisjoint hab]
  · intro a
    split_ifs
    · exact hmeas a
    · exact MeasurableSet.empty

/-- The literal union has exactly the seed score used in isolation, for the
actual two normalized observer measures. No physical realization is assumed. -/
theorem physicalSeed_signed_value (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (cells : Fin L → Set ℝ) (hmeas : ∀ a, MeasurableSet (cells a)) (u v : ℝ) (threshold : Fin (L + 1))
    (hdisjoint : Pairwise (fun a b => Disjoint (cells a) (cells b))) :
    let gamma := fun a => u * μ.real (cells a) - v * ν.real (cells a)
    u * μ.real (physicalSeed cells gamma threshold) -
      v * ν.real (physicalSeed cells gamma threshold) = value gamma threshold := by
  dsimp only
  rw [physicalSeed_mass μ _ hmeas _ _ hdisjoint, physicalSeed_mass ν _ hmeas _ _ hdisjoint]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, value]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent] {M L : ℕ}

def seed (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) : Set ℝ :=
  physicalSeed (cells job) (difference S job) (draw job)

def package (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (old : Agent → Set ℝ) (draw : Fin (M + 1) → Fin (L + 1)) (column : Agent) : Set ℝ :=
  old column ∪ ⋃ job, if S.column job = column then seed S cells draw job else ∅

def DisjointCells (cells : Fin (M + 1) → Fin L → Set ℝ) : Prop :=
  Pairwise (fun p q : Fin (M + 1) × Fin L => Disjoint (cells p.1 p.2) (cells q.1 q.2))

omit [Fintype Agent] [DecidableEq Agent] in
theorem seed_measurable (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (hmeas : ∀ job a, MeasurableSet (cells job a))
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) :
    MeasurableSet (seed S cells draw job) := physicalSeed_measurable _ (hmeas job) _ _

omit [Fintype Agent] in
theorem package_measurable (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (hmeas : ∀ job a, MeasurableSet (cells job a))
    (old : Agent → Set ℝ) (hold : ∀ j, MeasurableSet (old j))
    (draw : Fin (M + 1) → Fin (L + 1)) (column : Agent) :
    MeasurableSet (package S cells old draw column) := by
  apply (hold column).union
  apply MeasurableSet.iUnion
  intro job
  split_ifs
  · exact seed_measurable S cells hmeas draw job
  · exact MeasurableSet.empty

omit [Fintype Agent] [DecidableEq Agent] in
theorem seed_subset (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) :
    seed S cells draw job ⊆ ⋃ a, (cells job a) := physicalSeed_subset _ _ _

omit [Fintype Agent] [DecidableEq Agent] in
theorem seed_disjoint (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (hdisjoint : DisjointCells cells) (draw : Fin (M + 1) → Fin (L + 1)) :
    Pairwise (fun job other => Disjoint (seed S cells draw job) (seed S cells draw other)) := by
  intro job other hne
  apply Disjoint.mono (seed_subset S cells draw job) (seed_subset S cells draw other)
  apply disjoint_iUnion_left.mpr
  intro a
  apply disjoint_iUnion_right.mpr
  intro b
  exact hdisjoint (i := (job, a)) (j := (other, b)) (by
    intro h
    exact hne (congrArg Prod.fst h))

omit [Fintype Agent] [DecidableEq Agent] in
theorem old_seed_disjoint (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (old : Agent → Set ℝ)
    (hold : ∀ column job a, Disjoint (old column) (cells job a))
    (draw : Fin (M + 1) → Fin (L + 1)) (column : Agent) (job : Fin (M + 1)) :
    Disjoint (old column) (seed S cells draw job) :=
  (disjoint_iUnion_right.mpr (hold column job)).mono_right (seed_subset S cells draw job)

omit [Fintype Agent] in
theorem mem_package_cases (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (old : Agent → Set ℝ) (draw : Fin (M + 1) → Fin (L + 1)) (column : Agent) (x : ℝ) :
    x ∈ package S cells old draw column ↔
      x ∈ old column ∨ ∃ job, S.column job = column ∧ x ∈ seed S cells draw job := by
  simp only [package, mem_union, mem_iUnion]
  refine or_congr Iff.rfl ?_
  apply exists_congr
  intro job
  split_ifs <;> simp_all

/-- Distinct witness parents give disjoint physical seed unions even after
all jobs belonging to a column have been combined with its old endowment. -/
theorem packages_disjoint (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (hdisjoint : DisjointCells cells) (old : Agent → Set ℝ)
    (hold : Pairwise (fun i j => Disjoint (old i) (old j)))
    (holdcells : ∀ column job a, Disjoint (old column) (cells job a))
    (draw : Fin (M + 1) → Fin (L + 1)) :
    Pairwise (fun i j => Disjoint (package S cells old draw i) (package S cells old draw j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rw [mem_package_cases] at hxi hxj
  rcases hxi with hxi | ⟨job, hjob, hxi⟩
  · rcases hxj with hxj | ⟨other, _, hxj⟩
    · exact Set.disjoint_left.mp (hold hij) hxi hxj
    · exact Set.disjoint_left.mp (old_seed_disjoint S cells old holdcells draw i other) hxi hxj
  · rcases hxj with hxj | ⟨other, hother, hxj⟩
    · exact Set.disjoint_left.mp (old_seed_disjoint S cells old holdcells draw j job) hxj hxi
    · have hne : job ≠ other := by
        intro heq
        exact hij ((hjob.symm.trans (congrArg S.column heq)).trans hother)
      exact Set.disjoint_left.mp (seed_disjoint S cells hdisjoint draw hne) hxi hxj

omit [Fintype Agent] [DecidableEq Agent] in
theorem seed_mass (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (hmeas : ∀ job a, MeasurableSet (cells job a))
    (hdisjoint : DisjointCells cells)
    (hcache : ∀ job a row, S.weight job a row = (cost row).real (cells job a))
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) (row : Agent) :
    (cost row).real (seed S cells draw job) = rowSeed S job row (draw job) := by
  rw [seed, physicalSeed_mass _ _ (hmeas job)]
  · simp only [rowSeed, hcache]
  · intro a b hab
    exact hdisjoint (i := (job, a)) (j := (job, b)) (by
      intro h
      exact hab (congrArg Prod.snd h))

/-- The assignment matrix is exactly the actual observers' value table for
the literal packages, including all zero thresholds and zero witness values. -/
theorem package_mass (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Set ℝ)
    (hmeas : ∀ job a, MeasurableSet (cells job a))
    (hdisjoint : DisjointCells cells) (old : Agent → Set ℝ)
    (hold : ∀ column job a, Disjoint (old column) (cells job a))
    (hcache : ∀ job a row, S.weight job a row = (cost row).real (cells job a))
    (draw : Fin (M + 1) → Fin (L + 1)) (row column : Agent) :
    (cost row).real (package S cells old draw column) =
      matrix S (fun i j => (cost i).real (old j)) draw row column := by
  have hpieces : Pairwise (fun job other => Disjoint
      (if S.column job = column then seed S cells draw job else ∅)
      (if S.column other = column then seed S cells draw other else ∅)) := by
    intro job other hne
    split_ifs <;> simp [seed_disjoint S cells hdisjoint draw hne]
  have hpieceMeas (job : Fin (M + 1)) : MeasurableSet
      (if S.column job = column then seed S cells draw job else ∅) := by
    split_ifs
    · exact seed_measurable S cells hmeas draw job
    · exact MeasurableSet.empty
  have hdis : Disjoint (old column)
      (⋃ job, if S.column job = column then seed S cells draw job else ∅) := by
    apply disjoint_iUnion_right.mpr
    intro job
    split_ifs
    · exact old_seed_disjoint S cells old hold draw column job
    · exact disjoint_bot_right
  rw [package, measureReal_union hdis (MeasurableSet.iUnion hpieceMeas),
    measureReal_iUnion_fintype hpieces hpieceMeas]
  change _ = (cost row).real (old column) + ∑ job, contribution S draw row column job
  congr 1
  apply Finset.sum_congr rfl
  intro job _
  unfold contribution
  split_ifs
  · exact seed_mass cost S cells hmeas hdisjoint hcache draw job row
  · simp


end EnvyFreeResearch.Full.UpperLogicalPreparation.Seeds
