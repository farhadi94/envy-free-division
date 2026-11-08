import EnvyFreeResearch.Full.UpperSeedMatrix

/-! The cached seed matrix is the value table of literal disjoint unions of
witness cells and the old endowments. No physical-realization premise is
assumed for the matrix. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperPhysicalSeeds

open UpperRecordedDomain UpperSeeds UpperSeedMatrix

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent] {M L : ℕ}

def seed (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) : Set ℝ :=
  physicalSeed (cells job) (difference S job) (draw job)

def package (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (old : Agent → Set ℝ) (draw : Fin (M + 1) → Fin (L + 1)) (column : Agent) : Set ℝ :=
  old column ∪ ⋃ job, if S.column job = column then seed S cells draw job else ∅

def DisjointCells (cells : Fin (M + 1) → Fin L → Component) : Prop :=
  Pairwise (fun p q : Fin (M + 1) × Fin L => Disjoint (cells p.1 p.2).carrier (cells q.1 q.2).carrier)

omit [Fintype Agent] [DecidableEq Agent] in
theorem seed_measurable (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) :
    MeasurableSet (seed S cells draw job) := physicalSeed_measurable _ _ _

omit [Fintype Agent] in
theorem package_measurable (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (old : Agent → Set ℝ) (hold : ∀ j, MeasurableSet (old j))
    (draw : Fin (M + 1) → Fin (L + 1)) (column : Agent) :
    MeasurableSet (package S cells old draw column) := by
  apply (hold column).union
  apply MeasurableSet.iUnion
  intro job
  split_ifs
  · exact seed_measurable S cells draw job
  · exact MeasurableSet.empty

omit [Fintype Agent] [DecidableEq Agent] in
theorem seed_subset (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) :
    seed S cells draw job ⊆ ⋃ a, (cells job a).carrier := physicalSeed_subset _ _ _

omit [Fintype Agent] [DecidableEq Agent] in
theorem seed_disjoint (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
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
theorem old_seed_disjoint (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (old : Agent → Set ℝ)
    (hold : ∀ column job a, Disjoint (old column) (cells job a).carrier)
    (draw : Fin (M + 1) → Fin (L + 1)) (column : Agent) (job : Fin (M + 1)) :
    Disjoint (old column) (seed S cells draw job) :=
  (disjoint_iUnion_right.mpr (hold column job)).mono_right (seed_subset S cells draw job)

omit [Fintype Agent] in
theorem mem_package_cases (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
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
theorem packages_disjoint (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (hdisjoint : DisjointCells cells) (old : Agent → Set ℝ)
    (hold : Pairwise (fun i j => Disjoint (old i) (old j)))
    (holdcells : ∀ column job a, Disjoint (old column) (cells job a).carrier)
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
    (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (hdisjoint : DisjointCells cells)
    (hcache : ∀ job a row, S.weight job a row = (cost row).real (cells job a).carrier)
    (draw : Fin (M + 1) → Fin (L + 1)) (job : Fin (M + 1)) (row : Agent) :
    (cost row).real (seed S cells draw job) = rowSeed S job row (draw job) := by
  rw [seed, physicalSeed_mass]
  · simp only [rowSeed, hcache]
  · intro a b hab
    exact hdisjoint (i := (job, a)) (j := (job, b)) (by
      intro h
      exact hab (congrArg Prod.snd h))

/-- The assignment matrix is exactly the actual observers' value table for
the literal packages, including all zero thresholds and zero witness values. -/
theorem package_mass (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (S : SeedSystem Agent M L) (cells : Fin (M + 1) → Fin L → Component)
    (hdisjoint : DisjointCells cells) (old : Agent → Set ℝ)
    (hold : ∀ column job a, Disjoint (old column) (cells job a).carrier)
    (hcache : ∀ job a row, S.weight job a row = (cost row).real (cells job a).carrier)
    (draw : Fin (M + 1) → Fin (L + 1)) (row column : Agent) :
    (cost row).real (package S cells old draw column) =
      matrix S (fun i j => (cost i).real (old j)) draw row column := by
  have hpieces : Pairwise (fun job other => Disjoint
      (if S.column job = column then seed S cells draw job else ∅)
      (if S.column other = column then seed S cells draw other else ∅)) := by
    intro job other hne
    split_ifs <;> simp [seed_disjoint S cells hdisjoint draw hne]
  have hmeas (job : Fin (M + 1)) : MeasurableSet
      (if S.column job = column then seed S cells draw job else ∅) := by
    split_ifs
    · exact seed_measurable S cells draw job
    · exact MeasurableSet.empty
  have hdis : Disjoint (old column)
      (⋃ job, if S.column job = column then seed S cells draw job else ∅) := by
    apply disjoint_iUnion_right.mpr
    intro job
    split_ifs
    · exact old_seed_disjoint S cells old hold draw column job
    · exact disjoint_bot_right
  rw [package, measureReal_union hdis (MeasurableSet.iUnion hmeas),
    measureReal_iUnion_fintype hpieces hmeas]
  change _ = (cost row).real (old column) + ∑ job, contribution S draw row column job
  congr 1
  apply Finset.sum_congr rfl
  intro job _
  unfold contribution
  split_ifs
  · exact seed_mass cost S cells hdisjoint hcache draw job row
  · simp

end EnvyFreeResearch.Full.UpperPhysicalSeeds
