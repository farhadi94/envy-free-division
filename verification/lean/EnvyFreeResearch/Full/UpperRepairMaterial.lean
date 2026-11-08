import EnvyFreeResearch.Full.UpperRepairAllocationPhysical
import EnvyFreeResearch.Full.UpperRepairRemainingPhysical

/-! Literal conservation of every point through the actual assignment,
seed grouping, corrected payments, and full-buffer remainder. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairMaterial

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs UpperCorrectionFinalCache
  UpperCorrectionStageProgram UpperPreparedEnvelopeMean UpperRepairAllocation UpperComponentAssembly

theorem packages_union {n r k : ℕ} (old : Fin k → State n) (pieces : Fin r → State n)
    (column : Fin r → Fin k) (history : History n) :
    (⋃ c, domain (UpperComponentAssembly.packages old pieces column history c).cells) =
      (⋃ c, domain (old c).cells) ∪ ⋃ j, domain (pieces j).cells := by
  simp_rw [UpperComponentAssembly.packages_domain]
  ext x
  constructor
  · intro hx
    obtain ⟨c, hx⟩ := mem_iUnion.mp hx
    rcases hx with hx | hx
    · exact Or.inl (mem_iUnion.mpr ⟨_, hx⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      split_ifs at hj with h
      · exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
      · exact hj.elim
  · rintro (hx | hx)
    · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨c, Or.inl hc⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨column j, Or.inr (mem_iUnion.mpr ⟨j, by simpa using hj⟩)⟩

theorem permuted_union {α β : Type} (e : Equiv.Perm α) (s : α → Set β) :
    (⋃ i, s (e i)) = ⋃ i, s i := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨e i, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨e.symm i, by simpa using hi⟩

theorem allocation_union {n k coarse fine : ℕ} [Nonempty (Fin k)]
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (stage : Result n k) :
    (⋃ j, domain (allocation hk chores active origin old data L theta labels pi threshold stage j).cells) =
      ((⋃ c, domain (old c).cells) ∪
        ⋃ j, domain (dataSeedState hk active origin data L theta labels pi threshold j).cells) ∪
      ⋃ j, domain (paymentState stage j).cells := by
  simp_rw [allocation, join_domain]
  rw [iUnion_union_distrib,
    permuted_union (assignment chores (dataMatrix hk active origin old data L theta labels pi threshold))
      (fun c => domain (UpperRepairPackages.packages hk active origin old data L theta labels pi threshold c).cells)]
  exact congrArg (fun s => s ∪ ⋃ j, domain (paymentState stage j).cells)
    (packages_union old _ _ _)

variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
  (hbudget : 2 * (jobCount k * L) < q + 1)
  (theta : I) (cap eta lam : ℝ) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (tape : Fin k → UpperCircular.Circle)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => UpperGridData.reserve d theta labels
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => dataTargets hk q chores active origin old d L theta labels pi threshold lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape
local notation "seedSet" => seedUnion (seedSystem hk policy active origin q m L draw theta labels pi)
  (seedCells hk policy active origin q m L draw theta labels pi) threshold
local notation "payments" => ⋃ j, domain (paymentState stage j).cells
local notation "X" => allocation hk chores active origin old d L theta labels pi threshold stage
local notation "B'" => UpperRepairRemaining.remaining hk active origin d L theta labels pi threshold stage.2.1

variable (hpass : UpperLogicalPreparationGuard.guard policy active origin q m (requests k L) theta cap draw labels = true)
  (selected : Finset (Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)))
  (hc : Checks μ active R cuts targets eta selected cap) (hrun : stage.2.2 = false)

include hpolicy hgood hpositive in
theorem actual_allocation_union :
    (⋃ j, domain (X j).cells) = ((⋃ c, domain (old c).cells) ∪ seedSet) ∪ payments := by
  rw [allocation_union]
  simp_rw [dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
  rfl

include hpolicy hgood hpositive hrun in
theorem spent_subset : seedSet ∪ payments ⊆ domain origin.cells := by
  apply union_subset
  · apply iUnion_subset
    intro j
    exact (Seeds.seed_subset _ _ _ _).trans (iUnion_subset fun a =>
      seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw theta labels pi j a)
  · apply iUnion_subset
    intro j
    exact (paymentState_subset policy active R cuts targets eta lam tape hrun j).trans
      (UpperLogicalPreparation.reserveState_subset μ policy hpolicy active origin hgood hpositive q m draw theta labels)

include hpolicy hgood hpositive hbudget hpass hc hrun in
theorem material_preserved :
    (⋃ j, domain (X j).cells) ∪ domain (B').cells = (⋃ c, domain (old c).cells) ∪ domain origin.cells := by
  rw [actual_allocation_union μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
    theta eta lam labels pi threshold tape,
    UpperRepairRemaining.remaining_domain μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
      hbudget theta cap eta lam labels pi threshold tape hpass selected hc hrun]
  have hs := spent_subset μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
    theta eta lam labels pi threshold tape hrun
  ext x
  simp only [mem_union, mem_iUnion, mem_sdiff]
  constructor
  · rintro ((h | h) | h)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (hs (Or.inl h))
    · exact Or.inr (hs (Or.inr (mem_iUnion.mpr h)))
    · exact Or.inr h.1
  · intro h
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · by_cases hx : x ∈ seedSet ∪ payments
      · rcases hx with hx | hx
        · exact Or.inl (Or.inl (Or.inr hx))
        · exact Or.inl (Or.inr (mem_iUnion.mp hx))
      · exact Or.inr ⟨h, by simpa only [mem_union, mem_iUnion] using hx⟩

include hpolicy hgood hpositive hbudget hpass hc hrun in
theorem residue_disjoint
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells)) (j : Fin k) :
    Disjoint (domain (X j).cells) (domain (B').cells) := by
  have hu := actual_allocation_union μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
    theta eta lam labels pi threshold tape
  rw [UpperRepairRemaining.remaining_domain μ policy hpolicy hk chores active origin hgood hpositive old q m L draw
    hbudget theta cap eta lam labels pi threshold tape hpass selected hc hrun]
  apply disjoint_left.mpr
  intro x hx hr
  have hx' : x ∈ ((⋃ c, domain (old c).cells) ∪ seedSet) ∪ payments := by
    rw [← hu]
    exact mem_iUnion.mpr ⟨j, hx⟩
  rcases hx' with (hx' | hx') | hx'
  · obtain ⟨c, hc'⟩ := mem_iUnion.mp hx'
    exact disjoint_left.mp (holdbuffer c) hc' hr.1
  · exact hr.2 (Or.inl hx')
  · exact hr.2 (Or.inr hx')

end EnvyFreeResearch.Full.UpperRepairMaterial
