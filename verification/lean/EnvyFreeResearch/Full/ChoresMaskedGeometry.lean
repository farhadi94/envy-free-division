import EnvyFreeResearch.Full.ChoresMaskedQuery
import EnvyFreeResearch.Full.ChoresPackageProposal

/-! Physical restriction identities for the masked compensation call.
Each participant observes its own label block of each pooled parent.
Discarding irrelevant blocks preserves own utility and exactly the
same-label comparisons used by the package payment argument. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Masked
open Set MeasureTheory PackageGeometry
open scoped Classical

variable {Agent Root Label : Type*}

def pooled (blocks : Root → Label → Set ℝ) (s : Root) : Set ℝ := ⋃ p, blocks s p

def retained (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (proposed : Agent → Set ℝ) (i : Agent) : Set ℝ :=
  proposed i ∩ blocks (assignedRoot i) (taskLabel i)

def maskedUtility (cost : Agent → Measure ℝ) (blocks : Root → Label → Set ℝ)
    (taskLabel : Agent → Label) (gap : Root → Agent → ℝ)
    (i : Agent) (s : Root) (D : Set ℝ) : ℝ :=
  max 0 (((cost i).restrict (blocks s (taskLabel i))).real D-gap s i)

theorem masked_utility_intersection (cost : Agent → Measure ℝ)
    (blocks : Root → Label → Set ℝ) (taskLabel : Agent → Label)
    (gap : Root → Agent → ℝ) (i : Agent) (s : Root) (D : Set ℝ) (hm : MeasurableSet D) :
    maskedUtility cost blocks taskLabel gap i s D =
      max 0 ((cost i).real (D ∩ blocks s (taskLabel i))-gap s i) := by
  rw [maskedUtility,measureReal_restrict_apply hm]

theorem physical_own_utility (cost : Agent → Measure ℝ)
    (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (proposed : Agent → Set ℝ) (gap : Root → Agent → ℝ)
    (i : Agent) (hm : MeasurableSet (proposed i)) :
    max 0 ((cost i).real (retained blocks assignedRoot taskLabel proposed i)-gap (assignedRoot i) i) =
      maskedUtility cost blocks taskLabel gap i (assignedRoot i) (proposed i) := by
  exact (masked_utility_intersection cost blocks taskLabel gap i (assignedRoot i) (proposed i) hm).symm

/-- Same-label comparison transfers to the actual retained donor piece.
No cross-label comparison is asserted or needed. -/
theorem physical_same_label_comparison (cost : Agent → Measure ℝ)
    (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (proposed : Agent → Set ℝ) (gap : Root → Agent → ℝ)
    (i j : Agent) (hi : MeasurableSet (proposed i)) (hj : MeasurableSet (proposed j))
    (hlabel : taskLabel j = taskLabel i)
    (hEF : maskedUtility cost blocks taskLabel gap i (assignedRoot j) (proposed j) ≤
      maskedUtility cost blocks taskLabel gap i (assignedRoot i) (proposed i)) :
    max 0 ((cost i).real (retained blocks assignedRoot taskLabel proposed j)-gap (assignedRoot j) i) ≤
      max 0 ((cost i).real (retained blocks assignedRoot taskLabel proposed i)-gap (assignedRoot i) i) := by
  rw [masked_utility_intersection cost blocks taskLabel gap i (assignedRoot j) (proposed j) hj,
    ← physical_own_utility cost blocks assignedRoot taskLabel proposed gap i hi] at hEF
  simpa only [retained,hlabel] using hEF

theorem physical_unused_threshold (cost : Agent → Measure ℝ)
    (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (proposed : Agent → Set ℝ) (gap : Root → Agent → ℝ)
    (i : Agent) (unused : Root) (hi : MeasurableSet (proposed i))
    (hm : MeasurableSet (pooled blocks unused))
    (hwhole : maskedUtility cost blocks taskLabel gap i unused (pooled blocks unused) ≤
      maskedUtility cost blocks taskLabel gap i (assignedRoot i) (proposed i)) :
    max 0 ((cost i).real (blocks unused (taskLabel i))-gap unused i) ≤
      max 0 ((cost i).real (retained blocks assignedRoot taskLabel proposed i)-gap (assignedRoot i) i) := by
  rw [masked_utility_intersection cost blocks taskLabel gap i unused (pooled blocks unused) hm,
    ← physical_own_utility cost blocks assignedRoot taskLabel proposed gap i hi] at hwhole
  have hsub : blocks unused (taskLabel i) ⊆ pooled blocks unused :=
    subset_iUnion (fun p => blocks unused p) (taskLabel i)
  simpa only [inter_eq_self_of_subset_right hsub] using hwhole

theorem retained_subset (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (proposed : Agent → Set ℝ) (i : Agent) :
    retained blocks assignedRoot taskLabel proposed i ⊆ blocks (assignedRoot i) (taskLabel i) :=
  inter_subset_right

theorem retained_measurable (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (proposed : Agent → Set ℝ) (i : Agent)
    (hb : MeasurableSet (blocks (assignedRoot i) (taskLabel i)))
    (hp : MeasurableSet (proposed i)) :
    MeasurableSet (retained blocks assignedRoot taskLabel proposed i) := hp.inter hb

theorem retained_disjoint (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (proposed : Agent → Set ℝ)
    (hinj : Function.Injective assignedRoot)
    (hdisj : ∀ s t, s ≠ t → ∀ p q, Disjoint (blocks s p) (blocks t q)) :
    Pairwise (fun i j => Disjoint (retained blocks assignedRoot taskLabel proposed i)
      (retained blocks assignedRoot taskLabel proposed j)) := by
  intro i j hij
  exact (hdisj (assignedRoot i) (assignedRoot j) (fun h => hij (hinj h))
    (taskLabel i) (taskLabel j)).mono
      (retained_subset blocks assignedRoot taskLabel proposed i)
      (retained_subset blocks assignedRoot taskLabel proposed j)

/-- A physical suffix in the pooled natural order restricts to a suffix
of its own block, even when the block has gaps or zero-cost components. -/
theorem retained_suffix (blocks : Root → Label → Set ℝ) (assignedRoot : Agent → Root)
    (taskLabel : Agent → Label) (endpoint : Agent → ℝ) (i : Agent) :
    retained blocks assignedRoot taskLabel
      (fun j => pooled blocks (assignedRoot j) ∩ Ioc (endpoint j) 1) i =
      blocks (assignedRoot i) (taskLabel i) ∩ Ioc (endpoint i) 1 := by
  ext x
  constructor
  · rintro ⟨⟨_,hx⟩,hb⟩
    exact ⟨hb,hx⟩
  · rintro ⟨hb,hx⟩
    exact ⟨⟨mem_iUnion.mpr ⟨taskLabel i,hb⟩,hx⟩,hb⟩

end EnvyFreeResearch.Full.Chores.Masked
