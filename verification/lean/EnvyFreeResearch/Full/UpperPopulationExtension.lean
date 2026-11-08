import EnvyFreeResearch.Full.UpperPopulationIndex
import EnvyFreeResearch.Full.UpperComponentGroups

/-! Actual active-label permutations and recorded piece families extend to
the original population while fixing frozen labels and adding empty pieces. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperZeroRows
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperCircularStage
variable {n : ℕ}

def extendPermutation (active : Finset (Fin n)) (f : Equiv.Perm (Fin active.card)) :
    Equiv.Perm (Fin n) := f.extendDomain (active.orderIsoOfFin rfl).toEquiv

theorem extendPermutation_apply (active : Finset (Fin n)) (f : Equiv.Perm (Fin active.card))
    (i : Fin active.card) : extendPermutation active f (enumerate active i) = enumerate active (f i) :=
  f.extendDomain_apply_image (active.orderIsoOfFin rfl).toEquiv i

theorem extendPermutation_fixed (active : Finset (Fin n)) (f : Equiv.Perm (Fin active.card))
    (j : Fin n) (hj : j ∉ active) : extendPermutation active f j = j :=
  f.extendDomain_apply_not_subtype (active.orderIsoOfFin rfl).toEquiv hj

def extendPieces (active : Finset (Fin n)) (pieces : Fin active.card → State n)
    (history : History n) (j : Fin n) : State n :=
  if hj : j ∈ active then pieces ((active.orderIsoOfFin rfl).symm ⟨j,hj⟩) else empty history

theorem extendPieces_apply (active : Finset (Fin n)) (pieces : Fin active.card → State n)
    (history : History n) (i : Fin active.card) :
    extendPieces active pieces history (enumerate active i) = pieces i := by
  rw [extendPieces,dif_pos (enumerate_mem active i)]
  exact congrArg pieces ((active.orderIsoOfFin rfl).symm_apply_apply i)

theorem extendPieces_frozen (active : Finset (Fin n)) (pieces : Fin active.card → State n)
    (history : History n) (j : Fin n) (hj : j ∉ active) :
    extendPieces active pieces history j = empty history := by simp [extendPieces,hj]

theorem enumerate_preimage (active : Finset (Fin n)) (j : Fin n) (hj : j ∈ active) :
    ∃ i, enumerate active i = j := by
  have h : j ∈ Set.range (enumerate active) := by rw [enumerate_range]; exact hj
  exact h

theorem extendPieces_domain (active : Finset (Fin n)) (pieces : Fin active.card → State n)
    (history : History n) :
    (⋃ j, domain (extendPieces active pieces history j).cells) = ⋃ i, domain (pieces i).cells := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    by_cases ha : j ∈ active
    · obtain ⟨i,rfl⟩ := enumerate_preimage active j ha
      rw [extendPieces_apply] at hj
      exact ⟨i,hj⟩
    · rw [extendPieces_frozen _ _ _ _ ha] at hj
      exact False.elim hj
  · rintro ⟨i,hi⟩
    exact ⟨enumerate active i,by rwa [extendPieces_apply]⟩

theorem extendPieces_pairwise (active : Finset (Fin n)) (pieces : Fin active.card → State n)
    (history : History n)
    (hpair : Pairwise (fun i j => Disjoint (domain (pieces i).cells) (domain (pieces j).cells))) :
    Pairwise (fun i j => Disjoint (domain (extendPieces active pieces history i).cells)
      (domain (extendPieces active pieces history j).cells)) := by
  intro i j hij
  by_cases hi : i ∈ active
  · by_cases hj : j ∈ active
    · obtain ⟨a,rfl⟩ := enumerate_preimage active i hi
      obtain ⟨b,rfl⟩ := enumerate_preimage active j hj
      rw [extendPieces_apply,extendPieces_apply]
      exact hpair (fun h => hij (congrArg (enumerate active) h))
    · rw [extendPieces_frozen _ _ _ _ hj]
      exact disjoint_empty _
  · rw [extendPieces_frozen _ _ _ _ hi]
    exact empty_disjoint _

theorem extendPieces_wellFormed (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Finset (Fin n))
    (pieces : Fin active.card → State n) (history : History n)
    (hh : UpperEndpointCache.Truthful μ history) (hgood : ∀ i, WellFormed μ (pieces i)) :
    ∀ j, WellFormed μ (extendPieces active pieces history j) := by
  intro j
  unfold extendPieces
  split_ifs
  · exact hgood _
  · exact empty_wellFormed μ history hh

theorem extendPieces_history (active : Finset (Fin n)) (pieces : Fin active.card → State n)
    (history : History n) (hh : ∀ i, (pieces i).history = history) (j : Fin n) :
    (extendPieces active pieces history j).history = history := by
  unfold extendPieces
  split_ifs
  · exact hh _
  · rfl

end EnvyFreeResearch.Full.UpperZeroRows
