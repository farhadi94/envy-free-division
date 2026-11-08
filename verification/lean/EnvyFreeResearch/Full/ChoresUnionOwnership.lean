import EnvyFreeResearch.Full.ChoresUnionCoreParts

/-! Literal ownership of the isolated left endpoint. Recorded component
lists represent (0,1]; assigning 0 to the cutter changes no atomless value
and yields exact coverage of [0,1] together with the returned residue. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram
open scoped Classical

variable {n : ℕ}

def ownedAllocation (U : Set ℝ) (c : Fin n) (out : IntervalCore.Outcome n) (i : Fin n) : Set ℝ :=
  domainAllocation U c out i ∪ if i = c then {0} else ∅

theorem owned_allocation_value (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (hzero : 0 ∉ U) (c : Fin n) (out : IntervalCore.Outcome n) (i j : Fin n) :
    (cost i).real (ownedAllocation U c out j) = (cost i).real (domainAllocation U c out j) := by
  by_cases hj : j = c
  · have hd : Disjoint (domainAllocation U c out j) ({0} : Set ℝ) :=
      disjoint_singleton_right.mpr (fun h => hzero h.2)
    rw [ownedAllocation,ite_eq_left hj,measureReal_union hd (measurableSet_singleton 0)]
    simp only [measureReal_def,measure_singleton,ENNReal.toReal_zero,add_zero]
  · simp only [ownedAllocation,ite_eq_right hj,union_empty]

theorem owned_domain_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (hzero : 0 ∉ U) (c : Fin n) (out : IntervalCore.Outcome n)
    (hcorrect : DomainCorrect cost U c out) :
    Pairwise (fun i j => Disjoint (ownedAllocation U c out i) (ownedAllocation U c out j)) ∧
    (∀ i, Disjoint (ownedAllocation U c out i) (domainResidue U out)) ∧
    (⋃ i, ownedAllocation U c out i) ∪ domainResidue U out = U ∪ {0} ∧
    (∀ i j, (cost i).real (ownedAllocation U c out i) ≤ (cost i).real (ownedAllocation U c out j)) ∧
    (cost c).real (domainResidue U out) ≤ ((n-1 : ℕ) : ℝ)/n*(cost c).real (U ∪ {0}) ∧
    ∃ j, (cost c).real (domainResidue U out)/(n-1 : ℕ) ≤
      (cost c).real (ownedAllocation U c out j)-(cost c).real (ownedAllocation U c out c) := by
  obtain ⟨hd,hdr,hcover,hEF,hshrink,j,hgap⟩ := hcorrect
  have ha0 : ∀ i, Disjoint (domainAllocation U c out i) ({0} : Set ℝ) :=
    fun i => disjoint_singleton_right.mpr (fun h => hzero h.2)
  have hr0 : Disjoint (domainResidue U out) ({0} : Set ℝ) :=
    disjoint_singleton_right.mpr (fun h => hzero h.2)
  have htotal : (cost c).real (U ∪ {0}) = (cost c).real U := by
    rw [measureReal_union (disjoint_singleton_right.mpr hzero) (measurableSet_singleton 0)]
    simp only [measureReal_def,measure_singleton,ENNReal.toReal_zero,add_zero]
  refine ⟨?_,?_,?_,?_,?_,j,?_⟩
  · intro i j hij
    have hbase := hd hij
    by_cases hi : i = c <;> by_cases hj : j = c
    · exact (hij (hi.trans hj.symm)).elim
    · simp only [ownedAllocation,ite_eq_left hi,ite_eq_right hj,union_empty]
      exact disjoint_union_left.mpr ⟨hbase,(ha0 j).symm⟩
    · simp only [ownedAllocation,ite_eq_right hi,ite_eq_left hj,union_empty]
      exact disjoint_union_right.mpr ⟨hbase,ha0 i⟩
    · simpa only [ownedAllocation,ite_eq_right hi,ite_eq_right hj,union_empty] using hbase
  · intro i
    by_cases hi : i = c
    · simp only [ownedAllocation,ite_eq_left hi]
      exact disjoint_union_left.mpr ⟨hdr i,hr0.symm⟩
    · simpa only [ownedAllocation,ite_eq_right hi,union_empty] using hdr i
  · have hsingle : (⋃ i : Fin n, if i = c then ({0} : Set ℝ) else ∅) = {0} := by
      apply Subset.antisymm
      · apply iUnion_subset
        intro i
        by_cases hi : i = c <;> simp [hi]
      · simpa only [ite_true] using
          (subset_iUnion (fun i : Fin n => if i = c then ({0} : Set ℝ) else ∅) c)
    simp only [ownedAllocation,iUnion_union_distrib,hsingle]
    calc
      ((⋃ i, domainAllocation U c out i) ∪ {0}) ∪ domainResidue U out =
          ((⋃ i, domainAllocation U c out i) ∪ domainResidue U out) ∪ {0} := by ac_rfl
      _ = U ∪ {0} := by rw [hcover]
  · intro i j
    simpa only [owned_allocation_value cost U hzero] using hEF i j
  · simpa only [htotal] using hshrink
  · simpa only [owned_allocation_value cost U hzero] using hgap

theorem owned_unit_cover (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (out : IntervalCore.Outcome n)
    (hcorrect : DomainCorrect cost (Ioc 0 1) c out) :
    (⋃ i, ownedAllocation (Ioc 0 1) c out i) ∪ domainResidue (Ioc 0 1) out = Icc 0 1 := by
  have hzero : (0 : ℝ) ∉ Ioc 0 1 := fun h => lt_irrefl 0 h.1
  simpa only [Ioc_union_left zero_le_one] using
    (owned_domain_correct cost (Ioc 0 1) hzero c out hcorrect).2.2.1

end EnvyFreeResearch.Full.Chores.OrderedUnion
