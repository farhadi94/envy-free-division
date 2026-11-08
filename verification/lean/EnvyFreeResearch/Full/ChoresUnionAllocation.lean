import EnvyFreeResearch.Full.ChoresUnionCompiler
import EnvyFreeResearch.Full.ChoresIntervalAllocation

/-! Transfer of the actual interval Core allocation to its recorded physical
domain. Intersection removes virtual gaps, retaining all physical material,
including zero-cost components. The isolated endpoint 0 is dealt with by a
separate literal-ownership wrapper. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ}

theorem cache_domain_subset (P : Profile (Fin n)) (U : Set ℝ)
    (cache : List (Parent n)) (hc : CacheValid P U cache) : U ⊆ Ioc 0 1 := by
  intro x hx
  obtain ⟨p,hp,hpx⟩ := (mem_material_iff cache x).mp (hc.2.2.symm ▸ hx)
  have hb := ((valid_iff_forall P cache).mp hc.1 p hp).1
  exact ⟨hb.1.trans_lt hpx.1,hpx.2.trans hb.2.2⟩

def domainAllocation (U : Set ℝ) (c : Fin n) (out : IntervalCore.Outcome n) (i : Fin n) : Set ℝ :=
  IntervalCore.outputAllocation 0 1 c out i ∩ U

def domainResidue (U : Set ℝ) (out : IntervalCore.Outcome n) : Set ℝ :=
  IntervalCore.outputResidue out ∩ U

theorem interval_allocation_measurable (c : Fin n) (out : IntervalCore.Outcome n) (i : Fin n) :
    MeasurableSet (IntervalCore.outputAllocation 0 1 c out i) := by
  classical
  cases out with
  | zero z =>
    by_cases h : i = z <;> simp only [IntervalCore.outputAllocation,h,ite_true,ite_false]
    · exact measurableSet_Icc
    · exact MeasurableSet.empty
  | prefixes parent s =>
    apply MeasurableSet.union measurableSet_Ioc
    by_cases h : i = c <;> simp only [h,ite_true,ite_false]
    · exact measurableSet_singleton 0
    · exact MeasurableSet.empty

theorem interval_residue_measurable (out : IntervalCore.Outcome n) :
    MeasurableSet (IntervalCore.outputResidue out) := by
  cases out with
  | zero z => exact MeasurableSet.empty
  | prefixes parent s => exact MeasurableSet.iUnion (fun _ => measurableSet_Ioc)

def DomainCorrect (cost : Fin n → Measure ℝ) (U : Set ℝ) (c : Fin n)
    (out : IntervalCore.Outcome n) : Prop :=
  Pairwise (fun i j => Disjoint (domainAllocation U c out i) (domainAllocation U c out j)) ∧
  (∀ i, Disjoint (domainAllocation U c out i) (domainResidue U out)) ∧
  (⋃ i, domainAllocation U c out i) ∪ domainResidue U out = U ∧
  (∀ i j, (cost i).real (domainAllocation U c out i) ≤
    (cost i).real (domainAllocation U c out j)) ∧
  (cost c).real (domainResidue U out) ≤ ((n-1 : ℕ) : ℝ)/n*(cost c).real U ∧
  ∃ j, (cost c).real (domainResidue U out)/(n-1 : ℕ) ≤
    (cost c).real (domainAllocation U c out j)-(cost c).real (domainAllocation U c out c)

theorem domain_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (hU : U ⊆ Icc 0 1) (c : Fin n) (out : IntervalCore.Outcome n)
    (hcorrect : IntervalCore.MeasuredCorrect (fun i => (cost i).restrict U) c 0 1 out) :
    DomainCorrect cost U c out := by
  have halloc : ∀ i j, ((cost i).restrict U).real (IntervalCore.outputAllocation 0 1 c out j) =
      (cost i).real (domainAllocation U c out j) := by
    intro i j
    exact measureReal_restrict_apply (interval_allocation_measurable c out j)
  have hres : ((cost c).restrict U).real (IntervalCore.outputResidue out) =
      (cost c).real (domainResidue U out) :=
    measureReal_restrict_apply (interval_residue_measurable out)
  have htotal : ((cost c).restrict U).real (Icc 0 1) = (cost c).real U := by
    rw [measureReal_restrict_apply measurableSet_Icc,inter_eq_right.mpr hU]
  obtain ⟨hd,hdr,hcover,hEF,hshrink,j,hgap⟩ := hcorrect
  refine ⟨fun i j hij => (hd hij).mono inter_subset_left inter_subset_left,
    fun i => (hdr i).mono inter_subset_left inter_subset_left,?_,?_,?_,j,?_⟩
  · change (⋃ i, IntervalCore.outputAllocation 0 1 c out i ∩ U) ∪
      (IntervalCore.outputResidue out ∩ U) = U
    rw [← iUnion_inter,← union_inter_distrib_right,hcover,inter_eq_right.mpr hU]
  · intro i j
    simpa only [halloc] using hEF i j
  · simpa only [hres,htotal] using hshrink
  · simpa only [hres,halloc] using hgap

end EnvyFreeResearch.Full.Chores.OrderedUnion
