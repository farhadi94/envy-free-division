import EnvyFreeResearch.Full.ChoresComponentPopulationProgram
import EnvyFreeResearch.Full.ChoresUnionEntry

/-! Finite interval output with explicit ownership of the left endpoint.
The half-open native allocation is unchanged except for that null singleton. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.UnitEntry
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion Completion QueryProgram
open scoped Classical
variable {n : ℕ}

structure Output (n : ℕ) where
  allocation : Completion.Allocation n (Fin n)
  zeroOwner : Fin n

def Output.share (out : Output n) (i : Fin n) : Set ℝ :=
  material (out.allocation.pieces i) ∪ if i=out.zeroOwner then {0} else ∅

theorem material_finite_union (ps : List (Parent n)) :
    material ps = ⋃ p ∈ ps, Ioc p.left p.right := by
  induction ps with
  | nil => simp [material]
  | cons p ps ih => simp only [material,ih,List.mem_cons,iUnion_iUnion_eq_or_left]

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (out : Output n) (hs : out.allocation.Sound cost id (Ioc 0 1))
include hs

theorem zero_not_mem (i : Fin n) : (0 : ℝ) ∉ material (out.allocation.pieces i) := by
  intro h
  have hx := hs.subset cost id (Ioc 0 1) out.allocation i h
  exact (lt_irrefl (0 : ℝ)) hx.1

theorem share_value (i j : Fin n) :
    (cost i).real (out.share j)=(cost i).real (material (out.allocation.pieces j)) := by
  by_cases hj : j=out.zeroOwner
  · rw [Output.share,ite_eq_left hj,measureReal_union
      (disjoint_singleton_right.mpr (zero_not_mem cost out hs j)) (measurableSet_singleton 0)]
    simp only [measureReal_def,measure_singleton,ENNReal.toReal_zero,add_zero]
  · simp only [Output.share,ite_eq_right hj,union_empty]

theorem share_disjoint : Pairwise (fun i j => Disjoint (out.share i) (out.share j)) := by
  intro i j hij
  have hz (a : Fin n) : Disjoint (material (out.allocation.pieces a)) ({0} : Set ℝ) :=
    disjoint_singleton_right.mpr (zero_not_mem cost out hs a)
  by_cases hi : i=out.zeroOwner <;> by_cases hj : j=out.zeroOwner
  · exact (hij (hi.trans hj.symm)).elim
  · simp only [Output.share,ite_eq_left hi,ite_eq_right hj,union_empty]
    exact disjoint_union_left.mpr ⟨hs.disjoint hij,(hz j).symm⟩
  · simp only [Output.share,ite_eq_right hi,ite_eq_left hj,union_empty]
    exact disjoint_union_right.mpr ⟨hs.disjoint hij,hz i⟩
  · simpa only [Output.share,ite_eq_right hi,ite_eq_right hj,union_empty] using hs.disjoint hij

theorem share_cover : (⋃ i, out.share i)=Icc 0 1 := by
  have hz : (⋃ i : Fin n, if i=out.zeroOwner then ({0} : Set ℝ) else ∅)={0} := by
    apply Subset.antisymm
    · apply iUnion_subset
      intro i
      by_cases hi : i=out.zeroOwner <;> simp [hi]
    · simpa only [ite_true] using
        subset_iUnion (fun i : Fin n => if i=out.zeroOwner then ({0} : Set ℝ) else ∅) out.zeroOwner
  simp only [Output.share,iUnion_union_distrib,hs.cover,hz,Ioc_union_left zero_le_one]

theorem share_envy_free (i j : Fin n) : (cost i).real (out.share i) ≤ (cost i).real (out.share j) := by
  rw [share_value cost out hs,share_value cost out hs]
  exact hs.envy_free i j

theorem interval_bounds (i : Fin n) (p : Parent n) (hp : p ∈ out.allocation.pieces i) :
    0 ≤ p.left ∧ p.left ≤ p.right ∧ p.right ≤ 1 :=
  ((valid_iff_forall _ _).mp (hs.cache i).1 p hp).1

omit hs in
theorem share_measurable (i : Fin n) : MeasurableSet (out.share i) := by
  apply (material_measurable _).union
  by_cases hi : i=out.zeroOwner <;> simp only [hi,ite_true,ite_false]
  · exact measurableSet_singleton _
  · exact MeasurableSet.empty

omit hs in
theorem finite_interval_output (i : Fin n) :
    out.share i=(⋃ p ∈ out.allocation.pieces i, Ioc p.left p.right) ∪
      if i=out.zeroOwner then {0} else ∅ := by
  rw [Output.share,material_finite_union]
end EnvyFreeResearch.Full.Chores.UnitEntry
