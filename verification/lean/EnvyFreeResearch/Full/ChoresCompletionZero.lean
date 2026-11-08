import EnvyFreeResearch.Full.ChoresCompletionAllocation

/-! Query-free completion at a completed envy-free boundary when one
active agent assigns zero cost to the entire remaining domain. Physical
joins retain all positive-length zero-cost material. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Agent : Type*}

def Allocation.join (first second : Allocation n Agent) : Allocation n Agent :=
  ⟨fun i => Augment.assemble (first.pieces i++second.pieces i)⟩

theorem Allocation.join_material (first second : Allocation n Agent) (i : Agent) :
    material ((first.join second).pieces i)=material (first.pieces i) ∪ material (second.pieces i) :=
  (Augment.assemble_material _).trans (Augment.material_append _ _)

theorem Allocation.join_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Agent → Fin n) (U V : Set ℝ) (first second : Allocation n Agent)
    (hfirst : first.Sound cost agent U) (hsecond : second.Sound cost agent V)
    (hd : Disjoint U V) : (first.join second).Sound cost agent (U ∪ V) := by
  have hcross (i j : Agent) : Disjoint (material (first.pieces i)) (material (second.pieces j)) :=
    hd.mono (hfirst.subset cost agent U first i) (hsecond.subset cost agent V second j)
  have hvalue (i : Agent) (observer : Fin n) :
      (cost observer).real (material ((first.join second).pieces i))=
        (cost observer).real (material (first.pieces i))+(cost observer).real (material (second.pieces i)) := by
    rw [Allocation.join_material]
    exact measureReal_union (hcross i i) (material_measurable _)
  constructor
  · intro i
    have h := Augment.assemble_join (measureProfile cost) (first.pieces i) (second.pieces i)
      (hfirst.cache i).1 (hsecond.cache i).1 (hfirst.cache i).2.1 (hsecond.cache i).2.1 (hcross i i)
    exact ⟨h.1,h.2.1,rfl⟩
  · intro i j hij
    rw [Allocation.join_material,Allocation.join_material]
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hfirst.disjoint hij,hcross i j⟩,
      disjoint_union_right.mpr ⟨(hcross j i).symm,hsecond.disjoint hij⟩⟩
  · simp only [Allocation.join_material,iUnion_union_distrib,hfirst.cover,hsecond.cover]
  · intro i j
    rw [hvalue,hvalue]
    exact add_le_add (hfirst.envy_free i j) (hsecond.envy_free i j)

def zeroAllocation (z : Agent) (cache : List (Parent n)) : Allocation n Agent :=
  ⟨fun i => if i=z then cache else []⟩

theorem zero_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Agent → Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (z : Agent)
    (hz : (cost (agent z)).real U=0) :
    (zeroAllocation z cache).Sound cost agent U := by
  constructor
  · intro i
    by_cases hi : i=z
    · simpa only [zeroAllocation,hi,ite_true] using (show CacheValid (measureProfile cost) (material cache) cache from ⟨hc.1,hc.2.1,rfl⟩)
    · simp [zeroAllocation,hi,CacheValid,Valid,Ordered,material]
  · intro i j hij
    by_cases hi : i=z <;> by_cases hj : j=z
    · exact (hij (hi.trans hj.symm)).elim
    · simp [zeroAllocation,hi,hj,material]
    · simp [zeroAllocation,hi,hj,material]
    · simp [zeroAllocation,hi,hj,material]
  · ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases he : i=z
      · simpa only [zeroAllocation,he,ite_true,hc.2.2] using hi
      · simp only [zeroAllocation,he,ite_false,material,mem_empty_iff_false] at hi
    · intro hx
      apply mem_iUnion.mpr
      exact ⟨z,by simpa only [zeroAllocation,ite_true,hc.2.2] using hx⟩
  · intro i j
    by_cases hi : i=z
    · subst i
      have hown : (cost (agent z)).real (material ((zeroAllocation z cache).pieces z))=0 := by
        simpa only [zeroAllocation,ite_true,hc.2.2] using hz
      rw [hown]
      exact measureReal_nonneg
    · simp only [zeroAllocation,hi,ite_false,material,measureReal_empty]
      exact measureReal_nonneg

theorem zero_complete (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Agent → Fin n) (allocated remaining : Set ℝ) (base : Allocation n Agent)
    (hbase : base.Sound cost agent allocated)
    (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) remaining cache)
    (hd : Disjoint allocated remaining) (z : Agent) (hz : (cost (agent z)).real remaining=0) :
    (base.join (zeroAllocation z cache)).Sound cost agent (allocated ∪ remaining) :=
  Allocation.join_sound cost agent allocated remaining base (zeroAllocation z cache) hbase
    (zero_sound cost agent remaining cache hc z hz) hd

end EnvyFreeResearch.Full.Chores.Completion
