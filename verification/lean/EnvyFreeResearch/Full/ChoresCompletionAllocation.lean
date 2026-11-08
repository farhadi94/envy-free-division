import EnvyFreeResearch.Full.ChoresCompletionSplit

/-! Physical allocation interface for recursive calls on a finite active
population. Caches retain all ambient observer values, while envy is tested
only for the embedded active agents. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n : ℕ} {Agent : Type*}

structure Allocation (n : ℕ) (Agent : Type*) where
  pieces : Agent → List (Parent n)

structure Allocation.Sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Agent → Fin n) (U : Set ℝ) (out : Allocation n Agent) : Prop where
  cache : ∀ i, CacheValid (measureProfile cost) (material (out.pieces i)) (out.pieces i)
  disjoint : Pairwise (fun i j => Disjoint (material (out.pieces i)) (material (out.pieces j)))
  cover : (⋃ i, material (out.pieces i))=U
  envy_free : ∀ i j, (cost (agent i)).real (material (out.pieces i)) ≤
    (cost (agent i)).real (material (out.pieces j))

theorem Allocation.Sound.subset (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Agent → Fin n) (U : Set ℝ) (out : Allocation n Agent)
    (h : out.Sound cost agent U) (i : Agent) : material (out.pieces i) ⊆ U := by
  rw [← h.cover]
  exact subset_iUnion (fun j => material (out.pieces j)) i

variable {k : ℕ} {Label : Type*}

def attach (base : Augment.WholeOutput n k Label) (child : Allocation n (Fin k)) : Allocation n (Fin k) :=
  ⟨fun i => Augment.assemble (base.allocated i++child.pieces i)⟩

theorem attach_material (base : Augment.WholeOutput n k Label) (child : Allocation n (Fin k)) (i : Fin k) :
    material ((attach base child).pieces i)=material (base.allocated i) ∪ material (child.pieces i) :=
  (Augment.assemble_material _).trans (Augment.material_append _ _)

theorem attach_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (recipient : ℕ → Fin n) (U : Set ℝ) (original : Label → List (Parent n))
    (base : Augment.WholeOutput n k Label) (hp : base.Correct cost recipient U original)
    (child : Allocation n (Fin k))
    (hc : child.Sound cost (fun i => recipient i.val) (material base.remainder)) :
    (attach base child).Sound cost (fun i => recipient i.val) U := by
  have hsub (i : Fin k) : material (child.pieces i) ⊆ material base.remainder :=
    hc.subset cost _ _ child i
  have hcross (i j : Fin k) : Disjoint (material (base.allocated i)) (material (child.pieces j)) :=
    (hp.remainder_disjoint i).mono_right (hsub j)
  have hvalue (i : Fin k) (observer : Fin n) :
      (cost observer).real (material ((attach base child).pieces i))=
        (cost observer).real (material (base.allocated i))+(cost observer).real (material (child.pieces i)) := by
    rw [attach_material]
    exact measureReal_union (hcross i i) (material_measurable _)
  constructor
  · intro i
    have h := Augment.assemble_join (measureProfile cost) (base.allocated i) (child.pieces i)
      (hp.allocated_cache i).1 (hc.cache i).1 (hp.allocated_cache i).2.1 (hc.cache i).2.1 (hcross i i)
    exact ⟨h.1,h.2.1,rfl⟩
  · intro i j hij
    rw [attach_material,attach_material]
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hp.disjoint hij,hcross i j⟩,
      disjoint_union_right.mpr ⟨(hcross j i).symm,hc.disjoint hij⟩⟩
  · simp only [attach_material,iUnion_union_distrib,hc.cover,hp.cover]
  · intro i j
    rw [hvalue,hvalue]
    exact add_le_add (hp.envy_free i j) (hc.envy_free i j)

theorem attach_contains (base : Augment.WholeOutput n k Label) (child : Allocation n (Fin k)) (i : Fin k) :
    material (base.allocated i) ⊆ material ((attach base child).pieces i) := by
  rw [attach_material]
  exact subset_union_left

end EnvyFreeResearch.Full.Chores.Completion
