import EnvyFreeResearch.Full.ChoresAugmentProgram

/-! Whole-piece augmentation for actual finite nonnegative nonatomic
measures, with all physical caches, complete complement and exact envy
comparisons exposed for the two-group completion protocol. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n k : ℕ} {Label : Type*} [LinearOrder Label] [Fintype Label]

structure WholeOutput.Correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (recipient : ℕ → Fin n) (U : Set ℝ) (original : Label → List (Parent n))
    (out : WholeOutput n k Label) : Prop where
  allocated_cache : ∀ i, CacheValid (measureProfile cost) (material (out.allocated i)) (out.allocated i)
  remainder_cache : CacheValid (measureProfile cost) (material out.remainder) out.remainder
  disjoint : Pairwise (fun i j => Disjoint (material (out.allocated i)) (material (out.allocated j)))
  remainder_disjoint : ∀ i, Disjoint (material (out.allocated i)) (material out.remainder)
  cover : (⋃ i, material (out.allocated i)) ∪ material out.remainder=U
  label_injective : Function.Injective out.originalLabel
  whole_piece : ∀ i, material (original (out.originalLabel i)) ⊆ material (out.allocated i)
  envy_free : ∀ i j, (cost (recipient i.val)).real (material (out.allocated i)) ≤
    (cost (recipient i.val)).real (material (out.allocated j))

theorem whole_physical_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (recipient : ℕ → Fin n) (k : ℕ) (U : Set ℝ) (original : Label → List (Parent n))
    (hv : FamilyValid (measureProfile cost) original) (hU : familyMaterial original=U)
    (initial : List Label) (hnd : initial.Nodup) (hlen : initial.length=2^(k+1)) (fallback : Label)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (wholeProgram recipient k original initial fallback) prior out trace ∧
      trace.length ≤ (2^k-1)*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 2^k-1 ∧
      out.Correct cost recipient U original := by
  obtain ⟨out,trace,hexec,hQ,hC,hv',hrv,hro,hdis,hrdis,hcover,hinj,hwhole,hEF⟩ :=
    whole_program_correct (measureProfile cost) (fun i => prefixCost_monotone (cost i) 0)
      oracle hpolicy recipient k original hv initial hnd hlen fallback prior
  refine ⟨out,trace,hexec,hQ,hC,⟨?_,⟨hrv,hro,rfl⟩,hdis,hrdis,hcover.trans hU,hinj,hwhole,?_⟩⟩
  · exact fun i => ⟨(hv' i).1,(hv' i).2,rfl⟩
  · intro i j
    rw [material_value cost _ (hv' i).1 (hv' i).2,material_value cost _ (hv' j).1 (hv' j).2]
    exact hEF i j

end EnvyFreeResearch.Full.Chores.Augment
