import EnvyFreeResearch.Full.ChoresOuterLocalProgram

/-! Exact physical domain and cached residue values used by the local step. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot
variable {n : ℕ}

theorem mem_batch_material (xs : List (Snapshot.Output n)) (x : ℝ) :
    x ∈ batchMaterial xs ↔ ∃ out ∈ xs, x ∈ out.carrier := by
  induction xs with
  | nil => simp [batchMaterial]
  | cons first rest ih =>
    constructor
    · intro hx
      rcases hx with hf | hr
      · exact ⟨first,List.mem_cons_self,hf⟩
      · obtain ⟨out,ho,hx⟩ := ih.mp hr
        exact ⟨out,List.mem_cons_of_mem _ ho,hx⟩
    · rintro ⟨out,ho,hx⟩
      rcases List.mem_cons.mp ho with rfl | ho
      · exact Or.inl hx
      · exact Or.inr (ih.mpr ⟨out,ho,hx⟩)

theorem batch_material_occurrences (xs : List (Snapshot.Output n)) :
    (⋃ root : Fin xs.length, ⋃ p : Fin n, (xs.get root).piece p)=batchMaterial xs := by
  ext x
  constructor
  · intro hx
    obtain ⟨root,p,hx⟩ := by simpa only [mem_iUnion] using hx
    exact (mem_batch_material xs x).mpr ⟨xs.get root,List.get_mem _ _,mem_iUnion.mpr ⟨p,hx⟩⟩
  · intro hx
    obtain ⟨out,ho,hx⟩ := (mem_batch_material xs x).mp hx
    obtain ⟨root,rfl⟩ := List.mem_iff_get.mp ho
    exact mem_iUnion.mpr ⟨root,hx⟩

theorem preprocessing_mutable_domain (out : Preprocessing.Output n) :
    material out.residue ∪ (⋃ root : Fin out.originals.length, ⋃ p : Fin n,
      (out.originals.get root).piece p)=preprocessingDomain out := by
  rw [batch_material_occurrences,preprocessingDomain,union_comm]

theorem preprocessing_residue_values (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (out : Preprocessing.Output n)
    (hclear : Snapshot.AnyChain cost (material out.middle) out.clearance out.residue) :
    cachedValue out.residue=(fun i => (cost i).real (material out.residue)) := by
  funext i
  exact Clearance.cached_total cost _ _ hclear.final_cache i

end EnvyFreeResearch.Full.Chores.Outer
