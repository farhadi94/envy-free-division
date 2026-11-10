import EnvyFreeResearch.Full.ChoresOuterResidueAssembly

/-! The assembled residue is exactly the whole unallocated domain. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

theorem full_residue_exact (P : Profile (Fin n)) (G : PackageGeometry.Pieces RootId (Fin n))
    (retained privateCache : RootId → Fin n → List (Parent n))
    (hp : PrivateCorrect P G.piece retained privateCache)
    (hsub : ∀ r p, material (retained r p) ⊆ G.piece r p)
    (R : Set ℝ) (hd : ∀ r p, Disjoint R (G.piece r p)) :
    R ∪ privateUnion privateCache = (R ∪ ⋃ r, ⋃ p, G.piece r p) \ privateUnion retained := by
  have hrr : Disjoint R (privateUnion retained) := by
    apply disjoint_iUnion_right.mpr
    intro r
    apply disjoint_iUnion_right.mpr
    intro p
    exact (hd r p).mono_right (hsub r p)
  have hrp := retained_private_disjoint P G retained privateCache hp hsub
  rw [← private_union_partition P G retained privateCache hp hsub]
  ext x
  constructor
  · rintro (hx | hx)
    · exact ⟨Or.inl hx,fun hr => disjoint_left.mp hrr hx hr⟩
    · exact ⟨Or.inr (Or.inr hx),fun hr => disjoint_left.mp hrp hr hx⟩
  · rintro ⟨hx,hr⟩
    rcases hx with hx | (hx | hx)
    · exact Or.inl hx
    · exact (hr hx).elim
    · exact Or.inr hx

theorem full_residue_complement_cache (P : Profile (Fin n))
    (G : PackageGeometry.Pieces RootId (Fin n))
    (retained privateCache : RootId → Fin n → List (Parent n))
    (hp : PrivateCorrect P G.piece retained privateCache)
    (hsub : ∀ r p, material (retained r p) ⊆ G.piece r p)
    (R : Set ℝ) (R0 : List (Parent n)) (hR : CacheValid P R R0)
    (hd : ∀ r p, Disjoint R (G.piece r p)) :
    CacheValid P ((R ∪ ⋃ r, ⋃ p, G.piece r p) \ privateUnion retained)
      (fullResidueCache R0 privateCache) := by
  rw [← full_residue_exact P G retained privateCache hp hsub R hd]
  exact full_residue_cache_correct P G retained privateCache hp R R0 hR hd
end EnvyFreeResearch.Full.Chores.Outer
