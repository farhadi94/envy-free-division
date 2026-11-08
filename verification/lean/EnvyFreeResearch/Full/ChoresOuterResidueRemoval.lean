import EnvyFreeResearch.Full.ChoresOuterResidueAssembly

/-! Remove a union of whole marked private slots without oracle queries.
The caller identifies the actual extracted suffixes with these slots. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

def removePrivate (cache : RootId → Fin n → List (Parent n))
    (marked : Finset (RootId × Fin n)) (r : RootId) (p : Fin n) : List (Parent n) :=
  if (r,p) ∈ marked then [] else cache r p

def markedPrivate (cache : RootId → Fin n → List (Parent n))
    (marked : Finset (RootId × Fin n)) : Set ℝ :=
  ⋃ a ∈ marked, material (cache a.1 a.2)

theorem remove_private_subset (cache : RootId → Fin n → List (Parent n))
    (marked : Finset (RootId × Fin n)) (r : RootId) (p : Fin n) :
    material (removePrivate cache marked r p) ⊆ material (cache r p) := by
  unfold removePrivate
  split
  · exact empty_subset _
  · exact Subset.rfl

theorem marked_remainder_partition (cache : RootId → Fin n → List (Parent n))
    (marked : Finset (RootId × Fin n)) :
    markedPrivate cache marked ∪ privateUnion (removePrivate cache marked)=privateUnion cache := by
  ext x
  simp only [markedPrivate,privateUnion,mem_union,mem_iUnion]
  constructor
  · rintro (⟨a,ha,hx⟩ | ⟨r,p,hx⟩)
    · exact ⟨a.1,a.2,hx⟩
    · exact ⟨r,p,remove_private_subset cache marked r p hx⟩
  · rintro ⟨r,p,hx⟩
    by_cases h : (r,p) ∈ marked
    · exact Or.inl ⟨(r,p),h,hx⟩
    · apply Or.inr
      exact ⟨r,p,by simpa only [removePrivate,ite_eq_right h] using hx⟩

theorem marked_remainder_disjoint (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n)) (marked : Finset (RootId × Fin n))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p) :
    Disjoint (markedPrivate cache marked) (privateUnion (removePrivate cache marked)) := by
  apply disjoint_iUnion_left.mpr
  intro a
  apply disjoint_iUnion_left.mpr
  intro ha
  apply disjoint_iUnion_right.mpr
  intro r
  apply disjoint_iUnion_right.mpr
  intro p
  by_cases hm : (r,p) ∈ marked
  · simp [removePrivate,hm,material]
  · have hne : a ≠ (r,p) := fun heq => hm (heq ▸ ha)
    exact (G.disjoint hne).mono (hsub a.1 a.2)
      ((remove_private_subset cache marked r p).trans (hsub r p))

theorem full_removed_exact (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n)) (marked : Finset (RootId × Fin n))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p)
    (R : Set ℝ) (hd : ∀ r p, Disjoint R (G.piece r p)) :
    R ∪ privateUnion (removePrivate cache marked)=
      (R ∪ privateUnion cache) \ markedPrivate cache marked := by
  have hr : Disjoint R (markedPrivate cache marked) := by
    apply disjoint_iUnion_right.mpr
    intro a
    apply disjoint_iUnion_right.mpr
    intro _
    exact (hd a.1 a.2).mono_right (hsub a.1 a.2)
  have hm := marked_remainder_disjoint G cache marked hsub
  rw [← marked_remainder_partition cache marked]
  ext x
  constructor
  · rintro (hx | hx)
    · exact ⟨Or.inl hx,fun h => disjoint_left.mp hr hx h⟩
    · exact ⟨Or.inr (Or.inr hx),fun h => disjoint_left.mp hm h hx⟩
  · rintro ⟨hx,hn⟩
    rcases hx with hx | (hx | hx)
    · exact Or.inl hx
    · exact (hn hx).elim
    · exact Or.inr hx

theorem removed_bundle_correct (P : Profile (Fin n))
    (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n)) (marked : Finset (RootId × Fin n))
    (hv : ∀ r p, Valid P (cache r p) ∧ Ordered (cache r p))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p) :
    CacheValid P (privateUnion (removePrivate cache marked))
      (privateBundle (removePrivate cache marked)) := by
  have hf : Augment.FamilyValid P (fun a : RootId × Fin n => removePrivate cache marked a.1 a.2) := by
    constructor
    · intro a
      by_cases ha : a ∈ marked
      · simp [removePrivate,ha,Valid,Ordered]
      · simpa only [removePrivate,Prod.mk.eta,ite_eq_right ha] using hv a.1 a.2
    · intro a b hab
      exact (G.disjoint hab).mono
        ((remove_private_subset cache marked a.1 a.2).trans (hsub a.1 a.2))
        ((remove_private_subset cache marked b.1 b.2).trans (hsub b.1 b.2))
  obtain ⟨hvalid,horder,hm⟩ := Augment.join_labels_valid P _ hf
    Finset.univ.toList (Finset.nodup_toList _)
  refine ⟨hvalid,horder,?_⟩
  simp only [Finset.mem_toList,Finset.mem_univ,iUnion_true] at hm
  refine hm.trans ?_
  ext x
  simp only [privateUnion,mem_iUnion]
  constructor
  · rintro ⟨⟨r,p⟩,hx⟩
    exact ⟨r,p,hx⟩
  · rintro ⟨r,p,hx⟩
    exact ⟨(r,p),hx⟩

theorem full_removed_cache_correct (P : Profile (Fin n))
    (G : PackageGeometry.Pieces RootId (Fin n))
    (cache : RootId → Fin n → List (Parent n)) (marked : Finset (RootId × Fin n))
    (hv : ∀ r p, Valid P (cache r p) ∧ Ordered (cache r p))
    (hsub : ∀ r p, material (cache r p) ⊆ G.piece r p)
    (R : Set ℝ) (R0 : List (Parent n)) (hR : CacheValid P R R0)
    (hd : ∀ r p, Disjoint R (G.piece r p)) :
    CacheValid P ((R ∪ privateUnion cache) \ markedPrivate cache marked)
      (fullResidueCache R0 (removePrivate cache marked)) := by
  have hc := removed_bundle_correct P G cache marked hv hsub
  have hdis : Disjoint (material R0) (material (privateBundle (removePrivate cache marked))) := by
    rw [hR.2.2,hc.2.2]
    apply disjoint_iUnion_right.mpr
    intro r
    apply disjoint_iUnion_right.mpr
    intro p
    exact (hd r p).mono_right ((remove_private_subset cache marked r p).trans (hsub r p))
  have hh := Augment.assemble_join P R0 (privateBundle (removePrivate cache marked))
    hR.1 hc.1 hR.2.1 hc.2.1 hdis
  refine ⟨hh.1,hh.2.1,?_⟩
  rw [fullResidueCache,hh.2.2,hR.2.2,hc.2.2]
  exact full_removed_exact G cache marked hsub R hd
end EnvyFreeResearch.Full.Chores.Outer
