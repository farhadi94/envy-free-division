import EnvyFreeResearch.Full.ChoresOuterPrivateCache
import EnvyFreeResearch.Full.ChoresAugmentComplement

/-! Literal residual domain and its zero-query cache assembly, including
all frozen original roots and the original outside residue. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

def privateUnion (cache : RootId → Fin n → List (Parent n)) : Set ℝ :=
  ⋃ r, ⋃ p, material (cache r p)

def privateBundle (cache : RootId → Fin n → List (Parent n)) : List (Parent n) :=
  Augment.joinLabels (fun a : RootId × Fin n => cache a.1 a.2) Finset.univ.toList

variable (P : Profile (Fin n)) (G : PackageGeometry.Pieces RootId (Fin n))
  (retained privateCache : RootId → Fin n → List (Parent n))
  (hprivate : PrivateCorrect P G.piece retained privateCache)
include hprivate

theorem private_subset (r : RootId) (p : Fin n) :
    material (privateCache r p) ⊆ G.piece r p := by
  rw [(hprivate r p).2.2]
  exact sdiff_subset

theorem private_bundle_correct : CacheValid P (privateUnion privateCache) (privateBundle privateCache) := by
  have hv : Augment.FamilyValid P (fun a : RootId × Fin n => privateCache a.1 a.2) := by
    refine ⟨fun a => ⟨(hprivate a.1 a.2).1,(hprivate a.1 a.2).2.1⟩,?_⟩
    intro a b hab
    exact (G.disjoint hab).mono (private_subset P G retained privateCache hprivate a.1 a.2)
      (private_subset P G retained privateCache hprivate b.1 b.2)
  obtain ⟨hvalid,horder,hm⟩ := Augment.join_labels_valid P _ hv
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

theorem retained_private_disjoint
    (hsub : ∀ r p, material (retained r p) ⊆ G.piece r p) :
    Disjoint (privateUnion retained) (privateUnion privateCache) := by
  apply disjoint_iUnion_left.mpr
  intro r
  apply disjoint_iUnion_left.mpr
  intro p
  apply disjoint_iUnion_right.mpr
  intro s
  apply disjoint_iUnion_right.mpr
  intro q
  by_cases h : (r,p)=(s,q)
  · have hr := congrArg Prod.fst h
    have hp := congrArg Prod.snd h
    change r=s at hr
    change p=q at hp
    subst s
    subst q
    rw [(hprivate r p).2.2]
    exact disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  · exact (G.disjoint h).mono (hsub r p) (private_subset P G retained privateCache hprivate s q)

theorem private_union_partition
    (hsub : ∀ r p, material (retained r p) ⊆ G.piece r p) :
    privateUnion retained ∪ privateUnion privateCache = ⋃ r, ⋃ p, G.piece r p := by
  ext x
  simp only [privateUnion,mem_union,mem_iUnion]
  constructor
  · rintro (⟨r,p,hx⟩ | ⟨r,p,hx⟩)
    · exact ⟨r,p,hsub r p hx⟩
    · exact ⟨r,p,private_subset P G retained privateCache hprivate r p hx⟩
  · rintro ⟨r,p,hx⟩
    by_cases hr : x ∈ material (retained r p)
    · exact Or.inl ⟨r,p,hr⟩
    · apply Or.inr
      refine ⟨r,p,?_⟩
      rw [(hprivate r p).2.2]
      exact ⟨hx,hr⟩

def fullResidueCache (R0 : List (Parent n)) (privateCache : RootId → Fin n → List (Parent n)) :
    List (Parent n) := Augment.assemble (R0++privateBundle privateCache)

theorem full_residue_cache_correct (R : Set ℝ) (R0 : List (Parent n))
    (hR : CacheValid P R R0) (hd : ∀ r p, Disjoint R (G.piece r p)) :
    CacheValid P (R ∪ privateUnion privateCache) (fullResidueCache R0 privateCache) := by
  have hc := private_bundle_correct P G retained privateCache hprivate
  have hdis : Disjoint (material R0) (material (privateBundle privateCache)) := by
    rw [hR.2.2,hc.2.2]
    apply disjoint_iUnion_right.mpr
    intro r
    apply disjoint_iUnion_right.mpr
    intro p
    exact (hd r p).mono_right (private_subset P G retained privateCache hprivate r p)
  have hh := Augment.assemble_join P R0 (privateBundle privateCache)
    hR.1 hc.1 hR.2.1 hc.2.1 hdis
  exact ⟨hh.1,hh.2.1,by rw [fullResidueCache,hh.2.2,hR.2.2,hc.2.2]⟩
end EnvyFreeResearch.Full.Chores.Outer
