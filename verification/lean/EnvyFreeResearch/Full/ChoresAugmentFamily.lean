import EnvyFreeResearch.Full.ChoresAugmentCache

/-! A transfer between two labelled pieces preserves the complete physical
partition. The source keeps its entire suffix and the destination receives
only the cut prefix, assembled from existing endpoint records. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Label : Type*} [DecidableEq Label]

def familyMaterial (pieces : Label → List (Parent n)) : Set ℝ := ⋃ j, material (pieces j)

def FamilyValid (P : Profile (Fin n)) (pieces : Label → List (Parent n)) : Prop :=
  (∀ j, Valid P (pieces j) ∧ Ordered (pieces j)) ∧
    Pairwise (fun j k => Disjoint (material (pieces j)) (material (pieces k)))

def transferState (pieces : Label → List (Parent n)) (source destination : Label)
    (out : Split n) : Label → List (Parent n) :=
  Function.update (Function.update pieces source out.suffixParts) destination
    (assemble (pieces destination ++ out.prefixParts))

theorem transfer_source (pieces : Label → List (Parent n)) (s d : Label) (h : s ≠ d) (out : Split n) :
    transferState pieces s d out s=out.suffixParts := by simp [transferState,h]

theorem transfer_destination (pieces : Label → List (Parent n)) (s d : Label) (out : Split n) :
    transferState pieces s d out d=assemble (pieces d++out.prefixParts) := by simp [transferState]

theorem transfer_other (pieces : Label → List (Parent n)) (s d j : Label)
    (hs : j ≠ s) (hd : j ≠ d) (out : Split n) : transferState pieces s d out j=pieces j := by
  simp [transferState,hs,hd]

theorem transfer_material (pieces : Label → List (Parent n)) (s d : Label) (h : s ≠ d) (out : Split n)
    (hsplit : material out.prefixParts ∪ material out.suffixParts=material (pieces s)) :
    familyMaterial (transferState pieces s d out)=familyMaterial pieces := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    by_cases hjd : j=d
    · subst j
      rw [transfer_destination,assemble_material,material_append] at hj
      rcases hj with hj | hj
      · exact mem_iUnion.mpr ⟨d,hj⟩
      · exact mem_iUnion.mpr ⟨s,hsplit ▸ Or.inl hj⟩
    · by_cases hjs : j=s
      · subst j
        rw [transfer_source pieces s d h] at hj
        exact mem_iUnion.mpr ⟨s,hsplit ▸ Or.inr hj⟩
      · rw [transfer_other pieces s d j hjs hjd] at hj
        exact mem_iUnion.mpr ⟨j,hj⟩
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    by_cases hjs : j=s
    · subst j
      rw [← hsplit] at hj
      rcases hj with hj | hj
      · apply mem_iUnion.mpr
        refine ⟨d,?_⟩
        rw [transfer_destination,assemble_material,material_append]
        exact Or.inr hj
      · exact mem_iUnion.mpr ⟨s,by rw [transfer_source pieces s d h]; exact hj⟩
    · by_cases hjd : j=d
      · subst j
        apply mem_iUnion.mpr
        refine ⟨d,?_⟩
        rw [transfer_destination,assemble_material,material_append]
        exact Or.inl hj
      · exact mem_iUnion.mpr ⟨j,by rw [transfer_other pieces s d j hjs hjd]; exact hj⟩

theorem transfer_valid (P : Profile (Fin n)) (pieces : Label → List (Parent n))
    (hv : FamilyValid P pieces) (s d : Label) (h : s ≠ d) (out : Split n)
    (hpre : Valid P out.prefixParts) (hsuf : Valid P out.suffixParts)
    (horder : Ordered (out.prefixParts++out.suffixParts))
    (hsplit : material out.prefixParts ∪ material out.suffixParts=material (pieces s))
    (hdis : Disjoint (material out.prefixParts) (material out.suffixParts)) :
    FamilyValid P (transferState pieces s d out) := by
  have hpreSub : material out.prefixParts ⊆ material (pieces s) := by
    rw [← hsplit]; exact subset_union_left
  have hsufSub : material out.suffixParts ⊆ material (pieces s) := by
    rw [← hsplit]; exact subset_union_right
  have hporder : Ordered out.prefixParts := (List.pairwise_append.mp horder).1
  have hsorder : Ordered out.suffixParts := (List.pairwise_append.mp horder).2.1
  have hjoin := assemble_join P (pieces d) out.prefixParts (hv.1 d).1 hpre (hv.1 d).2 hporder
    ((hv.2 h.symm).mono_right hpreSub)
  have hdest : material (transferState pieces s d out d)=material (pieces d) ∪ material out.prefixParts := by
    rw [transfer_destination]; exact hjoin.2.2
  constructor
  · intro j
    by_cases hjd : j=d
    · subst j; rw [transfer_destination]; exact ⟨hjoin.1,hjoin.2.1⟩
    · by_cases hjs : j=s
      · subst j; rw [transfer_source pieces s d h]; exact ⟨hsuf,hsorder⟩
      · rw [transfer_other pieces s d j hjs hjd]; exact hv.1 j
  · intro j k hjk
    by_cases hjd : j=d
    · subst j
      have hkd : k ≠ d := Ne.symm hjk
      rw [hdest]
      apply disjoint_union_left.mpr
      by_cases hks : k=s
      · subst k
        rw [transfer_source pieces s d h]
        exact ⟨(hv.2 h.symm).mono_right hsufSub,hdis⟩
      · rw [transfer_other pieces s d k hks hkd]
        exact ⟨hv.2 hjk,(hv.2 (Ne.symm hks)).mono_left hpreSub⟩
    · by_cases hkd : k=d
      · subst k
        rw [hdest]
        apply disjoint_union_right.mpr
        by_cases hjs : j=s
        · subst j
          rw [transfer_source pieces s d h]
          exact ⟨(hv.2 h).mono_left hsufSub,hdis.symm⟩
        · rw [transfer_other pieces s d j hjs hjd]
          exact ⟨hv.2 hjk,(hv.2 hjs).mono_right hpreSub⟩
      · by_cases hjs : j=s
        · subst j
          rw [transfer_source pieces s d h,transfer_other pieces s d k (Ne.symm hjk) hkd]
          exact (hv.2 hjk).mono_left hsufSub
        · by_cases hks : k=s
          · subst k
            rw [transfer_other pieces s d j hjs hjd,transfer_source pieces s d h]
            exact (hv.2 hjk).mono_right hsufSub
          · rw [transfer_other pieces s d j hjs hjd,transfer_other pieces s d k hks hkd]
            exact hv.2 hjk

theorem transfer_value (P : Profile (Fin n)) (pieces : Label → List (Parent n))
    (hv : ∀ j, Valid P (pieces j)) (s d : Label) (out : Split n)
    (hpre : Valid P out.prefixParts) (i : Fin n) :
    OrderedUnion.cachedValue (transferState pieces s d out d) i=
      OrderedUnion.cachedValue (pieces d) i+OrderedUnion.cachedValue out.prefixParts i := by
  rw [transfer_destination,assemble_value P ((valid_append P _ _).mpr ⟨hv d,hpre⟩)]
  induction pieces d with
  | nil => simp [OrderedUnion.cachedValue]
  | cons p ps ih => simp only [List.cons_append,OrderedUnion.cachedValue,ih]; ring

end EnvyFreeResearch.Full.Chores.Augment
