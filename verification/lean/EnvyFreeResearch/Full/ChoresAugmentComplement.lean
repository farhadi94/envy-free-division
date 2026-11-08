import EnvyFreeResearch.Full.ChoresAugmentFamily

/-! The unchosen labelled pieces form the exact physical complement.
They are joined into one ordered truthful cache by pure recorded-data
computation, without any further oracle calls. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Label : Type*} [DecidableEq Label]

def joinLabels (pieces : Label → List (Parent n)) (labels : List Label) : List (Parent n) :=
  assemble (labels.flatMap pieces)

theorem material_flatMap (pieces : Label → List (Parent n)) (labels : List Label) :
    material (labels.flatMap pieces)=⋃ j ∈ labels, material (pieces j) := by
  induction labels with
  | nil => simp [material]
  | cons j js ih => simp [material_append,ih]

theorem join_labels_valid (P : Profile (Fin n)) (pieces : Label → List (Parent n))
    (hv : FamilyValid P pieces) (labels : List Label) (hnd : labels.Nodup) :
    Valid P (joinLabels pieces labels) ∧ Ordered (joinLabels pieces labels) ∧
      material (joinLabels pieces labels)=⋃ j ∈ labels, material (pieces j) := by
  have hvalid : Valid P (labels.flatMap pieces) := by
    apply (valid_iff_forall _ _).mpr
    intro p hp
    obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
    exact (valid_iff_forall _ _).mp (hv.1 j).1 p hp
  have hdis : componentsDisjoint (labels.flatMap pieces) := by
    apply List.pairwise_flatMap.mpr
    refine ⟨fun j hj => ordered_components_disjoint (hv.1 j).2,?_⟩
    apply hnd.imp_of_mem
    intro j k hj hk hne p hp q hq
    exact (hv.2 hne).mono
      (fun x hx => (mem_material_iff _ _).mpr ⟨p,hp,hx⟩)
      (fun x hx => (mem_material_iff _ _).mpr ⟨q,hq,hx⟩)
  exact ⟨assemble_valid P hvalid,assemble_ordered hdis,
    (assemble_material _).trans (material_flatMap pieces labels)⟩

variable [Fintype Label] {k : ℕ}

def unchosen (choice : Fin k → Label) : Finset Label := Finset.univ \ Finset.univ.image choice

def complement (pieces : Label → List (Parent n)) (choice : Fin k → Label) : List (Parent n) :=
  joinLabels pieces (unchosen choice).toList

theorem mem_unchosen (choice : Fin k → Label) (j : Label) : j ∈ unchosen choice ↔ ∀ i, choice i ≠ j := by
  simp [unchosen]

theorem complement_material (pieces : Label → List (Parent n)) (choice : Fin k → Label) :
    material (complement pieces choice)=⋃ j ∈ unchosen choice, material (pieces j) := by
  rw [complement,joinLabels,assemble_material,material_flatMap]
  simp only [Finset.mem_toList]

theorem complement_valid (P : Profile (Fin n)) (pieces : Label → List (Parent n))
    (hv : FamilyValid P pieces) (choice : Fin k → Label) :
    Valid P (complement pieces choice) ∧ Ordered (complement pieces choice) :=
  (join_labels_valid P pieces hv _ (Finset.nodup_toList _)).imp_right And.left

theorem complement_cover (pieces : Label → List (Parent n)) (choice : Fin k → Label) :
    (⋃ i, material (pieces (choice i))) ∪ material (complement pieces choice)=familyMaterial pieces := by
  rw [complement_material]
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨choice i,hi⟩
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      obtain ⟨_,hx⟩ := mem_iUnion.mp hj
      exact mem_iUnion.mpr ⟨j,hx⟩
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    by_cases hc : ∃ i, choice i=j
    · obtain ⟨i,rfl⟩ := hc
      exact Or.inl (mem_iUnion.mpr ⟨i,hj⟩)
    · apply Or.inr
      exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨(mem_unchosen choice j).mpr (by simpa using hc),hj⟩⟩

theorem complement_disjoint (P : Profile (Fin n)) (pieces : Label → List (Parent n))
    (hv : FamilyValid P pieces) (choice : Fin k → Label) (i : Fin k) :
    Disjoint (material (pieces (choice i))) (material (complement pieces choice)) := by
  rw [complement_material]
  apply disjoint_iUnion_right.mpr
  intro j
  apply disjoint_iUnion_right.mpr
  intro hj
  exact hv.2 ((mem_unchosen choice j).mp hj i)

theorem chosen_disjoint (P : Profile (Fin n)) (pieces : Label → List (Parent n))
    (hv : FamilyValid P pieces) (choice : Fin k → Label) (hinj : Function.Injective choice) :
    Pairwise (fun i j => Disjoint (material (pieces (choice i))) (material (pieces (choice j)))) :=
  fun i j h => hv.2 (fun heq => h (hinj heq))

end EnvyFreeResearch.Full.Chores.Augment
