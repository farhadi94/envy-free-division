import EnvyFreeResearch.Full.ChoresFrontierCache

/-! Prefix and suffix records at an original atom boundary form the exact
original piece. Atom containment is literal set containment and includes
empty atoms, so it applies to arbitrary later physical suffix cuts. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers
open scoped Classical

variable {n : ℕ}

def boundaryPrefix (table : Table n) (p : Fin n) (t : Fin (n+1)) : List (Parent n) :=
  if h : t.val=0 then [] else
    (table (p,markAgent table p ⟨t.val-1,by have ht := t.isLt; omega⟩)).parts.prefixParts

theorem atomMaterial_mono {P : Set ℝ} {as bs : List (Atom n)} (h : as ⊆ bs) :
    atomMaterial P as ⊆ atomMaterial P bs := by
  intro x hx
  obtain ⟨a,ha,hx⟩ := (mem_atomMaterial P as x).mp hx
  exact (mem_atomMaterial P bs x).mpr ⟨a,h ha,hx⟩

theorem atomMaterial_take_mono (P : Set ℝ) (as : List (Atom n)) {s t : ℕ} (hst : s ≤ t) :
    atomMaterial P (as.take s) ⊆ atomMaterial P (as.take t) :=
  atomMaterial_mono (List.take_subset_take_left as hst)

theorem atomMaterial_drop_antitone (P : Set ℝ) (as : List (Atom n)) {s t : ℕ} (hst : s ≤ t) :
    atomMaterial P (as.drop t) ⊆ atomMaterial P (as.drop s) :=
  atomMaterial_mono (List.drop_subset_drop_left as hst)

theorem atom_subset_take (P : Set ℝ) (as : List (Atom n)) (a : Fin as.length) (t : ℕ) (ha : a.val < t) :
    (as.get a).domain P ⊆ atomMaterial P (as.take t) := by
  intro x hx
  apply (mem_atomMaterial P _ x).mpr
  exact ⟨as.get a,List.mem_take_iff_getElem.mpr ⟨a.val,lt_min ha a.isLt,rfl⟩,hx⟩

theorem atom_subset_drop (P : Set ℝ) (as : List (Atom n)) (a : Fin as.length) (t : ℕ) (ha : t ≤ a.val) :
    (as.get a).domain P ⊆ atomMaterial P (as.drop t) := by
  intro x hx
  apply (mem_atomMaterial P _ x).mpr
  refine ⟨as.get a,List.mem_drop_iff_getElem.mpr ⟨a.val-t,by omega,?_⟩,hx⟩
  change as[t+(a.val-t)]=as[a.val]
  congr 1
  omega

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
  (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
  (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
  (hown : (table (p,p)).parts.prefixParts=cache)

include hc hcorrect

theorem boundary_prefix_valid (t : Fin (n+1)) :
    CacheValid (measureProfile cost) (atomMaterial P ((atomsFromTable table p).take t.val))
      (boundaryPrefix table p t) := by
  unfold boundaryPrefix
  split_ifs with ht
  · simp [ht,atomMaterial,CacheValid,Valid,Ordered,material]
  · let j : Fin n := ⟨t.val-1,by have ht' := t.isLt; omega⟩
    have hidx : j.val+1=t.val := by dsimp [j]; omega
    have hj : j.val < (sortedMarks (marksFromTable table p)).length := by
      simpa only [(sorted_marks_perm _).length_eq,marksFromTable,List.length_ofFn] using j.isLt
    have hmark := congrArg Mark.point (markAgent_spec table p j)
    change (table (p,markAgent table p j)).point=(indexedMark table p j).point at hmark
    have hs := (hcorrect (markAgent table p j)).2.1
    have hmat := prefix_material_index cost P cache hc table p baseline hcorrect j.val hj
    change atomMaterial P ((atomsFromTable table p).take (j.val+1))=P ∩ Iic (indexedMark table p j).point at hmat
    rw [hmark,← hmat,hidx] at hs
    exact hs

include hown

theorem boundary_complement (t : Fin (n+1)) :
    material (boundaryCache table p cache t)=P \ material (boundaryPrefix table p t) := by
  obtain ⟨_,hd,hcover,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  rw [boundary_cache_material cost P cache hc table p baseline hcorrect hown,
    (boundary_prefix_valid cost P cache hc table p baseline hcorrect t).2.2,
    atomMaterial_drop P _ hd,hcover]

theorem boundary_prefix_subset (t : Fin (n+1)) : material (boundaryPrefix table p t) ⊆ P := by
  rw [(boundary_prefix_valid cost P cache hc table p baseline hcorrect t).2.2]
  calc
    atomMaterial P ((atomsFromTable table p).take t.val) ⊆ atomMaterial P (atomsFromTable table p) :=
      atomMaterial_mono (List.take_subset _ _)
    _ = P := (original_atom_table cost P cache hc table p baseline hcorrect hown).2.2.1

theorem boundary_suffix_subset (t : Fin (n+1)) : material (boundaryCache table p cache t) ⊆ P := by
  rw [boundary_complement cost P cache hc table p baseline hcorrect hown]
  exact sdiff_subset

theorem original_atom_in_equalizer (a i : Fin n) (ha : a.val < rankOf table p i) :
    ((atomsFromTable table p).get (Fin.cast (atoms_from_table_length table p).symm a)).domain P ⊆
      material (table (p,i)).parts.prefixParts := by
  rw [← prefix_material_rank cost P cache hc table p baseline hcorrect hown i]
  exact atom_subset_take P _ (Fin.cast (atoms_from_table_length table p).symm a) _ ha

theorem original_atom_in_suffix (a : Fin n) :
    ((atomsFromTable table p).get (Fin.cast (atoms_from_table_length table p).symm a)).domain P ⊆
      material (boundaryCache table p cache a.castSucc) := by
  rw [boundary_cache_material cost P cache hc table p baseline hcorrect hown]
  exact atom_subset_drop P _ (Fin.cast (atoms_from_table_length table p).symm a) _ le_rfl

end EnvyFreeResearch.Full.Chores.Frontier
