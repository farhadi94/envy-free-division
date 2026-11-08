import EnvyFreeResearch.Full.ChoresFrontierMeasures

/-! The rank adapter preserves literal material, not only its costs.
Initial and terminal zero atoms and coincident original marks stay in the
chain, and every ranked equalizer has its exact original physical cache. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers
open scoped Classical

variable {n : ℕ}

theorem fromMarks_take (previous : Mark n) (marks : List (Mark n)) (k : ℕ) :
    (fromMarks previous marks).take k=fromMarks previous (marks.take k) := by
  induction k generalizing previous marks with
  | zero => simp [fromMarks]
  | succ k ih =>
    cases marks with
    | nil => simp [fromMarks]
    | cons current rest => simp only [fromMarks,List.take_succ_cons,ih]

theorem lastPoint_take (previous : Mark n) (marks : List (Mark n)) (j : ℕ) (hj : j < marks.length) :
    lastPoint previous (marks.take (j+1))=(marks.get ⟨j,hj⟩).point := by
  induction marks generalizing previous j with
  | nil => simp at hj
  | cons current rest ih =>
    cases j with
    | zero => simp [lastPoint]
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      simpa only [List.take_succ_cons,lastPoint,List.get_cons_succ] using ih current j hj'

theorem atomMaterial_append (P : Set ℝ) (as bs : List (Atom n)) :
    atomMaterial P (as++bs)=atomMaterial P as ∪ atomMaterial P bs := by
  induction as with
  | nil => simp [atomMaterial]
  | cons a as ih => simp only [List.cons_append,atomMaterial,ih,union_assoc]

theorem atomMaterial_disjoint (P : Set ℝ) (as bs : List (Atom n))
    (hd : ∀ a ∈ as, ∀ b ∈ bs, Disjoint (a.domain P) (b.domain P)) :
    Disjoint (atomMaterial P as) (atomMaterial P bs) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,hx⟩ := (mem_atomMaterial P as x).mp hx
  obtain ⟨b,hb,hy⟩ := (mem_atomMaterial P bs x).mp hy
  exact disjoint_left.mp (hd a ha b hb) hx hy

theorem atomMaterial_drop (P : Set ℝ) (atoms : List (Atom n))
    (hd : atoms.Pairwise (fun a b => Disjoint (a.domain P) (b.domain P))) (k : ℕ) :
    atomMaterial P (atoms.drop k)=atomMaterial P atoms \ atomMaterial P (atoms.take k) := by
  have hsplit : atomMaterial P (atoms.take k) ∪ atomMaterial P (atoms.drop k)=atomMaterial P atoms := by
    rw [← atomMaterial_append,List.take_append_drop]
  have hd' : ((atoms.take k)++atoms.drop k).Pairwise (fun a b => Disjoint (a.domain P) (b.domain P)) := by
    simpa only [List.take_append_drop] using hd
  have hdis := atomMaterial_disjoint P _ _ (List.pairwise_append.mp hd').2.2
  ext x
  constructor
  · intro hx
    exact ⟨hsplit ▸ Or.inr hx,fun hy => disjoint_left.mp hdis hy hx⟩
  · rintro ⟨hx,hn⟩
    rw [← hsplit] at hx
    exact hx.resolve_left hn

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
  (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
  (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
  (hown : (table (p,p)).parts.prefixParts=cache)

include hc hcorrect

theorem prefix_material_index (j : ℕ)
    (hj : j < (sortedMarks (marksFromTable table p)).length) :
    atomMaterial P ((atomsFromTable table p).take (j+1))=
      P ∩ Iic ((sortedMarks (marksFromTable table p)).get ⟨j,hj⟩).point := by
  let marks := sortedMarks (marksFromTable table p)
  have hmarks : ∀ r ∈ marks, 0 ≤ r.point := by
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ((sorted_marks_perm _).mem_iff.mp hr)
    exact (hcorrect i).1.1
  have horder : marks.Pairwise beforeMark := sorted_marks_order _
  have hlower : ∀ r ∈ marks.take (j+1), (emptyMark n).point ≤ r.point :=
    fun r hr => hmarks r (List.mem_of_mem_take hr)
  have h := fromMarks_cover P (emptyMark n) (marks.take (j+1)) horder.take hlower
  rw [lastPoint_take (emptyMark n) marks j hj] at h
  change atomMaterial P ((fromMarks (emptyMark n) marks).take (j+1))= _
  rw [fromMarks_take,h]
  have hP := cache_domain_subset (measureProfile cost) P cache hc
  ext x
  constructor
  · rintro ⟨hx,hx0,hxpoint⟩
    exact ⟨hx,hxpoint⟩
  · rintro ⟨hx,hxpoint⟩
    exact ⟨hx,(hP hx).1,hxpoint⟩

theorem prefix_material_rawRank (i : Fin n) :
    atomMaterial P ((atomsFromTable table p).take (rawRank table p i))=material (table (p,i)).parts.prefixParts := by
  let marks := sortedMarks (marksFromTable table p)
  have hm : originalMark table p i ∈ marks := original_mark_mem table p i
  have hj : marks.idxOf (originalMark table p i) < marks.length := List.idxOf_lt_length_iff.mpr hm
  have h := prefix_material_index cost P cache hc table p baseline hcorrect (marks.idxOf (originalMark table p i)) hj
  have hget : marks.get ⟨marks.idxOf (originalMark table p i),hj⟩=originalMark table p i := List.getElem_idxOf hj
  change atomMaterial P ((atomsFromTable table p).take (rawRank table p i))=P ∩ Iic (marks.get _).point at h
  rw [hget] at h
  exact h.trans (hcorrect i).2.1.2.2.symm

include hown

theorem prefix_material_rank (i : Fin n) :
    atomMaterial P ((atomsFromTable table p).take (rankOf table p i))=material (table (p,i)).parts.prefixParts := by
  by_cases hi : i=p
  · subst i
    have ht : (atomsFromTable table p).take n=atomsFromTable table p :=
      List.take_of_length_le (by rw [atoms_from_table_length])
    rw [rank_owner,ht,hown,hc.2.2]
    exact (original_atom_table cost P cache hc table p baseline hcorrect hown).2.2.1
  · simpa only [rankOf,ite_eq_right hi] using prefix_material_rawRank cost P cache hc table p baseline hcorrect i

theorem suffix_material_rank (i : Fin n) :
    atomMaterial P ((atomsFromTable table p).drop (rankOf table p i))=material (table (p,i)).parts.suffixParts := by
  obtain ⟨hs,hd,hcover,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  rw [atomMaterial_drop P _ hd,hcover,prefix_material_rank cost P cache hc table p baseline hcorrect hown i,
    (hcorrect i).2.1.2.2,(hcorrect i).2.2.1.2.2]
  ext x
  constructor
  · rintro ⟨hx,hn⟩
    refine ⟨hx, ?_⟩
    change (table (p,i)).point < x
    exact lt_of_not_ge (fun h => hn ⟨hx,h⟩)
  · rintro ⟨hx,hp⟩
    change (table (p,i)).point < x at hp
    exact ⟨hx,fun h => not_lt_of_ge h.2 hp⟩

end EnvyFreeResearch.Full.Chores.Frontier
