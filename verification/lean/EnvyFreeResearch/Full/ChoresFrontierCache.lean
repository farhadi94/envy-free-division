import EnvyFreeResearch.Full.ChoresFrontierGeometry

/-! Every atom boundary has a physical suffix cache already present in the
original equalizer table. Selecting it is finite computation on that table;
no new Eval or Cut query is used, including at zero and coincident marks. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers
open scoped Classical

variable {n : ℕ}

def indexedMark (table : Table n) (p : Fin n) (j : Fin n) : Mark n :=
  (sortedMarks (marksFromTable table p)).get
    (Fin.cast (by simpa only [(sorted_marks_perm _).length_eq,List.length_ofFn,marksFromTable]) j)

theorem indexedMark_exists (table : Table n) (p : Fin n) (j : Fin n) :
    ∃ i : Fin n, originalMark table p i=indexedMark table p j := by
  have hm : indexedMark table p j ∈ sortedMarks (marksFromTable table p) := List.get_mem _ _
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp ((sorted_marks_perm _).mem_iff.mp hm)
  exact ⟨i,hi⟩

def markAgent (table : Table n) (p : Fin n) (j : Fin n) : Fin n :=
  (indexedMark_exists table p j).choose

theorem markAgent_spec (table : Table n) (p : Fin n) (j : Fin n) :
    originalMark table p (markAgent table p j)=indexedMark table p j :=
  (indexedMark_exists table p j).choose_spec

def boundaryCache (table : Table n) (p : Fin n) (original : List (Parent n))
    (t : Fin (n+1)) : List (Parent n) :=
  if h : t.val=0 then original else
    (table (p,markAgent table p ⟨t.val-1,by have ht := t.isLt; omega⟩)).parts.suffixParts

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
  (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
  (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
  (hown : (table (p,p)).parts.prefixParts=cache)

include hc hcorrect hown

theorem suffix_material_index (j : Fin n) :
    atomMaterial P ((atomsFromTable table p).drop (j.val+1))=
      P ∩ Ioi (indexedMark table p j).point := by
  obtain ⟨hs,hd,hcover,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  have hj : j.val < (sortedMarks (marksFromTable table p)).length := by
    simpa only [(sorted_marks_perm _).length_eq,marksFromTable,List.length_ofFn] using j.isLt
  rw [atomMaterial_drop P _ hd,hcover,
    prefix_material_index cost P cache hc table p baseline hcorrect j.val hj]
  change P \ (P ∩ Iic (indexedMark table p j).point)=P ∩ Ioi (indexedMark table p j).point
  ext x
  constructor
  · rintro ⟨hx,hn⟩
    refine ⟨hx,?_⟩
    change (indexedMark table p j).point < x
    exact lt_of_not_ge (fun h => hn ⟨hx,h⟩)
  · rintro ⟨hx,hp⟩
    change (indexedMark table p j).point < x at hp
    exact ⟨hx,fun h => not_lt_of_ge h.2 hp⟩

theorem boundary_cache_valid (t : Fin (n+1)) :
    CacheValid (measureProfile cost) (atomMaterial P ((atomsFromTable table p).drop t.val))
      (boundaryCache table p cache t) := by
  unfold boundaryCache
  split_ifs with ht
  · simpa only [ht,List.drop_zero,
      (original_atom_table cost P cache hc table p baseline hcorrect hown).2.2.1] using hc
  · let j : Fin n := ⟨t.val-1,by have ht' := t.isLt; omega⟩
    have hidx : j.val+1=t.val := by dsimp [j]; omega
    have hmark := congrArg Mark.point (markAgent_spec table p j)
    change (table (p,markAgent table p j)).point=(indexedMark table p j).point at hmark
    have hs := (hcorrect (markAgent table p j)).2.2.1
    rw [hmark,← suffix_material_index cost P cache hc table p baseline hcorrect hown j,hidx] at hs
    exact hs

theorem boundary_cache_material (t : Fin (n+1)) :
    material (boundaryCache table p cache t)=atomMaterial P ((atomsFromTable table p).drop t.val) :=
  (boundary_cache_valid cost P cache hc table p baseline hcorrect hown t).2.2

theorem boundary_cache_value (t : Fin (n+1)) (i : Fin n) :
    cachedValue (boundaryCache table p cache t) i=tailCost (weight table p) i t.val := by
  have hcache := boundary_cache_valid cost P cache hc table p baseline hcorrect hown t
  rw [← material_value cost _ hcache.1 hcache.2.1,hcache.2.2,weight_tail_sum]
  obtain ⟨hs,hd,_,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  have hP : MeasurableSet P := by rw [← hc.2.2]; exact material_measurable _
  exact atomMaterial_value cost P hP _ (fun a ha => hs a (List.mem_of_mem_drop ha)) hd.drop i

end EnvyFreeResearch.Full.Chores.Frontier
