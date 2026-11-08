import EnvyFreeResearch.Full.ChoresOriginalAtoms

/-! Original atom tables are computed from the actual recorded equalizers.
All marks, including ties and zero marks, participate in the sort. There
are exactly n atom records (some may be empty), with exact original costs
and a literal disjoint cover of the original share. No oracle calls occur. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OriginalAtoms
open Set MeasureTheory OrderedUnion InitialPartition Equalizers
open scoped Classical

variable {n : ℕ}

def emptyMark (n : ℕ) : Mark n := ⟨0,fun _ => 0⟩

def marksFromTable (table : Table n) (p : Fin n) : List (Mark n) :=
  List.ofFn (fun i => ⟨(table (p,i)).point,(table (p,i)).values⟩)

def atomsFromTable (table : Table n) (p : Fin n) : List (Atom n) :=
  fromMarks (emptyMark n) (sortedMarks (marksFromTable table p))

theorem atoms_from_table_length (table : Table n) (p : Fin n) :
    (atomsFromTable table p).length = n := by
  rw [atomsFromTable,fromMarks_length,(sorted_marks_perm _).length_eq]
  exact List.length_ofFn

theorem empty_mark_sound (cost : Fin n → Measure ℝ) (P : Set ℝ) (hP : P ⊆ Ioc (0 : ℝ) 1) :
    (emptyMark n).Sound cost P := by
  refine ⟨by norm_num [emptyMark],?_⟩
  intro i
  have hset : P ∩ Iic 0 = ∅ := by
    apply Set.eq_empty_of_subset_empty
    intro x hx
    exact (not_lt_of_ge hx.2 (hP hx.1).1).elim
  simp only [emptyMark,hset,measureReal_empty]

theorem original_atom_table (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
    (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
    (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
    (hown : (table (p,p)).parts.prefixParts = cache) :
    (∀ atom ∈ atomsFromTable table p, atom.Sound cost P) ∧
      (atomsFromTable table p).Pairwise (fun a b => Disjoint (a.domain P) (b.domain P)) ∧
      atomMaterial P (atomsFromTable table p) = P ∧ (atomsFromTable table p).length = n := by
  have hP : MeasurableSet P := by rw [← hc.2.2]; exact material_measurable _
  have hbound := cache_domain_subset (measureProfile cost) P cache hc
  have hmarks : ∀ r ∈ sortedMarks (marksFromTable table p), r.Sound cost P := by
    intro r hr
    have hm : r ∈ marksFromTable table p := (sorted_marks_perm _).mem_iff.mp hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
    exact ⟨(hcorrect i).1,(hcorrect i).2.2.2.2⟩
  have horder := sorted_marks_order (marksFromTable table p)
  have hlower : ∀ r ∈ sortedMarks (marksFromTable table p), (emptyMark n).point ≤ r.point :=
    fun r hr => (hmarks r hr).1.1
  refine ⟨fromMarks_sound cost P hP (emptyMark n) _ (empty_mark_sound cost P hbound)
    hmarks horder hlower,fromMarks_disjoint P (emptyMark n) _ horder hlower,?_,
    atoms_from_table_length table p⟩
  rw [atomsFromTable,fromMarks_cover P (emptyMark n) _ horder hlower]
  have hownMem : (⟨(table (p,p)).point,(table (p,p)).values⟩ : Mark n) ∈
      sortedMarks (marksFromTable table p) := by
    apply (sorted_marks_perm _).mem_iff.mpr
    exact List.mem_ofFn.mpr ⟨p,rfl⟩
  have hlast := mem_le_lastPoint (emptyMark n) _ horder _ hownMem
  have hmat := (hcorrect p).2.1.2.2
  rw [hown,hc.2.2] at hmat
  apply inter_eq_left.mpr
  intro x hx
  have hpref : x ∈ P ∩ Iic (table (p,p)).point := hmat ▸ hx
  exact ⟨(hbound hx).1,hpref.2.trans hlast⟩

end EnvyFreeResearch.Full.Chores.OriginalAtoms
