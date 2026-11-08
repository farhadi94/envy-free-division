import EnvyFreeResearch.Full.ChoresFrontierRanks

/-! The finite frontier rows are the actual costs of original atom sets.
Their suffix sums equal original equalizer gaps, including the owner's
whole-piece boundary and all coincident/zero marks. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers
open scoped Classical BigOperators

variable {n : ℕ}

theorem mem_atomMaterial (P : Set ℝ) (atoms : List (Atom n)) (x : ℝ) :
    x ∈ atomMaterial P atoms ↔ ∃ a ∈ atoms, x ∈ a.domain P := by
  induction atoms with
  | nil => simp [atomMaterial]
  | cons a atoms ih => simp [atomMaterial,ih]

theorem atomMaterial_measurable (P : Set ℝ) (hP : MeasurableSet P) (atoms : List (Atom n)) :
    MeasurableSet (atomMaterial P atoms) := by
  induction atoms with
  | nil => exact MeasurableSet.empty
  | cons a atoms ih => exact (hP.inter measurableSet_Ioc).union ih

theorem atomMaterial_value (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (P : Set ℝ) (hP : MeasurableSet P) (atoms : List (Atom n))
    (hs : ∀ a ∈ atoms, a.Sound cost P)
    (hd : atoms.Pairwise (fun a b => Disjoint (a.domain P) (b.domain P))) (i : Fin n) :
    (cost i).real (atomMaterial P atoms)=(atoms.map (fun a => a.values i)).sum := by
  induction atoms with
  | nil => simp [atomMaterial]
  | cons a atoms ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hd
    have hdis : Disjoint (a.domain P) (atomMaterial P atoms) := by
      apply disjoint_left.mpr
      intro x hx hy
      obtain ⟨b,hb,hy⟩ := (mem_atomMaterial P atoms x).mp hy
      exact disjoint_left.mp (hhead b hb) hx hy
    rw [atomMaterial,measureReal_union hdis (atomMaterial_measurable P hP atoms),
      ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) htail,
      ← (hs a List.mem_cons_self).2 i]
    rfl

def weight (table : Table n) (p : Fin n) (i a : Fin n) : ℝ :=
  ((atomsFromTable table p).get (Fin.cast (atoms_from_table_length table p).symm a)).values i

theorem weight_tail_sum (table : Table n) (p i : Fin n) (t : ℕ) :
    tailCost (weight table p) i t=
      (((atomsFromTable table p).drop t).map (fun a => a.values i)).sum := by
  let atoms := atomsFromTable table p
  let e : Fin n ≃ Fin atoms.length := finCongr (atoms_from_table_length table p).symm
  have h : tailCost (weight table p) i t=
      ∑ a : Fin atoms.length, if t ≤ a.val then (atoms.get a).values i else 0 := by
    apply Fintype.sum_equiv e
    intro a
    rfl
  exact h.trans (indexed_tail_sum atoms (fun a => a.values i) t)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (P : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) P cache)
  (table : Table n) (p : Fin n) (baseline : Fin n → ℝ)
  (hcorrect : ∀ i, Equalizers.Correct cost P baseline i (table (p,i)))
  (hown : (table (p,p)).parts.prefixParts=cache)

include hc hcorrect hown

theorem original_atom_sum (i : Fin n) :
    ((atomsFromTable table p).map (fun a => a.values i)).sum=(cost i).real P := by
  obtain ⟨hs,hd,hcover,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  have hP : MeasurableSet P := by rw [← hc.2.2]; exact material_measurable _
  have hv := atomMaterial_value cost P hP _ hs hd i
  rw [hcover] at hv
  exact hv.symm

theorem own_baseline : baseline p=(cost p).real P := by
  have hset := (hcorrect p).2.1.2.2
  rw [hown,hc.2.2] at hset
  have h := (hcorrect p).2.2.2.1
  rw [← hset] at h
  exact h.symm

theorem prefix_sum_rank (i : Fin n) :
    (((atomsFromTable table p).take (rankOf table p i)).map (fun a => a.values i)).sum=baseline i := by
  by_cases hi : i=p
  · subst i
    have ht : (atomsFromTable table p).take n=atomsFromTable table p :=
      List.take_of_length_le (by rw [atoms_from_table_length])
    rw [rank_owner,ht]
    exact (original_atom_sum cost P cache hc table p baseline hcorrect hown p).trans
      (own_baseline cost P cache hc table p baseline hcorrect hown).symm
  · rw [rankOf,if_neg hi,prefix_sum_rawRank]
    exact ((hcorrect i).2.2.2.2 i).trans (hcorrect i).2.2.2.1

theorem gap_is_tail (i : Fin n) :
    tailCost (weight table p) i (rankOf table p i)=(cost i).real P-baseline i := by
  rw [weight_tail_sum]
  have hsum := congrArg (fun atoms : List (Atom n) => (atoms.map (fun a => a.values i)).sum)
    (List.take_append_drop (rankOf table p i) (atomsFromTable table p))
  simp only [List.map_append,List.sum_append] at hsum
  rw [prefix_sum_rank cost P cache hc table p baseline hcorrect hown i,
    original_atom_sum cost P cache hc table p baseline hcorrect hown i] at hsum
  linarith

theorem weight_nonnegative (i a : Fin n) : 0 ≤ weight table p i a := by
  obtain ⟨hs,_,_,_⟩ := original_atom_table cost P cache hc table p baseline hcorrect hown
  have h := hs _ (List.get_mem _ (Fin.cast (atoms_from_table_length table p).symm a))
  change 0 ≤ ((atomsFromTable table p).get _).values i
  rw [h.2 i]
  exact measureReal_nonneg

end EnvyFreeResearch.Full.Chores.Frontier
