import EnvyFreeResearch.Full.ChoresCutterProgress

/-!
# Literal allocation and residue of interval Core

The leftmost input endpoint belongs to the cutter's bundle; all other cells
are half-open on the left. Consequently the physical material is partitioned
literally, even when some parent or allocated prefix has zero length.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.IntervalCore

open Set MeasureTheory IntervalOracle PhysicalCore InitialPartition
open scoped BigOperators

def prefixPiece {n : ℕ} (parent : Fin n → Parent n) (s : PhysicalCore.State n n) (p : Fin n) : Set ℝ :=
  Ioc (parent p).left (s.endpoint p).point

def suffixPiece {n : ℕ} (parent : Fin n → Parent n) (s : PhysicalCore.State n n) (p : Fin n) : Set ℝ :=
  Ioc (s.endpoint p).point (parent p).right

def allocated {n : ℕ} (a : ℝ) (c : Fin n) (parent : Fin n → Parent n)
    (s : PhysicalCore.State n n) (i : Fin n) : Set ℝ :=
  prefixPiece parent s (s.matching i) ∪ if i = c then {a} else ∅

def residue {n : ℕ} (parent : Fin n → Parent n) (s : PhysicalCore.State n n) : Set ℝ :=
  ⋃ p, suffixPiece parent s p

lemma prefixPiece_subset {n : ℕ} (parent : Fin n → Parent n) (s : PhysicalCore.State n n)
    (hpoint : ∀ p, (parent p).left ≤ (s.endpoint p).point ∧ (s.endpoint p).point ≤ (parent p).right)
    (p : Fin n) : prefixPiece parent s p ⊆ Ioc (parent p).left (parent p).right :=
  fun _ hx => ⟨hx.1, hx.2.trans (hpoint p).2⟩

lemma suffixPiece_subset {n : ℕ} (parent : Fin n → Parent n) (s : PhysicalCore.State n n)
    (hpoint : ∀ p, (parent p).left ≤ (s.endpoint p).point ∧ (s.endpoint p).point ≤ (parent p).right)
    (p : Fin n) : suffixPiece parent s p ⊆ Ioc (parent p).left (parent p).right :=
  fun _ hx => ⟨(hpoint p).1.trans_lt hx.1, hx.2⟩

theorem prefix_geometry {n : ℕ} (P : Profile (Fin n)) (c : Fin n) (a b : ℝ)
    (hab : a ≤ b) (parent : Fin n → Parent n) (s : PhysicalCore.State n n)
    (hcorrect : Correct P c a b (.prefixes parent s)) :
    Pairwise (fun i j => Disjoint (allocated a c parent s i) (allocated a c parent s j)) ∧
    (∀ i, Disjoint (allocated a c parent s i) (residue parent s)) ∧
    (⋃ i, allocated a c parent s i) ∪ residue parent s = Icc a b := by
  obtain ⟨hbound, _, _, hdisjoint, hcover, hpoint, _, _⟩ := hcorrect
  have hp : ∀ p q, p ≠ q → Disjoint (prefixPiece parent s p) (prefixPiece parent s q) :=
    fun p q h => (hdisjoint h).mono (prefixPiece_subset parent s hpoint p) (prefixPiece_subset parent s hpoint q)
  have hps : ∀ p q, Disjoint (prefixPiece parent s p) (suffixPiece parent s q) := by
    intro p q
    by_cases h : p = q
    · subst q
      exact Ioc_disjoint_Ioc_of_le le_rfl
    · exact (hdisjoint h).mono (prefixPiece_subset parent s hpoint p) (suffixPiece_subset parent s hpoint q)
  have hap : ∀ p, Disjoint ({a} : Set ℝ) (prefixPiece parent s p) := by
    intro p
    apply disjoint_singleton_left.mpr
    intro h
    exact not_lt_of_ge (hbound p).1 h.1
  have has : ∀ p, Disjoint ({a} : Set ℝ) (suffixPiece parent s p) := by
    intro p
    apply disjoint_singleton_left.mpr
    intro h
    exact not_lt_of_ge ((hbound p).1.trans (hpoint p).1) h.1
  have hr : Disjoint ({a} : Set ℝ) (residue parent s) := disjoint_iUnion_right.mpr has
  have hpr : ∀ p, Disjoint (prefixPiece parent s p) (residue parent s) :=
    fun p => disjoint_iUnion_right.mpr (hps p)
  have hallocated : (⋃ i, allocated a c parent s i) = (⋃ p, prefixPiece parent s p) ∪ {a} := by
    have hsingle : (⋃ i : Fin n, if i = c then ({a} : Set ℝ) else ∅) = {a} := by
      apply Subset.antisymm
      · apply iUnion_subset
        intro i
        by_cases hi : i = c <;> simp [hi]
      · simpa only [ite_true] using (subset_iUnion (fun i : Fin n => if i = c then ({a} : Set ℝ) else ∅) c)
    simp only [allocated, iUnion_union_distrib, hsingle]
    rw [s.matching.surjective.iUnion_comp]
  have hsplit : (⋃ p, prefixPiece parent s p) ∪ residue parent s = Ioc a b := by
    rw [residue, ← iUnion_union_distrib]
    convert hcover using 1
    congr 1
    funext p
    exact Ioc_union_Ioc_eq_Ioc (hpoint p).1 (hpoint p).2
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hbase := hp (s.matching i) (s.matching j) (s.matching.injective.ne hij)
    by_cases hi : i = c <;> by_cases hj : j = c
    · exact (hij (hi.trans hj.symm)).elim
    · simp only [allocated, hi, hj, ite_true, ite_false, union_empty]
      exact disjoint_union_left.mpr ⟨by simpa only [hi] using hbase, hap _⟩
    · simp only [allocated, hi, hj, ite_true, ite_false, union_empty]
      exact disjoint_union_right.mpr ⟨by simpa only [hj] using hbase, (hap _).symm⟩
    · simpa only [allocated, hi, hj, ite_false, union_empty] using hbase
  · intro i
    by_cases hi : i = c
    · simpa only [allocated, hi, ite_true, disjoint_union_left] using And.intro (hpr (s.matching i)) hr
    · simpa only [allocated, hi, ite_false, union_empty] using hpr (s.matching i)
  · rw [hallocated]
    calc
      ((⋃ p, prefixPiece parent s p) ∪ {a}) ∪ residue parent s =
          {a} ∪ ((⋃ p, prefixPiece parent s p) ∪ residue parent s) := by ac_rfl
      _ = {a} ∪ Ioc a b := by rw [hsplit]
      _ = Icc a b := by
        ext x
        simp only [mem_union, mem_singleton_iff, mem_Ioc, mem_Icc]
        constructor
        · rintro (rfl | ⟨hx, hxb⟩)
          · exact ⟨le_rfl, hab⟩
          · exact ⟨le_of_lt hx, hxb⟩
        · rintro ⟨hax, hxb⟩
          rcases eq_or_lt_of_le hax with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨h, hxb⟩

theorem suffixes_disjoint {n : ℕ} (P : Profile (Fin n)) (c : Fin n) (a b : ℝ)
    (parent : Fin n → Parent n) (s : PhysicalCore.State n n)
    (hcorrect : Correct P c a b (.prefixes parent s)) :
    Pairwise (fun p q => Disjoint (suffixPiece parent s p) (suffixPiece parent s q)) := by
  intro p q hpq
  exact (hcorrect.2.2.2.1 hpq).mono (suffixPiece_subset parent s hcorrect.2.2.2.2.2.1 p)
    (suffixPiece_subset parent s hcorrect.2.2.2.2.2.1 q)

theorem allocated_value {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (a b : ℝ) (ha : 0 ≤ a) (parent : Fin n → Parent n)
    (s : PhysicalCore.State n n) (hcorrect : Correct (measureProfile cost) c a b (.prefixes parent s)) :
    ∀ i j, (cost i).real (allocated a c parent s j) =
      prefixValue (measureProfile cost) (parentFrame parent) s i (s.matching j) := by
  obtain ⟨hbound, _, _, _, _, hpoint, _, _⟩ := hcorrect
  intro i j
  have hbase : (cost i).real (prefixPiece parent s (s.matching j)) =
      prefixValue (measureProfile cost) (parentFrame parent) s i (s.matching j) :=
    (prefix_difference_eq_interval (cost i) (ha.trans (hbound _).1) (hpoint _).1).symm
  have hsingle : Disjoint (prefixPiece parent s (s.matching j)) ({a} : Set ℝ) := by
    apply disjoint_singleton_right.mpr
    intro h
    exact not_lt_of_ge (hbound _).1 h.1
  by_cases hj : j = c
  · rw [allocated, ite_eq_left hj, measureReal_union hsingle (measurableSet_singleton a)]
    simpa only [measureReal_def, measure_singleton, ENNReal.toReal_zero, add_zero] using hbase
  · simpa only [allocated, ite_eq_right hj, union_empty] using hbase

theorem residue_value {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (a b : ℝ) (ha : 0 ≤ a) (parent : Fin n → Parent n)
    (s : PhysicalCore.State n n) (hcorrect : Correct (measureProfile cost) c a b (.prefixes parent s)) :
    ∀ i, (cost i).real (residue parent s) = residueValue (measureProfile cost) parent s i := by
  intro i
  rw [residue, measureReal_iUnion_fintype (suffixes_disjoint (measureProfile cost) c a b parent s hcorrect)
    (fun _ => measurableSet_Ioc)]
  apply Finset.sum_congr rfl
  intro p _
  exact (prefix_difference_eq_interval (cost i)
    ((ha.trans (hcorrect.1 p).1).trans (hcorrect.2.2.2.2.2.1 p).1)
    (hcorrect.2.2.2.2.2.1 p).2).symm

theorem input_value {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (i : Fin n) :
    (cost i).real (Icc a b) = (measureProfile cost).cumulative i b - (measureProfile cost).cumulative i a := by
  have hsplit := physical_split_cost (cost i) (le_refl a) hab
  have heq : (cost i).real (Icc a b) = (cost i).real (Ioc a b) := by
    simpa only [Icc_self, measureReal_def, measure_singleton, ENNReal.toReal_zero, zero_add] using hsplit.symm
  rw [heq]
  exact (prefix_difference_eq_interval (cost i) ha hab).symm

/-- The interval Core's prefix alternative is a literal partial allocation,
is exactly chore EF for the original atomless measures, and has both required
cutter-progress estimates. All values refer to actual returned physical sets. -/
theorem measured_prefix_correct {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1)
    (parent : Fin n → Parent n) (s : PhysicalCore.State n n)
    (hcorrect : Correct (measureProfile cost) c a b (.prefixes parent s)) :
    Pairwise (fun i j => Disjoint (allocated a c parent s i) (allocated a c parent s j)) ∧
    (∀ i, Disjoint (allocated a c parent s i) (residue parent s)) ∧
    (⋃ i, allocated a c parent s i) ∪ residue parent s = Icc a b ∧
    (∀ i j, (cost i).real (allocated a c parent s i) ≤ (cost i).real (allocated a c parent s j)) ∧
    (cost c).real (residue parent s) ≤ ((n - 1 : ℕ) : ℝ) / n * (cost c).real (Icc a b) ∧
    ∃ j, (s.endpoint (s.matching j)).point = (parent (s.matching j)).right ∧
      (cost c).real (residue parent s) / (n - 1 : ℕ) ≤
        (cost c).real (allocated a c parent s j) - (cost c).real (allocated a c parent s c) := by
  obtain ⟨hd, hdr, hu⟩ := prefix_geometry (measureProfile cost) c a b hbound.2.1 parent s hcorrect
  have hmono : ∀ i, Monotone ((measureProfile cost).cumulative i) := fun i => prefixCost_monotone (cost i) 0
  obtain ⟨_, hshrink, j, hj, hgap⟩ := cutter_progress hn (measureProfile cost) hmono c a b parent s hcorrect
  refine ⟨hd, hdr, hu, ?_, ?_, j, hj, ?_⟩
  · intro i j
    rw [allocated_value cost c a b hbound.1 parent s hcorrect i i,
      allocated_value cost c a b hbound.1 parent s hcorrect i j]
    exact hcorrect.2.2.2.2.2.2.1 i (s.matching j)
  · rw [residue_value cost c a b hbound.1 parent s hcorrect c,
      input_value cost a b hbound.1 hbound.2.1 c]
    exact hshrink
  · rw [residue_value cost c a b hbound.1 parent s hcorrect c,
      allocated_value cost c a b hbound.1 parent s hcorrect c j,
      allocated_value cost c a b hbound.1 parent s hcorrect c c]
    exact hgap

def outputAllocation {n : ℕ} (a b : ℝ) (c : Fin n) : Outcome n → Fin n → Set ℝ
  | .zero z => fun i => if i = z then Icc a b else ∅
  | .prefixes parent s => allocated a c parent s

def outputResidue {n : ℕ} : Outcome n → Set ℝ
  | .zero _ => ∅
  | .prefixes parent s => residue parent s

def MeasuredCorrect {n : ℕ} (cost : Fin n → Measure ℝ) (c : Fin n) (a b : ℝ) (out : Outcome n) : Prop :=
  Pairwise (fun i j => Disjoint (outputAllocation a b c out i) (outputAllocation a b c out j)) ∧
  (∀ i, Disjoint (outputAllocation a b c out i) (outputResidue out)) ∧
  (⋃ i, outputAllocation a b c out i) ∪ outputResidue out = Icc a b ∧
  (∀ i j, (cost i).real (outputAllocation a b c out i) ≤ (cost i).real (outputAllocation a b c out j)) ∧
  (cost c).real (outputResidue out) ≤ ((n - 1 : ℕ) : ℝ) / n * (cost c).real (Icc a b) ∧
  ∃ j, (cost c).real (outputResidue out) / (n - 1 : ℕ) ≤
    (cost c).real (outputAllocation a b c out j) - (cost c).real (outputAllocation a b c out c)

theorem measured_correct {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1) (out : Outcome n)
    (hcorrect : Correct (measureProfile cost) c a b out) : MeasuredCorrect cost c a b out := by
  cases out with
  | prefixes parent s =>
    obtain ⟨hd, hdr, hu, hEF, hshrink, j, _, hgap⟩ :=
      measured_prefix_correct hn cost c a b hbound parent s hcorrect
    exact ⟨hd, hdr, hu, hEF, hshrink, j, hgap⟩
  | zero z =>
    have hz : (cost z).real (Icc a b) = 0 := by
      rw [input_value cost a b hbound.1 hbound.2.1 z]
      exact hcorrect
    refine ⟨?_, ?_, ?_, ?_, ?_, c, ?_⟩
    · intro i j hij
      by_cases hi : i = z <;> by_cases hj : j = z
      · exact (hij (hi.trans hj.symm)).elim
      · simp [outputAllocation, hi, hj]
      · simp [outputAllocation, hi, hj]
      · simp [outputAllocation, hi, hj]
    · intro i
      exact disjoint_empty _
    · simp only [outputResidue, union_empty, outputAllocation]
      apply Subset.antisymm
      · apply iUnion_subset
        intro i
        by_cases hi : i = z <;> simp [hi]
      · simpa only [ite_true] using (subset_iUnion (fun i : Fin n => if i = z then Icc a b else ∅) z)
    · intro i j
      by_cases hi : i = z
      · subst i
        by_cases hj : j = z <;> simp [outputAllocation, hj, hz]
      · simp only [outputAllocation, ite_eq_right hi, measureReal_empty]
        exact measureReal_nonneg
    · exact le_trans (by simp [outputResidue]) (mul_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) measureReal_nonneg)
    · simp only [outputResidue, measureReal_empty, zero_div, sub_self, le_refl]

/-- The actual interval Core endpoint for finite atomless Borel costs: its
returned physical sets are disjoint, exhaustive with their literal residue,
exactly EF, and satisfy both progress inequalities within the full ledger.
The residue may be nonempty; this is the Core primitive, not theorem 2.1. -/
theorem interval_core_measures {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1) :
    ∃ out : Outcome n, ∃ trace : OracleProtocol.History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (coreProgram c a b).protocol oracle () (queryBudget n) [] =
        ⟨trace, .returned out⟩ ∧ trace.length ≤ queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ n - 1 + trimBudget n ∧
      MeasuredCorrect cost c a b out ∧ Cached (measureProfile cost) out := by
  have hmono : ∀ i, Monotone ((measureProfile cost).cumulative i) := fun i => prefixCost_monotone (cost i) 0
  obtain ⟨out, trace, hrun, hlen, hcuts, hcorrect, hcached⟩ :=
    core_program_correct_cached (measureProfile cost) hmono oracle hpolicy c a b hbound
  exact ⟨out, trace, hrun, hlen, hcuts, measured_correct hn cost c a b hbound out hcorrect, hcached⟩

end EnvyFreeResearch.Full.Chores.IntervalCore
