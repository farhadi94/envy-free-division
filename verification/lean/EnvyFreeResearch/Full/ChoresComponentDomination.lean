import EnvyFreeResearch.Full.ChoresCompletionZero
import EnvyFreeResearch.Full.ChoresComponentActiveRestore

/-! Unary recursive completion for the exhausted branch. The proper child
population receives the whole residue; original whole-domain margins protect
all inactive recipients. The final physical join makes no oracle call. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

variable {n k : ℕ}

def extend (agent : Fin k ↪ Fin n) (child : Allocation n (Fin k)) : Allocation n (Fin n) :=
  ⟨fun i => if h : ∃ a, agent a = i then child.pieces (Classical.choose h) else []⟩

@[simp] theorem extend_at (agent : Fin k ↪ Fin n) (child : Allocation n (Fin k)) (i : Fin k) :
    (extend agent child).pieces (agent i) = child.pieces i := by
  have h : ∃ a, agent a = agent i := ⟨i, rfl⟩
  simp only [extend, dite_eq_left h]
  rw [agent.injective (Classical.choose_spec h)]

theorem extend_outside (agent : Fin k ↪ Fin n) (child : Allocation n (Fin k)) (i : Fin n)
    (hi : i ∉ Set.range agent) : (extend agent child).pieces i = [] := by
  exact dite_eq_right hi

theorem extend_subsets (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k ↪ Fin n) (R : Set ℝ) (child : Allocation n (Fin k))
    (hc : child.Sound cost agent R) (i : Fin n) : material ((extend agent child).pieces i) ⊆ R := by
  by_cases hi : i ∈ Set.range agent
  · obtain ⟨a, rfl⟩ := hi
    rw [extend_at]
    exact hc.subset cost agent R child a
  · rw [extend_outside agent child i hi]
    exact empty_subset _

theorem extend_cache (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k ↪ Fin n) (R : Set ℝ) (child : Allocation n (Fin k))
    (hc : child.Sound cost agent R) (i : Fin n) :
    CacheValid (measureProfile cost) (material ((extend agent child).pieces i)) ((extend agent child).pieces i) := by
  by_cases hi : i ∈ Set.range agent
  · obtain ⟨a, rfl⟩ := hi
    simpa only [extend_at] using hc.cache a
  · rw [extend_outside agent child i hi]
    exact empty_cache_valid _

theorem extend_disjoint (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k ↪ Fin n) (R : Set ℝ) (child : Allocation n (Fin k))
    (hc : child.Sound cost agent R) :
    Pairwise (fun i j => Disjoint (material ((extend agent child).pieces i))
      (material ((extend agent child).pieces j))) := by
  intro i j hij
  by_cases hi : i ∈ Set.range agent
  · obtain ⟨a, rfl⟩ := hi
    by_cases hj : j ∈ Set.range agent
    · obtain ⟨b, rfl⟩ := hj
      rw [extend_at, extend_at]
      exact hc.disjoint (fun hab => hij (congrArg agent hab))
    · rw [extend_outside agent child j hj]
      exact disjoint_empty _
  · rw [extend_outside agent child i hi]
    exact empty_disjoint _

theorem extend_cover (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k ↪ Fin n) (R : Set ℝ) (child : Allocation n (Fin k))
    (hc : child.Sound cost agent R) :
    (⋃ i, material ((extend agent child).pieces i)) = R := by
  apply subset_antisymm
  · exact iUnion_subset (extend_subsets cost agent R child hc)
  · rw [← hc.cover]
    apply iUnion_subset
    intro i
    rw [← extend_at agent child i]
    exact subset_iUnion (fun j : Fin n => material ((extend agent child).pieces j)) (agent i)

def finishDomination (base : Allocation n (Fin n)) (agent : Fin k ↪ Fin n)
    (child : Allocation n (Fin k)) : Allocation n (Fin n) := base.join (extend agent child)

theorem finish_domination_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k ↪ Fin n) (U R : Set ℝ) (base : Allocation n (Fin n))
    (hbase : base.Sound cost id U) (hd : Disjoint U R)
    (hmargin : ∀ (i : Fin k) (j : Fin n), j ∉ Set.range agent →
      (cost (agent i)).real R ≤ (cost (agent i)).real (material (base.pieces j)) -
        (cost (agent i)).real (material (base.pieces (agent i))))
    (child : Allocation n (Fin k)) (hc : child.Sound cost agent R) :
    (finishDomination base agent child).Sound cost id (U ∪ R) := by
  let added := extend agent child
  have hcross (i j : Fin n) : Disjoint (material (base.pieces i)) (material (added.pieces j)) :=
    hd.mono (hbase.subset cost id U base i) (extend_subsets cost agent R child hc j)
  have hvalue (i observer : Fin n) :
      (cost observer).real (material ((finishDomination base agent child).pieces i)) =
        (cost observer).real (material (base.pieces i)) + (cost observer).real (material (added.pieces i)) := by
    rw [finishDomination, Allocation.join_material]
    exact measureReal_union (hcross i i) (material_measurable _)
  constructor
  · intro i
    have ha := extend_cache cost agent R child hc i
    have hh := Augment.assemble_join (measureProfile cost) (base.pieces i) (added.pieces i)
      (hbase.cache i).1 ha.1 (hbase.cache i).2.1 ha.2.1 (hcross i i)
    exact ⟨hh.1, hh.2.1, rfl⟩
  · intro i j hij
    rw [finishDomination, Allocation.join_material, Allocation.join_material]
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hbase.disjoint hij, hcross i j⟩,
      disjoint_union_right.mpr ⟨(hcross j i).symm, extend_disjoint cost agent R child hc hij⟩⟩
  · simp only [finishDomination, Allocation.join_material, iUnion_union_distrib,
      hbase.cover, extend_cover cost agent R child hc]
  · intro i j
    change (cost i).real _ ≤ (cost i).real _
    rw [hvalue, hvalue]
    by_cases hi : i ∈ Set.range agent
    · obtain ⟨a, rfl⟩ := hi
      have hown : (cost (agent a)).real (material (added.pieces (agent a))) =
          (cost (agent a)).real (material (child.pieces a)) := by rw [extend_at]
      rw [hown]
      by_cases hj : j ∈ Set.range agent
      · obtain ⟨b, rfl⟩ := hj
        change _ ≤ _ + (cost (agent a)).real (material ((extend agent child).pieces (agent b)))
        rw [extend_at]
        exact add_le_add (hbase.envy_free (agent a) (agent b)) (hc.envy_free a b)
      · have hz : (cost (agent a)).real (material (added.pieces j)) = 0 := by
          rw [extend_outside agent child j hj]
          exact measureReal_empty
        rw [hz, add_zero]
        have hs : (cost (agent a)).real (material (child.pieces a)) ≤ (cost (agent a)).real R :=
          measureReal_mono (hc.subset cost agent R child a)
        have hm := hmargin a j hj
        linarith
    · have hz : (cost i).real (material (added.pieces i)) = 0 := by
        rw [extend_outside agent child i hi]
        exact measureReal_empty
      rw [hz, add_zero]
      exact (hbase.envy_free i j).trans (le_add_of_nonneg_right measureReal_nonneg)

/-- The only queries in a domination completion are those of its actual
smaller-population child; assembly of the complete original caches is pure. -/
def dominationProgram (base : Allocation n (Fin n)) (agent : Fin k ↪ Fin n)
    (child : Program (Query (Fin n)) ℝ (Allocation n (Fin k))) :
    Program (Query (Fin n)) ℝ (Allocation n (Fin n)) :=
  child.bind (fun out => .returned (finishDomination base agent out))

theorem domination_program_executes
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (base : Allocation n (Fin n)) (agent : Fin k ↪ Fin n)
    (child : Program (Query (Fin n)) ℝ (Allocation n (Fin k)))
    (prior : History (Query (Fin n)) ℝ) (out : Allocation n (Fin k))
    (trace : History (Query (Fin n)) ℝ) (h : Executes oracle child prior out trace) :
    Executes oracle (dominationProgram base agent child) prior (finishDomination base agent out) trace := by
  simpa only [dominationProgram, List.append_nil] using h.bind
    (fun out => Program.returned (finishDomination base agent out)) (Executes.returned _ _)

end EnvyFreeResearch.Full.Chores.Population
