import EnvyFreeResearch.Full.ChoresSubCoreCache
import EnvyFreeResearch.Full.ChoresUnionAlign

/-!
# Paid recording of final donor suffixes

A masked SubCore endpoint may have been created in another observer's mask.
This program aligns that endpoint in the actual retained block, paying up to
`n` original Evals.  It returns exact all-observer caches of both the retained
suffix and its complementary prefix.  A whole table costs at most n times the
number of proposals, with no Cuts.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentRecording
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ}

theorem aligned_endpoints (P : Profile (Fin n)) (ps : List (Parent n)) (hv : Valid P ps) :
    Aligned ps 0 ∧ Aligned ps 1 := by
  constructor
  · intro p hp
    exact Or.inr (((valid_iff_forall _ _).mp hv p hp).1.1)
  · intro p hp
    exact Or.inl (((valid_iff_forall _ _).mp hv p hp).1.2.2)

def recordProgram (cache : List (Parent n)) (point : ℝ) :
    Program (Query (Fin n)) ℝ (Split n) :=
  (alignProgram point cache).bind (fun fresh =>
    .returned ⟨window 0 point fresh, window point 1 fresh⟩)

def Correct (P : Profile (Fin n)) (U : Set ℝ) (point : ℝ) (out : Split n) : Prop :=
  CacheValid P (U ∩ Iic point) out.prefixParts ∧
  CacheValid P (U ∩ Ioc point 1) out.suffixParts

theorem record_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (point : ℝ)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Split n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordProgram cache point) prior out trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) = 0 ∧
      Correct (measureProfile cost) U point out := by
  obtain ⟨fresh, trace, hexec, hlen, hcuts, hfresh, halign, _, _⟩ :=
    align_program_cache (measureProfile cost) oracle hpolicy U point cache hc prior
  let out : Split n := ⟨window 0 point fresh, window point 1 fresh⟩
  refine ⟨out, trace, ?_, hlen, hcuts, ?_⟩
  · simpa only [recordProgram, List.append_nil] using hexec.bind
      (fun fresh => Program.returned (⟨window 0 point fresh, window point 1 fresh⟩ : Split n))
      (Executes.returned _ (prior ++ trace))
  · obtain ⟨hzero, hone⟩ := aligned_endpoints (measureProfile cost) fresh hfresh.1
    have hU : U ⊆ Ioc (0 : ℝ) 1 := by
      rw [← hc.2.2]
      intro x hx
      obtain ⟨p, hp, hpx⟩ := (mem_material_iff cache x).mp hx
      have hb := ((valid_iff_forall _ _).mp hc.1 p hp).1
      exact ⟨hb.1.trans_lt hpx.1, hpx.2.trans hb.2.2⟩
    constructor
    · refine ⟨window_valid _ hfresh.1, window_ordered hfresh.2.1, ?_⟩
      change material (window 0 point fresh) = _
      rw [window_material hzero halign, hfresh.2.2]
      ext x
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, (hU h.1).1, h.2⟩
    · refine ⟨window_valid _ hfresh.1, window_ordered hfresh.2.1, ?_⟩
      change material (window point 1 fresh) = _
      rw [window_material halign hone, hfresh.2.2]

theorem recorded_values (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (point : ℝ) (out : Split n)
    (h : Correct (measureProfile cost) U point out) (i : Fin n) :
    cachedValue out.prefixParts i = (cost i).real (U ∩ Iic point) ∧
      cachedValue out.suffixParts i = (cost i).real (U ∩ Ioc point 1) := by
  constructor
  · rw [← h.1.2.2, material_value cost _ h.1.1 h.1.2.1]
  · rw [← h.2.2.2, material_value cost _ h.2.1 h.2.2.1]

variable {Task : Type*} [DecidableEq Task]

def recordList (cache : Task → List (Parent n)) (point : Task → ℝ) :
    List Task → Program (Query (Fin n)) ℝ (Task → Split n)
  | [] => .returned (fun _ => ⟨[], []⟩)
  | task :: rest => (recordProgram (cache task) (point task)).bind (fun first =>
      (recordList cache point rest).bind (fun tail =>
        .returned (Function.update tail task first)))

theorem record_list_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (domains : Task → Set ℝ) (cache : Task → List (Parent n)) (point : Task → ℝ)
    (hc : ∀ task, CacheValid (measureProfile cost) (domains task) (cache task))
    (tasks : List Task) (prior : History (Query (Fin n)) ℝ) :
    ∃ table : Task → Split n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordList cache point tasks) prior table trace ∧
      trace.length ≤ n * tasks.length ∧ trace.countP (fun qr => isCutQuery qr.1) = 0 ∧
      ∀ task ∈ tasks, Correct (measureProfile cost) (domains task) (point task) (table task) := by
  induction tasks generalizing prior with
  | nil => exact ⟨_, [], Executes.returned _ _, by simp, by simp, by simp⟩
  | cons task rest ih =>
    obtain ⟨first, t₁, hfirst, hlen₁, hcuts₁, hcorrect₁⟩ :=
      record_correct cost oracle hpolicy (domains task) (cache task) (hc task) (point task) prior
    obtain ⟨tail, t₂, htail, hlen₂, hcuts₂, hcorrect₂⟩ := ih (prior ++ t₁)
    let table := Function.update tail task first
    refine ⟨table, t₁ ++ t₂, ?_, ?_, ?_, ?_⟩
    · have ht := htail.bind (fun tail => Program.returned (Function.update tail task first))
        (Executes.returned _ ((prior ++ t₁) ++ t₂))
      simpa only [recordList, List.append_nil] using hfirst.bind
        (fun first => (recordList cache point rest).bind
          (fun tail => Program.returned (Function.update tail task first)))
        (by simpa only [List.append_nil] using ht)
    · simp only [List.length_append, List.length_cons]
      nlinarith
    · simp only [List.countP_append, hcuts₁, hcuts₂, zero_add]
    · intro j hj
      by_cases heq : j = task
      · subst j
        simpa only [table, Function.update_self] using hcorrect₁
      · exact (by simpa only [table, Function.update_of_ne heq] using
          hcorrect₂ j ((List.mem_cons.mp hj).resolve_left heq))

def recordTable [Fintype Task] (cache : Task → List (Parent n)) (point : Task → ℝ) :
    Program (Query (Fin n)) ℝ (Task → Split n) := recordList cache point Finset.univ.toList

theorem record_table_correct [Fintype Task] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (domains : Task → Set ℝ) (cache : Task → List (Parent n)) (point : Task → ℝ)
    (hc : ∀ task, CacheValid (measureProfile cost) (domains task) (cache task))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ table : Task → Split n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordTable cache point) prior table trace ∧
      trace.length ≤ n * Fintype.card Task ∧ trace.countP (fun qr => isCutQuery qr.1) = 0 ∧
      ∀ task, Correct (measureProfile cost) (domains task) (point task) (table task) := by
  obtain ⟨table, trace, hexec, hlen, hcuts, hcorrect⟩ :=
    record_list_correct cost oracle hpolicy domains cache point hc Finset.univ.toList prior
  exact ⟨table, trace, hexec, by simpa using hlen, hcuts,
    fun task => hcorrect task (by simp)⟩

end EnvyFreeResearch.Full.Chores.ComponentRecording
