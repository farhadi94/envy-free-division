import EnvyFreeResearch.Full.ChoresEqualizers

/-! The complete equalizer table is produced by an actual sequential
ordinary-query program. Its baseline values come from the input cache;
original envy-freeness proves all target feasibility inequalities. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Equalizers
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical BigOperators

variable {n : ℕ}

abbrev Table (n : ℕ) := Fin n × Fin n → RestrictedCutResult n

def recordList (baseline : Fin n → ℝ) (parents : Fin n → List (Parent n)) :
    List (Fin n × Fin n) → Program (Query (Fin n)) ℝ (Table n)
  | [] => .returned (fun _ => ⟨0,⟨[],[]⟩,fun _ => 0⟩)
  | pair :: rest => (recordProgram pair.1 pair.2 baseline (parents pair.1)).bind (fun first =>
      (recordList baseline parents rest).bind (fun tail =>
        .returned (Function.update tail pair first)))

theorem record_list_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (pieces : Fin n → Set ℝ) (parents : Fin n → List (Parent n))
    (hc : ∀ p, CacheValid (measureProfile cost) (pieces p) (parents p))
    (baseline : Fin n → ℝ) (hbase : ∀ i, 0 ≤ baseline i)
    (hfeasible : ∀ p i, baseline i ≤ cachedValue (parents p) i)
    (hown : ∀ p, baseline p = cachedValue (parents p) p)
    (pairs : List (Fin n × Fin n)) (prior : History (Query (Fin n)) ℝ) :
    ∃ table : Table n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordList baseline parents pairs) prior table trace ∧
      trace.length ≤ n*pairs.length ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ pairs.length ∧
      (∀ pair ∈ pairs, Correct cost (pieces pair.1) baseline pair.2 (table pair)) ∧
      (∀ p, (p,p) ∈ pairs → (table (p,p)).parts.prefixParts = parents p ∧
        (table (p,p)).parts.suffixParts = []) := by
  induction pairs generalizing prior with
  | nil => exact ⟨_,[],Executes.returned _ _,by simp,by simp,by simp,by simp⟩
  | cons pair rest ih =>
    obtain ⟨first,t₁,hfirst,hlen₁,hcuts₁,hcorrect₁,hown₁⟩ :=
      record_correct cost oracle hpolicy (pieces pair.1) (parents pair.1) (hc pair.1)
        pair.1 pair.2 baseline (hbase pair.2) (hfeasible pair.1 pair.2) (hown pair.1) prior
    obtain ⟨tail,t₂,htail,hlen₂,hcuts₂,hcorrect₂,hown₂⟩ := ih (prior++t₁)
    let table := Function.update tail pair first
    refine ⟨table,t₁++t₂,?_,?_,?_,?_,?_⟩
    · have htail' := htail.bind (fun tail => Program.returned (Function.update tail pair first))
        (Executes.returned _ ((prior++t₁)++t₂))
      have h := hfirst.bind (fun first => (recordList baseline parents rest).bind
        (fun tail => Program.returned (Function.update tail pair first)))
        (by simpa only [List.append_nil] using htail')
      simpa only [recordList] using h
    · simp only [List.length_append,List.length_cons]
      calc
        t₁.length+t₂.length ≤ n+n*rest.length := Nat.add_le_add hlen₁ hlen₂
        _ = n*(rest.length+1) := by ring
    · simp only [List.countP_append,List.length_cons]
      omega
    · intro q hq
      by_cases heq : q = pair
      · subst q
        simpa only [table,Function.update_self] using hcorrect₁
      · have hr : q ∈ rest := (List.mem_cons.mp hq).resolve_left heq
        simpa only [table,Function.update_of_ne heq] using hcorrect₂ q hr
    · intro p hp
      by_cases heq : (p,p) = pair
      · subst pair
        simpa only [table,Function.update_self] using
          And.intro (hown₁ rfl).1 (hown₁ rfl).2.1
      · have hr : (p,p) ∈ rest := (List.mem_cons.mp hp).resolve_left heq
        simpa only [table,Function.update_of_ne heq] using hown₂ p hr

def baselines (parents : Fin n → List (Parent n)) (i : Fin n) : ℝ := cachedValue (parents i) i

def recordTable (parents : Fin n → List (Parent n)) : Program (Query (Fin n)) ℝ (Table n) :=
  recordList (baselines parents) parents Finset.univ.toList

/-- Every original snapshot equalizer, including zero marks and the whole
own share, is recorded within a polynomial number of original queries. -/
theorem record_table_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (pieces : Fin n → Set ℝ) (parents : Fin n → List (Parent n))
    (hc : ∀ p, CacheValid (measureProfile cost) (pieces p) (parents p))
    (hEF : ∀ i j, (cost i).real (pieces i) ≤ (cost i).real (pieces j))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ table : Table n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (recordTable parents) prior table trace ∧
      trace.length ≤ n^3 ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ n^2 ∧
      (∀ p i, Correct cost (pieces p) (baselines parents) i (table (p,i))) ∧
      (∀ p, (table (p,p)).parts.prefixParts = parents p ∧ (table (p,p)).parts.suffixParts = []) := by
  have hv (p i : Fin n) : cachedValue (parents p) i = (cost i).real (pieces p) := by
    rw [← (hc p).2.2,material_value cost _ (hc p).1 (hc p).2.1]
  have hbase (i : Fin n) : 0 ≤ baselines parents i := by
    rw [baselines,hv]
    exact measureReal_nonneg
  have hfeasible (p i : Fin n) : baselines parents i ≤ cachedValue (parents p) i := by
    simpa only [baselines,hv] using hEF i p
  obtain ⟨table,trace,hexec,hlen,hcuts,hcorrect,hown⟩ :=
    record_list_correct cost oracle hpolicy pieces parents hc (baselines parents) hbase hfeasible
      (fun _ => rfl) Finset.univ.toList prior
  refine ⟨table,trace,hexec,?_,?_,fun p i => hcorrect (p,i) (by simp),fun p => hown p (by simp)⟩
  · simpa [pow_succ,Nat.mul_assoc] using hlen
  · simpa [pow_two] using hcuts

end EnvyFreeResearch.Full.Chores.Equalizers
