import EnvyFreeResearch.Full.ChoresPhysicalCore

/-!
# Sequential physical Core stages retaining all exploratory records

Every candidate runs against the current shared store, and every later trial
inherits all of its records, even after an earlier candidate succeeds. The
returned candidate is the first success in the fixed order. The bounds below
come from actual policy-reply traces through the verified program compiler.
Full nonhungry success is a separate finite-realization replay obligation.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent

lemma References.mono {n k : ℕ} {oldStore newStore : Store n}
    (hkeep : ∀ q, (oldStore q).Sublist (newStore q))
    {K : Core.Memo.Key n k} {s : State n k} (href : References oldStore K s) :
    References newStore K s := fun p => (hkeep (K.2 p)).subset (href p)

def prefer {α : Type*} : Option α → Option α → Option α
  | some a, _ => some a
  | none, b => b

lemma prefer_some {α : Type*} (first second : Option α) (a : α)
    (h : prefer first second = some a) : first = some a ∨ second = some a := by
  cases first with
  | none => exact Or.inr h
  | some x => exact Or.inl h

/-- Trials are composed as query programs, not as calls to a valuation-aware
success interface. The shared store is threaded through every failed candidate. -/
def trialsProgram {n k : ℕ} (frame : Frame n) (store : Store n)
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k)) :
    List (Fin (k + 1) × Fin (k + 1)) → Program (Query (Fin n)) ℝ (TrialResult n (k + 1))
  | [] => .returned ⟨store, none⟩
  | ip :: rest => (trialProgram frame store K ip.1 ip.2 (smaller ip.1 ip.2)).bind (fun result =>
      (trialsProgram frame result.store K smaller rest).bind (fun tail =>
        .returned ⟨tail.store, prefer result.output tail.output⟩))

/-- Complete physical termination and query accounting for a finite candidate
stage, preserving all cache references and checking every returned EF state. -/
theorem trials_program_correct {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (hsmaller : ∀ i p s, smaller i p = some s → References store (Core.Memo.remove K i p) s)
    (trials : List (Fin (k + 1) × Fin (k + 1)))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : TrialResult n (k + 1), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (trialsProgram frame store K smaller trials) prior result trace ∧
      trace.length ≤ n * trials.length ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ trials.length ∧
      ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      (∀ s, result.output = some s → References result.store K s ∧ EnvyFree K s) := by
  classical
  induction trials generalizing store prior with
  | nil =>
    refine ⟨⟨store, none⟩, [], Executes.returned _ _, by simp, by simp, hvalid,
      fun _ => List.Sublist.refl _, ?_⟩
    intro s hs
    cases hs
  | cons ip rest ih =>
    obtain ⟨first, firstTrace, hfirst, hfirstLen, hfirstCuts, hfirstStore, hfirstKeep, hfirstOut⟩ :=
      trial_program_correct P hmono oracle hpolicy frame store hvalid hzero K ip.1 ip.2
        (smaller ip.1 ip.2) (hsmaller ip.1 ip.2) prior
    have hsmall' : ∀ i p s, smaller i p = some s →
        References first.store (Core.Memo.remove K i p) s :=
      fun i p s hs => (hsmaller i p s hs).mono hfirstKeep
    obtain ⟨tail, tailTrace, htail, htailLen, htailCuts, htailStore, htailKeep, htailOut⟩ :=
      ih first.store hfirstStore hsmall' (prior ++ firstTrace)
    let result : TrialResult n (k + 1) := ⟨tail.store, prefer first.output tail.output⟩
    have htail' : Executes oracle
        ((trialsProgram frame first.store K smaller rest).bind (fun tail =>
          .returned ⟨tail.store, prefer first.output tail.output⟩))
        (prior ++ firstTrace) result tailTrace := by
      simpa only [List.append_nil] using htail.bind (fun tail => Program.returned
        (⟨tail.store, prefer first.output tail.output⟩ : TrialResult n (k + 1)))
        (Executes.returned result ((prior ++ firstTrace) ++ tailTrace))
    have hexec : Executes oracle (trialsProgram frame store K smaller (ip :: rest)) prior result
        (firstTrace ++ tailTrace) := by
      exact hfirst.bind (fun first =>
        (trialsProgram frame first.store K smaller rest).bind (fun tail =>
          .returned (⟨tail.store, prefer first.output tail.output⟩ : TrialResult n (k + 1)))) htail'
    refine ⟨result, firstTrace ++ tailTrace, hexec, ?_, ?_, htailStore,
      fun q => (hfirstKeep q).trans (htailKeep q), ?_⟩
    · simp only [List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [List.countP_append, List.length_cons]
      omega
    · intro s hs
      rcases prefer_some first.output tail.output s hs with hfirsts | htails
      · exact ⟨(hfirstOut s hfirsts).1.mono htailKeep, (hfirstOut s hfirsts).2⟩
      · exact htailOut s htails

/-- The actual physical stage tests the finite Cartesian set of all last pairs. -/
def stageProgram {n k : ℕ} (frame : Frame n) (store : Store n)
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k)) :
    Program (Query (Fin n)) ℝ (TrialResult n (k + 1)) :=
  trialsProgram frame store K smaller (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).toList

/-- The quadratic candidate bound is derived from the actual physical stage
and includes every exploratory Cut and every observer-recording Eval. -/
theorem stage_program_correct {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (hsmaller : ∀ i p s, smaller i p = some s → References store (Core.Memo.remove K i p) s)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : TrialResult n (k + 1), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (stageProgram frame store K smaller) prior result trace ∧
      trace.length ≤ n * (k + 1) ^ 2 ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ (k + 1) ^ 2 ∧
      ValidStore P frame result.store ∧ (∀ q, (store q).Sublist (result.store q)) ∧
      (∀ s, result.output = some s → References result.store K s ∧ EnvyFree K s) := by
  simpa only [stageProgram, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, pow_two] using trials_program_correct P hmono oracle hpolicy frame store hvalid
    hzero K smaller hsmaller (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).toList prior

/-- The composed physical stage is also an actual shared adaptive protocol,
with the proved bound as its fuel, rather than only a big-step certificate. -/
theorem stage_compiled_run {n k : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (K : Core.Memo.Key n (k + 1))
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State n k))
    (hsmaller : ∀ i p s, smaller i p = some s → References store (Core.Memo.remove K i p) s) :
    ∃ result : TrialResult n (k + 1), ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (stageProgram frame store K smaller).protocol oracle () (n * (k + 1) ^ 2) [] =
        ⟨trace, .returned result⟩ ∧
      trace.length ≤ n * (k + 1) ^ 2 ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ (k + 1) ^ 2 ∧
      ValidStore P frame result.store ∧
      (∀ s, result.output = some s → References result.store K s ∧ EnvyFree K s) := by
  obtain ⟨result, trace, hexec, hlen, hcuts, hvalid', _, hout⟩ := stage_program_correct
    P hmono oracle hpolicy frame store hvalid hzero K smaller hsmaller []
  exact ⟨result, trace, hexec.run _ hlen, hlen, hcuts, hvalid', hout⟩

end EnvyFreeResearch.Full.Chores.PhysicalCore
