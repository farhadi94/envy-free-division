import EnvyFreeResearch.Full.ChoresParentGeometry

/-!
# A concrete Core protocol on an original physical interval

The initial parent construction and memoized nonhungry prefix Core are one
ordinary-query program, with the complete earlier history supplied to each
reply. This closes the initial partition ledger for single-interval inputs;
disconnected recorded parents require the separate ordered-union compiler.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.IntervalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent PhysicalCore InitialPartition

def trimBudget (n : ℕ) : ℕ := n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1)
def queryBudget (n : ℕ) : ℕ := n ^ 2 + n * trimBudget n

/-- Prefix Core can be composed after the actual initial trace. -/
theorem prefix_executes {n : ℕ} (hn : 0 < n) (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (frame : Frame n) (store : Store n) (hvalid : ValidStore P frame store)
    (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hproper : ∀ p, frame.empty p ≠ frame.whole p) (prior : History (Query (Fin n)) ℝ) :
    ∃ result : PrefixResult n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (prefixProgram frame store) prior result trace ∧
      trace.length ≤ n * trimBudget n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ trimBudget n ∧
      ValidStore P frame result.store ∧ References result.store (fullKey n) result.state ∧
      EnvyFree (fullKey n) result.state ∧
      ∃ i, result.state.endpoint (result.state.matching i) = frame.whole (result.state.matching i) := by
  obtain ⟨table, trace, hexec, hlen, hcuts, hvalid', _, _, _⟩ :=
    layers_program_correct P hmono oracle hpolicy frame store hvalid hzero n prior
  obtain ⟨s, hs, href, hEF, ha⟩ := physical_cache_complete P hmono oracle hpolicy frame store hvalid hzero
    hproper n prior table trace hexec (fullKey n)
  let result : PrefixResult n := ⟨table.store, s⟩
  have hfinish : Executes oracle
      (match lookup table.cache (fullKey n) with
        | none => Program.failed
        | some s => Program.returned (⟨table.store, s⟩ : PrefixResult n))
      (prior ++ trace) result [] := by
    rw [hs]
    exact Executes.returned result _
  have hprogram : Executes oracle (prefixProgram frame store) prior result trace := by
    have h := hexec.bind (fun result =>
      match lookup result.cache (fullKey n) with
      | none => Program.failed
      | some s => Program.returned (⟨result.store, s⟩ : PrefixResult n)) hfinish
    rw [List.append_nil] at h
    exact h
  have hbudget : physicalBudget n n = trimBudget n := by
    rw [physicalBudget_eq]
    exact EnvyFreeResearch.R6Core.core_transition_closed n hn
  rw [hbudget] at hlen hcuts
  exact ⟨result, trace, hprogram, hlen, hcuts, hvalid', href, hEF,
    by simpa [result, fullKey] using anchored_has_whole hn frame (fullKey n) s ha⟩

def parentFrame {n : ℕ} (parent : Fin n → Parent n) : Frame n :=
  initialFrame (fun p => (parent p).left) (fun p => (parent p).right) (fun i p => (parent p).value i)

inductive Outcome (n : ℕ)
  | zero (agent : Fin n)
  | prefixes (parent : Fin n → Parent n) (state : PhysicalCore.State n n)

def finishProgram {n : ℕ} : InitialPartition.Outcome n → Program (Query (Fin n)) ℝ (Outcome n)
  | .zero i => .returned (.zero i)
  | .partition _ parents => if h : parents.length = n then
      let parent := indexed parents h
      (prefixProgram (parentFrame parent) (initialStore (parentFrame parent))).bind
        (fun result => .returned (.prefixes parent result.state))
    else .failed

def coreProgram {n : ℕ} (c : Fin n) (a b : ℝ) : Program (Query (Fin n)) ℝ (Outcome n) :=
  (initialProgram c a b).bind finishProgram

def Correct {n : ℕ} (P : Profile (Fin n)) (c : Fin n) (a b : ℝ) : Outcome n → Prop
  | .zero i => P.cumulative i b - P.cumulative i a = 0
  | .prefixes parent state =>
      (∀ p, a ≤ (parent p).left ∧ (parent p).left ≤ (parent p).right ∧ (parent p).right ≤ b) ∧
      (∀ i p, (parent p).value i = P.cumulative i (parent p).right - P.cumulative i (parent p).left) ∧
      (∀ p, (parent p).value c = (P.cumulative c b - P.cumulative c a) / n) ∧
      Pairwise (fun p q => Disjoint (Ioc (parent p).left (parent p).right) (Ioc (parent q).left (parent q).right)) ∧
      (⋃ p, Ioc (parent p).left (parent p).right) = Ioc a b ∧
      (∀ p, (parent p).left ≤ (state.endpoint p).point ∧ (state.endpoint p).point ≤ (parent p).right) ∧
      (∀ i p, prefixValue P (parentFrame parent) state i (state.matching i) ≤
        prefixValue P (parentFrame parent) state i p) ∧
      ∃ i, (state.endpoint (state.matching i)).point = (parent (state.matching i)).right

/-- Values needed to cache every complementary residue component are already
present in the returned endpoint records; obtaining them costs no new query. -/
def Cached {n : ℕ} (P : Profile (Fin n)) : Outcome n → Prop
  | .zero _ => True
  | .prefixes parent state => ∀ i p, ((state.endpoint p).formal i).1 =
      P.cumulative i (state.endpoint p).point - P.cumulative i (parent p).left

/-- Complete ordinary-query Core on a single physical input interval. No
parent values, successful cache entries, or chosen Cut roots are assumed. -/
theorem core_program_executes {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ outcome : Outcome n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (coreProgram c a b) prior outcome trace ∧ trace.length ≤ queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ n - 1 + trimBudget n ∧
      Correct P c a b outcome ∧ Cached P outcome := by
  obtain ⟨initial, first, hfirst, hfirstlen, hfirstcuts, hinitial⟩ :=
    initial_program_correct P hmono oracle hpolicy c a b hbound prior
  cases initial with
  | zero i =>
    refine ⟨.zero i, first, ?_, hfirstlen.trans (Nat.le_add_right _ _), ?_, hinitial, True.intro⟩
    · simpa only [coreProgram, List.append_nil] using hfirst.bind finishProgram (Executes.returned _ _)
    · exact hfirstcuts.trans (Nat.le_add_right _ _)
  | partition total parents =>
    obtain ⟨htotal, _, hlen, hchain, hequal⟩ := hinitial
    let parent := indexed parents hlen
    have hbounds : ∀ p, a ≤ (parent p).left ∧ (parent p).left ≤ (parent p).right ∧ (parent p).right ≤ b :=
      fun p => hchain.member_bounds P parents a b _ (indexed_mem parents hlen p)
    have hvalues : ∀ i p, (parent p).value i = P.cumulative i (parent p).right - P.cumulative i (parent p).left :=
      fun i p => hchain.member_value P parents a b _ (indexed_mem parents hlen p) i
    have hphysical : ∀ p, 0 ≤ (parent p).left ∧ (parent p).left ≤ (parent p).right ∧ (parent p).right ≤ 1 :=
      fun p => ⟨hbound.1.trans (hbounds p).1, (hbounds p).2.1, (hbounds p).2.2.trans hbound.2.2⟩
    let frame := parentFrame parent
    have hvalid : ValidStore P frame (initialStore frame) :=
      initialStore_valid P hmono _ _ _ hphysical hvalues
    obtain ⟨result, tail, htail, htaillen, htailcuts, hfinalValid, href, hEF, i, hi⟩ :=
      prefix_executes (Fin.pos c) P hmono oracle hpolicy frame (initialStore frame) hvalid
        (fun _ _ => rfl) (initialFrame_proper (Fin.pos c) _ _ _) (prior ++ first)
    have hfinish : Executes oracle (finishProgram (.partition total parents))
        (prior ++ first) (.prefixes parent result.state) tail := by
      rw [finishProgram, dite_eq_left hlen]
      simpa only [List.append_nil] using htail.bind
        (fun result => Program.returned (Outcome.prefixes parent result.state)) (Executes.returned _ _)
    refine ⟨.prefixes parent result.state, first ++ tail, hfirst.bind finishProgram hfinish,
      ?_, ?_, ⟨hbounds, hvalues, ?_, indexed_disjoint P parents a b hchain hlen,
      indexed_union P parents a b hchain hlen, physical_prefix_bounds P hfinalValid result.state href,
      real_envy_free P hfinalValid result.state href hEF, i, congrArg Record.point hi⟩, ?_⟩
    · rw [List.length_append]
      exact Nat.add_le_add hfirstlen htaillen
    · rw [List.countP_append]
      exact Nat.add_le_add hfirstcuts htailcuts
    · intro p
      rw [hequal _ (indexed_mem parents hlen p), htotal c]
    · intro i p
      exact ((hfinalValid p).2.1 _ (href p)).1 i

/-- The actual compiled adaptive next-action protocol returns within the full
initial-plus-prefix ledger, for every full-history legal reply policy. -/
theorem core_program_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1) :
    ∃ outcome : Outcome n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (coreProgram c a b).protocol oracle () (queryBudget n) [] = ⟨trace, .returned outcome⟩ ∧
      trace.length ≤ queryBudget n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ n - 1 + trimBudget n ∧
      Correct P c a b outcome := by
  obtain ⟨outcome, trace, hexec, hlen, hcuts, hcorrect⟩ :=
    core_program_executes P hmono oracle hpolicy c a b hbound []
  exact ⟨outcome, trace, hexec.run _ hlen, hlen, hcuts, hcorrect.1⟩

theorem core_program_correct_cached {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (a b : ℝ) (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1) :
    ∃ outcome : Outcome n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (coreProgram c a b).protocol oracle () (queryBudget n) [] = ⟨trace, .returned outcome⟩ ∧
      trace.length ≤ queryBudget n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ n - 1 + trimBudget n ∧
      Correct P c a b outcome ∧ Cached P outcome := by
  obtain ⟨outcome, trace, hexec, hlen, hcuts, hcorrect⟩ :=
    core_program_executes P hmono oracle hpolicy c a b hbound []
  exact ⟨outcome, trace, hexec.run _ hlen, hlen, hcuts, hcorrect⟩

end EnvyFreeResearch.Full.Chores.IntervalCore
