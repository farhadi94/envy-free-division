import EnvyFreeResearch.Full.ChoresMemoization

/-!
# The materialized Core table and its complete trim-request ledger

Every tested candidate is retained in the request log, including candidates
that fail the EF test. A whole-parent branch or unavailable smaller state
makes no trim request. This is the instrumented hungry computation: the
ordinary interval implementation and persistent nonhungry replay remain
separate obligations.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Core.Memo

open scoped BigOperators

structure TrimRequest (n : ℕ) where
  agent : Fin n
  parent : Fin n
  target : ℝ

/-- A candidate computes its new endpoint once and logs precisely its trim
branch. The EF test is the actual test against the given continuous costs. -/
def trial {k : ℕ} (C : HungryCosts (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (i p : Fin (k + 1)) (old : Option (State k)) :
    Option (State (k + 1)) × List (TrimRequest (k + 1)) := by
  classical
  exact match old with
  | none => (none, [])
  | some s =>
    let whole := C.cost i p 1 ≤ target C i p s
    let x := if whole then 1 else cut i p (target C i p s)
    let candidate := extendState i p s x
    (if Feasible candidate ∧ EnvyFree C.cost candidate then some candidate else none,
      if whole then [] else [⟨i, p, target C i p s⟩])

lemma trial_value {k : ℕ} (C : HungryCosts (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (i p : Fin (k + 1)) (old : Option (State k)) :
    (trial C cut i p old).1 = old.bind (checkedCandidate C cut i p) := by
  cases old <;> rfl

lemma trial_length_le {k : ℕ} (C : HungryCosts (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (i p : Fin (k + 1)) (old : Option (State k)) :
    (trial C cut i p old).2.length ≤ 1 := by
  classical
  cases old with
  | none => simp [trial]
  | some s => simp only [trial]; split_ifs <;> simp

lemma trial_singleton_requests (C : HungryCosts 1) (cut : Fin 1 → Fin 1 → ℝ → ℝ)
    (i p : Fin 1) (old : Option (State 0)) : (trial C cut i p old).2 = [] := by
  classical
  cases old with
  | none => rfl
  | some s => simp [trial, target]

lemma flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (b : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ b) : (xs.flatMap f).length ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm]
      using Nat.add_le_add hx hxs

/-- All candidates in the fixed finite order are tested, even after an earlier
success. Keeping these exploratory requests is conservative for the bound. -/
def stage {k : ℕ} (C : HungryCosts (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State k)) :
    Option (State (k + 1)) × List (TrimRequest (k + 1)) :=
  let candidates := (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).toList.map
    (fun ip => trial C cut ip.1 ip.2 (smaller ip.1 ip.2))
  (firstSome (candidates.map Prod.fst), candidates.flatMap Prod.snd)

lemma stage_value {k : ℕ} (C : HungryCosts (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State k)) :
    (stage C cut smaller).1 = searchStage C cut smaller := by
  simp [stage, searchStage, List.map_map, Function.comp_def, trial_value]

lemma stage_length_le {k : ℕ} (C : HungryCosts (k + 1))
    (cut : Fin (k + 1) → Fin (k + 1) → ℝ → ℝ)
    (smaller : Fin (k + 1) → Fin (k + 1) → Option (State k)) :
    (stage C cut smaller).2.length ≤ (k + 1) ^ 2 := by
  unfold stage
  dsimp only
  rw [List.flatMap_map]
  have h := flatMap_length_le (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).toList
    (fun ip => (trial C cut ip.1 ip.2 (smaller ip.1 ip.2)).2) 1
    (fun ip _ => trial_length_le C cut ip.1 ip.2 _)
  simpa [pow_two] using h

lemma stage_singleton_requests (C : HungryCosts 1) (cut : Fin 1 → Fin 1 → ℝ → ℝ)
    (smaller : Fin 1 → Fin 1 → Option (State 0)) : (stage C cut smaller).2 = [] := by
  simp [stage, List.flatMap_map, Function.comp_def, trial_singleton_requests]

/-- Lift a local trim request back to the original agent and parent labels. -/
def liftRequest {n k : ℕ} (K : Key n k) (q : TrimRequest k) : TrimRequest n :=
  ⟨K.1 q.agent, K.2 q.parent, q.target⟩

/-- This table explicitly shares the preceding list and accumulates every
trial's requests once. It does not call the recursive subset solver. -/
def loggedLayers {n : ℕ} (C : HungryCosts n) (cut : Fin n → Fin n → ℝ → ℝ) :
    (k : ℕ) → Cache n k × List (TrimRequest n)
  | 0 => (layers C cut 0, [])
  | k + 1 =>
    let previous := loggedLayers C cut k
    let results := (Finset.univ : Finset (Key n (k + 1))).toList.map (fun K =>
      let result := stage (restrict C K) (fun i p t => cut (K.1 i) (K.2 p) t)
        (fun i p => lookup previous.1 (remove K i p))
      ((K, result.1), result.2.map (liftRequest K)))
    (results.map Prod.fst, previous.2 ++ results.flatMap Prod.snd)

lemma loggedLayers_value (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) : (loggedLayers C cut k).1 = layers C cut k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [loggedLayers, layers, List.map_map, Function.comp_def, stage_value, ih]

lemma loggedLayers_singleton_requests (n : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) : (loggedLayers C cut 1).2 = [] := by
  simp [loggedLayers, List.flatMap_map, Function.comp_def, stage_singleton_requests]

lemma loggedLayers_step_bound (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) :
    (loggedLayers C cut (k + 1)).2.length ≤ (loggedLayers C cut k).2.length +
      (k + 1) ^ 2 * (n.choose (k + 1)) ^ 2 := by
  classical
  conv_lhs => rw [loggedLayers]
  dsimp only
  rw [List.length_append, List.flatMap_map]
  apply Nat.add_le_add_left
  have h := flatMap_length_le (Finset.univ : Finset (Key n (k + 1))).toList
    (fun K => ((stage (restrict C K) (fun i p t => cut (K.1 i) (K.2 p) t)
      (fun i p => lookup (loggedLayers C cut k).1 (remove K i p))).2.map (liftRequest K)))
    ((k + 1) ^ 2) (by
      intro K _
      rw [List.length_map]
      exact stage_length_le _ _ _)
  simpa only [Function.comp_def, Finset.length_toList, Finset.card_univ, key_card, Nat.mul_comm] using h

/-- The actual logged table obeys the weighted subset count; the singleton
layer is proved to issue no trims, rather than charged away as an assumption. -/
theorem loggedLayers_bound (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) :
    (loggedLayers C cut k).2.length ≤
      ∑ j ∈ Finset.range (k - 1), (j + 2) ^ 2 * (n.choose (j + 2)) ^ 2 := by
  induction k with
  | zero => simp [loggedLayers]
  | succ k ih =>
    cases k with
    | zero => simp [loggedLayers_singleton_requests]
    | succ k =>
      have hs := loggedLayers_step_bound n (k + 1) C cut
      have h := hs.trans (Nat.add_le_add_right ih _)
      rw [show k + 1 + 1 - 1 = k + 1 by omega, Finset.sum_range_succ]
      simpa only [Nat.add_sub_cancel, Nat.add_assoc] using h

/-- The precise `T_n` ledger is derived from the concrete materialized cache
and all of its attempted trim branches. These are logical prefix trim requests,
not yet the final ordinary-query trace of the nonhungry protocol. -/
theorem full_logged_trim_bound (n : ℕ) (hn : 0 < n) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) :
    (loggedLayers C cut n).2.length ≤ n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1) := by
  have h := loggedLayers_bound n n C cut
  change (loggedLayers C cut n).2.length ≤ EnvyFreeResearch.R6Core.coreTransitionCount n at h
  simpa only [EnvyFreeResearch.R6Core.core_transition_closed n hn] using h

/-- All materialized logged entries are correct without assuming any earlier
cache successes or an anchored witness. -/
theorem logged_lookup_succeeds (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) (hcut : CutSpec C cut) (K : Key n k) :
    ∃ s, lookup (loggedLayers C cut k).1 K = some s ∧ Feasible s ∧
      EnvyFree (restrict C K).cost s ∧ Anchored (restrict C K).cost s := by
  rw [loggedLayers_value]
  exact every_lookup_succeeds n k C cut hcut K

end EnvyFreeResearch.Full.Chores.Core.Memo
