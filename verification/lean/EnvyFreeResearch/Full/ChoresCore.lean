import EnvyFreeResearch.R6Core
import EnvyFreeResearch.Full.ChoresRealization

/-!
# Continuous prefix states and the finite Core candidate search

This module connects the existing finite sign-class theorem to genuine
continuous prefix functions and defines the last-pair search used by Core.
Hungry anchored-state existence is supplied in `ChoresAnchored.lean`. No
statement here asserts the general chore theorem or its physical query bound.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Core

open Set

structure State (n : ℕ) where
  endpoint : Fin n → ℝ
  matching : Equiv.Perm (Fin n)

def Feasible {n : ℕ} (s : State n) : Prop :=
  ∀ p, s.endpoint p ∈ Icc (0 : ℝ) 1

def EnvyFree {n : ℕ} (cost : Fin n → Fin n → ℝ → ℝ) (s : State n) : Prop :=
  ∀ i p, cost i (s.matching i) (s.endpoint (s.matching i)) ≤ cost i p (s.endpoint p)

def Anchored {n : ℕ} (cost : Fin n → Fin n → ℝ → ℝ) (s : State n) : Prop :=
  ∃ rank : Fin n → ℕ, ∀ i,
    s.endpoint (s.matching i) = 1 ∨
      ∃ j, rank j < rank i ∧
        cost i (s.matching j) (s.endpoint (s.matching j)) =
          cost i (s.matching i) (s.endpoint (s.matching i))

/-- A hungry continuous parent cost profile. -/
structure HungryCosts (n : ℕ) where
  cost : Fin n → Fin n → ℝ → ℝ
  continuous : ∀ i p, ContinuousOn (cost i p) (Icc (0 : ℝ) 1)
  strict : ∀ i p, StrictMonoOn (cost i p) (Icc (0 : ℝ) 1)
  zero : ∀ i p, cost i p 0 = 0

/-- Canonical maximality now applies to actual prefix endpoints in `[0,1]`;
strictness outside the physical parent is not assumed. -/
theorem anchored_dominates {n : ℕ} (C : HungryCosts n) (s t : State n)
    (hs : Feasible s) (ht : Feasible t)
    (hEFs : EnvyFree C.cost s) (hEFt : EnvyFree C.cost t)
    (ha : Anchored C.cost s) : ∀ p, t.endpoint p ≤ s.endpoint p := by
  classical
  obtain ⟨rank, hanchor⟩ := ha
  let J := Finset.univ.filter (fun p => s.endpoint p < t.endpoint p)
  have hsign : ∀ i p, C.cost i p (s.endpoint p) < C.cost i p (t.endpoint p) ↔ p ∈ J := by
    intro i p
    simpa [J] using (C.strict i p).lt_iff_lt (hs p) (ht p)
  have h := EnvyFreeResearch.R6Core.anchored_table_dominates
    (fun i p => C.cost i p (s.endpoint p))
    (fun i p => C.cost i p (t.endpoint p))
    (fun i => C.cost i (s.matching i) (s.endpoint (s.matching i)))
    (fun i => C.cost i (t.matching i) (t.endpoint (t.matching i)))
    s.matching t.matching J rank (fun i => s.endpoint (s.matching i) = 1)
    (fun _ => rfl) (fun _ => rfl) hEFs hEFt hsign hanchor (by
      intro i hi
      apply (C.strict i (s.matching i)).monotoneOn (ht _) (hs _)
      rw [hi]
      exact (ht _).2)
  intro p
  exact (C.strict p p).le_iff_le (ht p) (hs p) |>.mp (h.2 p p)

theorem anchored_unique {n : ℕ} (C : HungryCosts n) (s t : State n)
    (hs : Feasible s) (ht : Feasible t)
    (hEFs : EnvyFree C.cost s) (hEFt : EnvyFree C.cost t)
    (has : Anchored C.cost s) (hat : Anchored C.cost t) : s.endpoint = t.endpoint := by
  funext p
  exact le_antisymm (anchored_dominates C t s ht hs hEFt hEFs hat p)
    (anchored_dominates C s t hs ht hEFs hEFt has p)

/-- Remove the tested last agent and parent from the physical profile. -/
def HungryCosts.remove {n : ℕ} (C : HungryCosts (n + 1)) (i p : Fin (n + 1)) :
    HungryCosts n where
  cost := fun j q => C.cost (i.succAbove j) (p.succAbove q)
  continuous := fun j q => C.continuous (i.succAbove j) (p.succAbove q)
  strict := fun j q => C.strict (i.succAbove j) (p.succAbove q)
  zero := fun j q => C.zero (i.succAbove j) (p.succAbove q)

/-- Add one new matched pair while retaining the entire smaller matching. -/
def extendMatching {n : ℕ} (i p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' i).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' p).symm)

@[simp] theorem extendMatching_new {n : ℕ} (i p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    extendMatching i p σ i = p := by simp [extendMatching]

@[simp] theorem extendMatching_old {n : ℕ} (i p : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    extendMatching i p σ (i.succAbove j) = p.succAbove (σ j) := by
  simp [extendMatching]

/-- One complete candidate is an actual finite endpoint vector and permutation. -/
def extendState {n : ℕ} (i p : Fin (n + 1)) (s : State n) (x : ℝ) : State (n + 1) where
  endpoint := p.insertNth x s.endpoint
  matching := extendMatching i p s.matching

@[simp] theorem extendState_new {n : ℕ} (i p : Fin (n + 1)) (s : State n) (x : ℝ) :
    (extendState i p s x).endpoint p = x := by simp [extendState]

@[simp] theorem extendState_old {n : ℕ} (i p : Fin (n + 1)) (s : State n)
    (x : ℝ) (q : Fin n) :
    (extendState i p s x).endpoint (p.succAbove q) = s.endpoint q := by
  simp [extendState]

/-- Minimum among the old physical prefixes. The empty problem uses whole cost. -/
def target {n : ℕ} (C : HungryCosts (n + 1)) (i p : Fin (n + 1)) (s : State n) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    Finset.univ.inf' h (fun q => C.cost i (p.succAbove q) (s.endpoint q))
  else C.cost i p 1

/-- A trim selector has only the ordinary physical target contract. -/
def CutSpec {n : ℕ} (C : HungryCosts n) (cut : Fin n → Fin n → ℝ → ℝ) : Prop :=
  ∀ i p t, 0 ≤ t → t ≤ C.cost i p 1 →
    cut i p t ∈ Icc (0 : ℝ) 1 ∧ C.cost i p (cut i p t) = t

/-- Continuous nonatomic prefix geometry provides every admissible trim. -/
theorem exists_cut_selector {n : ℕ} (C : HungryCosts n) :
    ∃ cut : Fin n → Fin n → ℝ → ℝ, CutSpec C cut := by
  classical
  have hex : ∀ i p t, 0 ≤ t ∧ t ≤ C.cost i p 1 →
      ∃ x ∈ Icc (0 : ℝ) 1, C.cost i p x = t := by
    intro i p t ht
    apply intermediate_value_Icc (by norm_num) (C.continuous i p)
    simpa [C.zero i p] using ht
  let cut := fun i p t => if h : 0 ≤ t ∧ t ≤ C.cost i p 1 then
    Classical.choose (hex i p t h) else 0
  refine ⟨cut, ?_⟩
  intro i p t ht0 ht1
  dsimp only [cut]
  rw [dite_eq_left (show 0 ≤ t ∧ t ≤ C.cost i p 1 from ⟨ht0, ht1⟩)]
  exact Classical.choose_spec (hex i p t ⟨ht0, ht1⟩)

/-- The candidate's newly queried endpoint. -/
def candidateEndpoint {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ)
    (i p : Fin (n + 1)) (s : State n) : ℝ :=
  if C.cost i p 1 ≤ target C i p s then 1 else cut i p (target C i p s)

def candidate {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ)
    (i p : Fin (n + 1)) (s : State n) : State (n + 1) :=
  extendState i p s (candidateEndpoint C cut i p s)

/-- Every candidate is checked against all actual finite EF comparisons. -/
def checkedCandidate {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ)
    (i p : Fin (n + 1)) (s : State n) : Option (State (n + 1)) := by
  classical
  exact if Feasible (candidate C cut i p s) ∧ EnvyFree C.cost (candidate C cut i p s) then
    some (candidate C cut i p s) else none

/-- First-success search makes its candidate order explicit and keeps failures. -/
def firstSome {α : Type*} : List (Option α) → Option α
  | [] => none
  | none :: xs => firstSome xs
  | some x :: _ => some x

theorem firstSome_some_mem {α : Type*} (xs : List (Option α)) (x : α)
    (h : firstSome xs = some x) : some x ∈ xs := by
  induction xs with
  | nil => simp [firstSome] at h
  | cons a xs ih =>
    cases a with
    | none => exact List.mem_cons_of_mem _ (ih h)
    | some a =>
      have ha : a = x := Option.some.inj h
      subst x
      exact List.mem_cons_self

theorem firstSome_exists_of_mem {α : Type*} (xs : List (Option α)) (x : α)
    (h : some x ∈ xs) : ∃ y, firstSome xs = some y := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    cases a with
    | none =>
      apply ih
      simpa using h
    | some a => exact ⟨a, rfl⟩

/-- The actual finite last-pair search, reading one smaller state per pair. -/
def searchStage {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ)
    (smaller : Fin (n + 1) → Fin (n + 1) → Option (State n)) : Option (State (n + 1)) :=
  firstSome ((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).toList.map
    (fun ip => (smaller ip.1 ip.2).bind (checkedCandidate C cut ip.1 ip.2)))

/-- The recursion is a concrete finite search specification. A physical
memoized balanced-subset table and its query trace are separate obligations. -/
def solve : (n : ℕ) → (C : HungryCosts n) →
    (Fin n → Fin n → ℝ → ℝ) → Option (State n)
  | 0, _, _ => some ⟨Fin.elim0, Equiv.refl _⟩
  | n + 1, C, cut => searchStage C cut (fun i p =>
      solve n (C.remove i p) (fun j q t => cut (i.succAbove j) (p.succAbove q) t))

/-- No invalid or non-EF candidate can be returned by the stage. -/
theorem searchStage_sound {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ)
    (smaller : Fin (n + 1) → Fin (n + 1) → Option (State n))
    (s : State (n + 1)) (h : searchStage C cut smaller = some s) :
    Feasible s ∧ EnvyFree C.cost s := by
  classical
  have hm := firstSome_some_mem _ s h
  obtain ⟨ip, _, hip⟩ := List.mem_map.mp hm
  cases hs : smaller ip.1 ip.2 with
  | none => simp [hs] at hip
  | some old =>
    rw [hs] at hip
    change checkedCandidate C cut ip.1 ip.2 old = some s at hip
    unfold checkedCandidate at hip
    split_ifs at hip with hg
    · cases Option.some.inj hip
      exact hg

/-- This is a partial-correctness theorem only: it does not assert success. -/
theorem solve_sound (n : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) (s : State n) (h : solve n C cut = some s) :
    Feasible s ∧ EnvyFree C.cost s := by
  cases n with
  | zero =>
    constructor
    · intro p; exact Fin.elim0 p
    · intro i; exact Fin.elim0 i
  | succ n => exact searchStage_sound C cut _ s h

theorem target_le {n : ℕ} (C : HungryCosts (n + 1)) (i p : Fin (n + 1))
    (s : State n) (q : Fin n) :
    target C i p s ≤ C.cost i (p.succAbove q) (s.endpoint q) := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨q, Finset.mem_univ q⟩
  rw [target, dite_eq_left hne]
  exact Finset.inf'_le _ (Finset.mem_univ q)

theorem le_target {n : ℕ} (C : HungryCosts (n + 1)) (i p : Fin (n + 1))
    (s : State n) (t : ℝ) (hwhole : t ≤ C.cost i p 1)
    (hprefix : ∀ q, t ≤ C.cost i (p.succAbove q) (s.endpoint q)) :
    t ≤ target C i p s := by
  classical
  unfold target
  split_ifs with hne
  · exact (Finset.le_inf'_iff hne _).mpr (fun q _ => hprefix q)
  · exact hwhole

/-- A last-pair candidate reproduces the endpoint vector of an anchored witness
once its smaller canonical prefix vector has been stored. The stored smaller
matching is allowed to differ from the witness matching. -/
theorem candidate_matches_witness {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ) (hcut : CutSpec C cut)
    (i p : Fin (n + 1)) (old : State n) (witness : State (n + 1))
    (hw : Feasible witness) (hEFw : EnvyFree C.cost witness)
    (hEFold : EnvyFree (C.remove i p).cost old)
    (hmatch : witness.matching i = p)
    (hprefix : ∀ q, old.endpoint q = witness.endpoint (p.succAbove q))
    (hanchor : witness.endpoint p = 1 ∨ ∃ q : Fin n,
      C.cost i (p.succAbove q) (witness.endpoint (p.succAbove q)) =
        C.cost i p (witness.endpoint p)) :
    (candidate C cut i p old).endpoint = witness.endpoint ∧
      Feasible (candidate C cut i p old) ∧ EnvyFree C.cost (candidate C cut i p old) := by
  classical
  have hown_le (q : Fin (n + 1)) :
      C.cost i p (witness.endpoint p) ≤ C.cost i q (witness.endpoint q) := by
    simpa only [hmatch] using hEFw i q
  have hwhole : C.cost i p (witness.endpoint p) ≤ C.cost i p 1 :=
    (C.strict i p).monotoneOn (hw p) (by simp) (hw p).2
  have htarget_ge : C.cost i p (witness.endpoint p) ≤ target C i p old :=
    le_target C i p old _ hwhole (fun q => by rw [hprefix q]; exact hown_le _)
  have hnew : candidateEndpoint C cut i p old = witness.endpoint p := by
    rcases hanchor with hwfull | ⟨q, hq⟩
    · have hfull : C.cost i p 1 ≤ target C i p old := by simpa [hwfull] using htarget_ge
      simp only [candidateEndpoint, ite_eq_left hfull, hwfull]
    · have htarget : target C i p old = C.cost i p (witness.endpoint p) := by
        apply le_antisymm _ htarget_ge
        calc
          target C i p old ≤ C.cost i (p.succAbove q) (old.endpoint q) := target_le C i p old q
          _ = C.cost i p (witness.endpoint p) := by rw [hprefix q, hq]
      by_cases hwfull : witness.endpoint p = 1
      · simp only [candidateEndpoint, htarget, hwfull, le_refl, ite_true]
      · have hlt : witness.endpoint p < 1 := lt_of_le_of_ne (hw p).2 hwfull
        have hcostlt := C.strict i p (hw p) (by simp) hlt
        have ht0 : 0 ≤ target C i p old := by
          rw [htarget, ← C.zero i p]
          exact (C.strict i p).monotoneOn (by simp) (hw p) (hw p).1
        have ht1 : target C i p old ≤ C.cost i p 1 := by rw [htarget]; exact hwhole
        have hc := hcut i p (target C i p old) ht0 ht1
        rw [candidateEndpoint, ite_eq_right (by rw [htarget]; exact not_le_of_gt hcostlt)]
        apply (C.strict i p).injOn hc.1 (hw p)
        exact hc.2.trans htarget
  have hend : (candidate C cut i p old).endpoint = witness.endpoint := by
    funext q
    refine Fin.succAboveCases p ?_ (fun q => ?_) q
    · simpa only [candidate, extendState_new] using hnew
    · simpa only [candidate, extendState_old] using hprefix q
  have hown : ∀ j,
      C.cost j ((candidate C cut i p old).matching j)
        ((candidate C cut i p old).endpoint ((candidate C cut i p old).matching j)) =
      C.cost j (witness.matching j) (witness.endpoint (witness.matching j)) := by
    intro j
    refine Fin.succAboveCases i ?_ (fun j => ?_) j
    · simp [candidate, extendState, hmatch, hnew]
    ·
      have hneq : witness.matching (i.succAbove j) ≠ p := by
        intro heq
        have heq' := witness.matching.injective (heq.trans hmatch.symm)
        exact i.succAbove_ne j heq'
      obtain heq | ⟨q, hq⟩ := Fin.eq_self_or_eq_succAbove p (witness.matching (i.succAbove j))
      · exact (hneq heq).elim
      · have hold := hEFold j q
        change C.cost (i.succAbove j) (p.succAbove (old.matching j))
          (old.endpoint (old.matching j)) ≤ C.cost (i.succAbove j) (p.succAbove q) (old.endpoint q) at hold
        rw [hprefix (old.matching j), hprefix q, ← hq] at hold
        have hwold := hEFw (i.succAbove j) (p.succAbove (old.matching j))
        simp only [candidate, extendState, extendMatching_old, Fin.insertNth_apply_succAbove]
        rw [hprefix (old.matching j)]
        exact le_antisymm hold hwold
  refine ⟨hend, ?_, ?_⟩
  · intro q
    rw [hend]
    exact hw q
  · intro j q
    rw [hown j, hend]
    exact hEFw j q

/-- The first-success finite search actually returns when the anchored witness's
last-pair branch is available. This proves candidate success rather than
assuming a successful transition in the table interface. -/
theorem searchStage_complete_from_witness {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ) (hcut : CutSpec C cut)
    (smaller : Fin (n + 1) → Fin (n + 1) → Option (State n))
    (i p : Fin (n + 1)) (old : State n) (witness : State (n + 1))
    (hlookup : smaller i p = some old)
    (hw : Feasible witness) (hEFw : EnvyFree C.cost witness)
    (hEFold : EnvyFree (C.remove i p).cost old)
    (hmatch : witness.matching i = p)
    (hprefix : ∀ q, old.endpoint q = witness.endpoint (p.succAbove q))
    (hanchor : witness.endpoint p = 1 ∨ ∃ q : Fin n,
      C.cost i (p.succAbove q) (witness.endpoint (p.succAbove q)) =
        C.cost i p (witness.endpoint p)) :
    ∃ s, searchStage C cut smaller = some s ∧ Feasible s ∧ EnvyFree C.cost s := by
  classical
  have hc := candidate_matches_witness C cut hcut i p old witness hw hEFw hEFold hmatch hprefix hanchor
  have hchecked : checkedCandidate C cut i p old = some (candidate C cut i p old) := by
    simp only [checkedCandidate, ite_eq_left hc.2]
  have hm : some (candidate C cut i p old) ∈
      ((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).toList.map
        (fun ip => (smaller ip.1 ip.2).bind (checkedCandidate C cut ip.1 ip.2))) := by
    apply List.mem_map.mpr
    refine ⟨(i, p), by simp, ?_⟩
    simp [hlookup, hchecked]
  obtain ⟨s, hs⟩ := firstSome_exists_of_mem _ _ hm
  exact ⟨s, hs, searchStage_sound C cut smaller s hs⟩

/-- Delete one matched pair without making any choice of a new matching. -/
def restrictMatching {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv i).trans
    ((π.subtypeEquiv (p := fun a => a ≠ i) (q := fun p => p ≠ π i)
      (fun _a => ⟨fun h heq => h (π.injective heq), fun h heq => h (congrArg π heq)⟩)).trans
      (finSuccAboveEquiv (π i)).symm)

@[simp] theorem restrictMatching_coe {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (j : Fin n) :
    (π i).succAbove (restrictMatching π i j) = π (i.succAbove j) := by
  change ((finSuccAboveEquiv (π i))
    ((finSuccAboveEquiv (π i)).symm
      ((π.subtypeEquiv (p := fun a => a ≠ i) (q := fun p => p ≠ π i)
      (fun _a => ⟨fun h heq => h (π.injective heq), fun h heq => h (congrArg π heq)⟩))
        ((finSuccAboveEquiv i) j)))).val = _
  simp [finSuccAboveEquiv_apply]

def restrictState {n : ℕ} (s : State (n + 1)) (i : Fin (n + 1)) : State n where
  endpoint := fun q => s.endpoint ((s.matching i).succAbove q)
  matching := restrictMatching s.matching i

theorem restrictState_feasible {n : ℕ} (s : State (n + 1))
    (hs : Feasible s) (i : Fin (n + 1)) : Feasible (restrictState s i) :=
  fun q => hs ((s.matching i).succAbove q)

theorem restrictState_envyFree {n : ℕ} (C : HungryCosts (n + 1)) (s : State (n + 1))
    (hs : EnvyFree C.cost s) (i : Fin (n + 1)) :
    EnvyFree (C.remove i (s.matching i)).cost (restrictState s i) := by
  intro j q
  simpa only [HungryCosts.remove, restrictState, restrictMatching_coe] using
    hs (i.succAbove j) ((s.matching i).succAbove q)

/-- Deleting a last-ranked pair preserves every earlier anchor. -/
theorem restrictState_anchored {n : ℕ} (C : HungryCosts (n + 1)) (s : State (n + 1))
    (rank : Fin (n + 1) → ℕ)
    (hanchor : ∀ i, s.endpoint (s.matching i) = 1 ∨
      ∃ j, rank j < rank i ∧ C.cost i (s.matching j) (s.endpoint (s.matching j)) =
        C.cost i (s.matching i) (s.endpoint (s.matching i)))
    (i : Fin (n + 1)) (hlast : ∀ j, rank j ≤ rank i) :
    Anchored (C.remove i (s.matching i)).cost (restrictState s i) := by
  refine ⟨fun j => rank (i.succAbove j), ?_⟩
  intro j
  rcases hanchor (i.succAbove j) with hw | ⟨k, hk, heq⟩
  · left
    simpa only [restrictState, restrictMatching_coe] using hw
  · have hki : k ≠ i := by
      intro hki
      subst k
      exact (not_lt_of_ge (hlast (i.succAbove j))) hk
    obtain h | ⟨l, hl⟩ := Fin.eq_self_or_eq_succAbove i k
    · exact (hki h).elim
    · right
      refine ⟨l, ?_, ?_⟩
      · simpa only [← hl] using hk
      · simpa only [HungryCosts.remove, restrictState, restrictMatching_coe, ← hl] using heq

theorem target_nonnegative {n : ℕ} (C : HungryCosts (n + 1))
    (i p : Fin (n + 1)) (s : State n) (hs : Feasible s) : 0 ≤ target C i p s := by
  apply le_target
  · rw [← C.zero i p]
    exact (C.strict i p).monotoneOn (by simp) (by simp) (by norm_num)
  · intro q
    rw [← C.zero i (p.succAbove q)]
    exact (C.strict i (p.succAbove q)).monotoneOn (by simp) (hs q) (hs q).1

/-- Every successful extension retains all old anchors and appends the new
agent after them. This is derived from exact trim targets and finite minima. -/
theorem candidate_anchored {n : ℕ} (C : HungryCosts (n + 1))
    (cut : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ) (hcut : CutSpec C cut)
    (i p : Fin (n + 1)) (s : State n) (hs : Feasible s)
    (ha : Anchored (C.remove i p).cost s) : Anchored C.cost (candidate C cut i p s) := by
  classical
  obtain ⟨rank, hrank⟩ := ha
  let R := (Finset.univ : Finset (Fin n)).sup rank + 1
  refine ⟨i.insertNth R rank, ?_⟩
  intro j
  refine Fin.succAboveCases i ?_ (fun j => ?_) j
  · by_cases hwhole : C.cost i p 1 ≤ target C i p s
    · left
      simp [candidate, extendState, candidateEndpoint, hwhole]
    · have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
        by_contra hn
        have ht : target C i p s = C.cost i p 1 := by simp [target, hn]
        exact hwhole (by rw [ht])
      obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_inf' hne
        (fun q => C.cost i (p.succAbove q) (s.endpoint q))
      have hqtarget : target C i p s = C.cost i (p.succAbove q) (s.endpoint q) := by
        rw [target, dite_eq_left hne]
        exact hq
      have hc := hcut i p (target C i p s) (target_nonnegative C i p s hs)
        (le_of_not_ge hwhole)
      right
      refine ⟨i.succAbove (s.matching.symm q), ?_, ?_⟩
      · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        exact Nat.lt_succ_of_le (Finset.le_sup (f := rank) (Finset.mem_univ _))
      · simp only [candidate, extendState, extendMatching_new, extendMatching_old,
          Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Equiv.apply_symm_apply,
          candidateEndpoint, ite_eq_right hwhole]
        exact hqtarget.symm.trans hc.2.symm
  · rcases hrank j with hw | ⟨k, hk, heq⟩
    · left
      simpa only [candidate, extendState, extendMatching_old,
        Fin.insertNth_apply_succAbove] using hw
    · right
      refine ⟨i.succAbove k, ?_, ?_⟩
      · simpa only [Fin.insertNth_apply_succAbove] using hk
      · simpa only [candidate, extendState, extendMatching_old,
          Fin.insertNth_apply_succAbove, HungryCosts.remove] using heq

/-- Every returned state of the recursive search is anchored. This statement
still does not assert that the search returns. -/
theorem solve_anchored (n : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) (hcut : CutSpec C cut)
    (s : State n) (h : solve n C cut = some s) : Anchored C.cost s := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    have hm := firstSome_some_mem _ s h
    obtain ⟨ip, _, hip⟩ := List.mem_map.mp hm
    let subcut := fun j q t => cut (ip.1.succAbove j) (ip.2.succAbove q) t
    cases hs : solve n (C.remove ip.1 ip.2) subcut with
    | none => simp [subcut, hs] at hip
    | some old =>
      have hsub : CutSpec (C.remove ip.1 ip.2) subcut := by
        intro j q t ht0 ht1
        exact hcut _ _ _ ht0 ht1
      have haold := ih (C.remove ip.1 ip.2) subcut hsub old hs
      have hfold := (solve_sound n (C.remove ip.1 ip.2) subcut old hs).1
      have hip' : checkedCandidate C cut ip.1 ip.2 old = some s := by simpa [subcut, hs] using hip
      unfold checkedCandidate at hip'
      split_ifs at hip' with hg
      cases Option.some.inj hip'
      exact candidate_anchored C cut hcut ip.1 ip.2 old hfold haold

/-- Full correctness of the finite recursive prefix search, conditional only on
an actual anchored witness. The proof derives every successful candidate and
permits arbitrary legal trim roots. `ChoresAnchored.lean` constructs this
witness unconditionally; memoized physical query accounting is still separate. -/
theorem solve_complete_from_anchored (n : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) (hcut : CutSpec C cut)
    (witness : State n) (hw : Feasible witness) (hEFw : EnvyFree C.cost witness)
    (ha : Anchored C.cost witness) :
    ∃ s, solve n C cut = some s ∧ Feasible s ∧ EnvyFree C.cost s ∧
      Anchored C.cost s ∧ s.endpoint = witness.endpoint := by
  classical
  induction n with
  | zero =>
    let s : State 0 := ⟨Fin.elim0, Equiv.refl _⟩
    have hs : solve 0 C cut = some s := rfl
    have hv := solve_sound 0 C cut s hs
    exact ⟨s, hs, hv.1, hv.2, solve_anchored 0 C cut hcut s hs,
      funext (fun p => Fin.elim0 p)⟩
  | succ n ih =>
    obtain ⟨rank, hrank⟩ := ha
    obtain ⟨i, _, himax⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin (n + 1))) rank (by simp)
    let p := witness.matching i
    let subcut := fun j q t => cut (i.succAbove j) (p.succAbove q) t
    have hsubcut : CutSpec (C.remove i p) subcut := by
      intro j q t ht0 ht1
      exact hcut _ _ _ ht0 ht1
    have hsubf := restrictState_feasible witness hw i
    have hsubEF := restrictState_envyFree C witness hEFw i
    have hsuba := restrictState_anchored C witness rank hrank i
      (fun j => himax j (Finset.mem_univ j))
    obtain ⟨old, hlookup, hfold, hEFold, haold, hcanonical⟩ :=
      ih (C.remove i p) subcut hsubcut (restrictState witness i) hsubf hsubEF hsuba
    have hprefix : ∀ q, old.endpoint q = witness.endpoint (p.succAbove q) :=
      fun q => congrFun hcanonical q
    have hlast : witness.endpoint p = 1 ∨ ∃ q : Fin n,
        C.cost i (p.succAbove q) (witness.endpoint (p.succAbove q)) =
          C.cost i p (witness.endpoint p) := by
      rcases hrank i with hwhole | ⟨j, hj, heq⟩
      · exact Or.inl hwhole
      · have hne : witness.matching j ≠ p := by
          intro heq
          have hji : j = i := witness.matching.injective heq
          subst j
          exact Nat.lt_irrefl _ hj
        obtain h | ⟨q, hq⟩ := Fin.eq_self_or_eq_succAbove p (witness.matching j)
        · exact (hne h).elim
        · right
          exact ⟨q, by simpa only [← hq] using heq⟩
    obtain ⟨s, hs, hsf, hsEF⟩ := searchStage_complete_from_witness C cut hcut
      (fun i p => solve n (C.remove i p)
        (fun j q t => cut (i.succAbove j) (p.succAbove q) t))
      i p old witness hlookup hw hEFw hEFold rfl hprefix hlast
    have hsolve : solve (n + 1) C cut = some s := hs
    have hsa := solve_anchored (n + 1) C cut hcut s hsolve
    exact ⟨s, hsolve, hsf, hsEF, hsa,
      anchored_unique C s witness hsf hw hsEF hEFw hsa ⟨rank, hrank⟩⟩

end EnvyFreeResearch.Full.Chores.Core
