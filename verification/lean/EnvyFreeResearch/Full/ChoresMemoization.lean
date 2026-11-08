import EnvyFreeResearch.Full.ChoresAnchored
import Mathlib.Order.Hom.PowersetCard

/-!
# A genuine balanced-subset cache for hungry Core

Each subset is represented by its unique increasing enumeration. Deleting a
local index composes that enumeration with `succAbove`, so differently reached
copies of the same subset have the same cache key. Each layer is materialized
as one finite list, and the next layer reads that list. No recursive smaller
problem is called inside a candidate trial.

This module proves equivalence with the closed hungry search theorem. Its
cost-function reads must still be implemented using the persistent physical
record table before this becomes the general nonhungry oracle protocol.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Core.Memo

open scoped BigOperators

abbrev Key (n k : ℕ) := (Fin k ↪o Fin n) × (Fin k ↪o Fin n)

/-- Increasing enumerations identify balanced subset pairs without storing
permutations of one and the same subset as different states. -/
theorem key_card (n k : ℕ) : Fintype.card (Key n k) = (n.choose k) ^ 2 := by
  have h : Fintype.card (Fin k ↪o Fin n) = n.choose k := by
    rw [Fintype.card_congr (Set.powersetCard.ofFinEmbEquiv (n := k) (I := Fin n))]
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
    simp
  simp only [Key, Fintype.card_prod, h, pow_two]

/-- Delete one agent and one parent while retaining their physical labels. -/
def remove {n k : ℕ} (K : Key n (k + 1)) (i p : Fin (k + 1)) : Key n k :=
  ((Fin.succAboveOrderEmb i).trans K.1, (Fin.succAboveOrderEmb p).trans K.2)

/-- Restriction reads the same original cost functions on a balanced subset. -/
def restrict {n k : ℕ} (C : HungryCosts n) (K : Key n k) : HungryCosts k where
  cost i p := C.cost (K.1 i) (K.2 p)
  continuous i p := C.continuous (K.1 i) (K.2 p)
  strict i p := C.strict (K.1 i) (K.2 p)
  zero i p := C.zero (K.1 i) (K.2 p)

@[simp] theorem restrict_remove {n k : ℕ} (C : HungryCosts n)
    (K : Key n (k + 1)) (i p : Fin (k + 1)) :
    restrict C (remove K i p) = (restrict C K).remove i p := rfl

abbrev Cache (n k : ℕ) := List (Key n k × Option (State k))

def lookup {n k : ℕ} (cache : Cache n k) (K : Key n k) : Option (State k) := by
  classical
  exact match cache with
  | [] => none
  | (L, value) :: rest => if K = L then value else lookup rest K

lemma lookup_map {n k : ℕ} (keys : List (Key n k)) (f : Key n k → Option (State k))
    (K : Key n k) (hK : K ∈ keys) : lookup (keys.map (fun L => (L, f L))) K = f K := by
  classical
  induction keys with
  | nil => simp at hK
  | cons L rest ih =>
    simp only [List.map_cons, lookup]
    by_cases heq : K = L
    · simp [heq]
    · rw [ite_eq_right heq]
      apply ih
      exact (List.mem_cons.mp hK).resolve_left heq

/-- One materialized table per subset size. `previous` is a cache lookup, not
a recursive call indexed by the candidate's deleted pair. -/
def layers {n : ℕ} (C : HungryCosts n) (cut : Fin n → Fin n → ℝ → ℝ) :
    (k : ℕ) → Cache n k
  | 0 => (Finset.univ : Finset (Key n 0)).toList.map
      (fun K => (K, some ⟨Fin.elim0, Equiv.refl _⟩))
  | k + 1 =>
    let previous := layers C cut k
    (Finset.univ : Finset (Key n (k + 1))).toList.map (fun K =>
      (K, searchStage (restrict C K) (fun i p t => cut (K.1 i) (K.2 p) t)
        (fun i p => lookup previous (remove K i p))))

/-- The physical-label-preserving deletion makes cache lookup equal to the
proved finite search, even when the same smaller key has many callers. -/
theorem lookup_layers (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) (K : Key n k) :
    lookup (layers C cut k) K = solve k (restrict C K)
      (fun i p t => cut (K.1 i) (K.2 p) t) := by
  classical
  induction k with
  | zero =>
    exact lookup_map _ _ K (by simp)
  | succ k ih =>
    rw [layers, lookup_map _ _ K (by simp)]
    unfold solve
    congr 1
    funext i p
    have h := ih (remove K i p)
    rw [restrict_remove] at h
    simpa only [remove, RelEmbedding.coe_trans, Fin.coe_succAboveOrderEmb, Function.comp_apply] using h

/-- Every balanced subset is present once in its actual materialized layer. -/
theorem layer_keys (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) :
    (layers C cut k).map Prod.fst = (Finset.univ : Finset (Key n k)).toList := by
  cases k <;> simp [layers, List.map_map, Function.comp_def]

theorem layer_keys_nodup (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) : ((layers C cut k).map Prod.fst).Nodup := by
  classical
  rw [layer_keys]
  exact Finset.nodup_toList _

theorem layer_length (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) : (layers C cut k).length = (n.choose k) ^ 2 := by
  have h := congrArg List.length (layer_keys n k C cut)
  simpa only [List.length_map, Finset.length_toList, Finset.card_univ, key_card] using h

/-- Correctness is inherited from the proved unconditional hungry theorem;
there is no successful-state assumption on the cache. -/
theorem every_lookup_succeeds (n k : ℕ) (C : HungryCosts n)
    (cut : Fin n → Fin n → ℝ → ℝ) (hcut : CutSpec C cut) (K : Key n k) :
    ∃ s, lookup (layers C cut k) K = some s ∧ Feasible s ∧
      EnvyFree (restrict C K).cost s ∧ Anchored (restrict C K).cost s := by
  have hlocal : CutSpec (restrict C K) (fun i p t => cut (K.1 i) (K.2 p) t) := by
    intro i p t ht0 ht1
    exact hcut _ _ _ ht0 ht1
  obtain ⟨s, hsolve, hs, hEF, ha, _⟩ := solve_complete k (restrict C K) _ hlocal
  exact ⟨s, (lookup_layers n k C cut K).trans hsolve, hs, hEF, ha⟩

end EnvyFreeResearch.Full.Chores.Core.Memo
