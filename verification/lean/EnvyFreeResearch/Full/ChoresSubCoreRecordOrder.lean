import EnvyFreeResearch.Full.ChoresPersistent
import Mathlib.Order.PiLex

/-!
# Immutable physical records as ordered SubCore coordinates

The full cached formal row vector is the primary ordering key; the physical
coordinate breaks any remaining tie. This is a total order on actual record
objects, and every permanent-table `Before` edge is strict in it. Algorithms
can therefore retain complete cached records as coordinates, rather than
looking up values in a changing store by an unstable numeric index.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Persistent

def OrderedRecord (n : ℕ) := Record n

def OrderedRecord.record {n : ℕ} (r : OrderedRecord n) : Record n := r

def orderedRecord {n : ℕ} (r : Record n) : OrderedRecord n := r

def recordKey {n : ℕ} (r : OrderedRecord n) : Lex (Lex (Fin n → Lex (ℝ × ℚ)) × ℝ) :=
  toLex (toLex (fun i => toLex (r.record.formal i)), r.record.point)

theorem recordKey_injective {n : ℕ} : Function.Injective (@recordKey n) := by
  intro r s heq
  have hf : r.record.formal = s.record.formal := by
    funext i
    exact congrArg (fun key => ofLex ((ofLex (ofLex key).1) i)) heq
  have hp : r.record.point = s.record.point := congrArg (fun key => (ofLex key).2) heq
  cases r
  cases s
  cases hp
  cases hf
  rfl

instance orderedRecordLinearOrder (n : ℕ) : LinearOrder (OrderedRecord n) :=
  LinearOrder.lift' recordKey recordKey_injective

def formalValue {n : ℕ} (i : Fin n) (r : OrderedRecord n) : Lex (ℝ × ℚ) := toLex (r.record.formal i)

theorem before_ordered_lt {n : ℕ} (hn : 0 < n) {r s : Record n} (h : Before r s) :
    orderedRecord r < orderedRecord s := by
  change recordKey (orderedRecord r) < recordKey (orderedRecord s)
  apply Prod.Lex.left
  change Pi.Lex (· < ·) (· < ·) (fun i => toLex (r.formal i)) (fun i => toLex (s.formal i))
  refine ⟨⟨0, hn⟩, ?_, ?_⟩
  · intro j hj
    have hjval : j.val < 0 := hj
    omega
  · exact Prod.Lex.toLex_lt_toLex.mpr (h.2 ⟨0, hn⟩)

theorem pairwise_ordered_records {n : ℕ} (hn : 0 < n) (records : List (Record n))
    (h : records.Pairwise Before) : (records.map orderedRecord).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact h.imp (before_ordered_lt hn)

theorem orderedRecord_injective {n : ℕ} : Function.Injective (@orderedRecord n) := fun _ _ h => h

theorem formalValue_strict {n : ℕ} {r s : Record n} (h : Before r s) (i : Fin n) :
    formalValue i (orderedRecord r) < formalValue i (orderedRecord s) := Prod.Lex.toLex_lt_toLex.mpr (h.2 i)

end EnvyFreeResearch.Full.Chores.SubCorePhysical
