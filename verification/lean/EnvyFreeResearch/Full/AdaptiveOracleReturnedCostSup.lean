import EnvyFreeResearch.Full.AdaptiveOracleReturnedCost
import Mathlib.Data.ENNReal.Basic

/-! Actual protocol costs are the suprema of finite-fuel answered counts.
On every returning tape these are exactly its returned trace counts. -/
noncomputable section
open scoped ENNReal
namespace EnvyFreeResearch.Full.AdaptiveOracle
open OracleProtocol
universe u v w t
variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}

def queryCost (next : Protocol Tape Query Reply Output) (oracle : Policy Query Reply)
    (tape : Tape) (history : History Query Reply := []) : ℝ≥0∞ :=
  ⨆ fuel : ℕ, ((run next oracle tape fuel history).answered.length : ℝ≥0∞)

def markedCost (mark : Query → Bool) (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (history : History Query Reply := []) : ℝ≥0∞ :=
  ⨆ fuel : ℕ, (((run next oracle tape fuel history).answered.map Prod.fst).countP mark : ℝ≥0∞)

theorem returned_queryCost (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (trace : History Query Reply) (out : Output)
    (h : run next oracle tape fuel history=⟨trace,.returned out⟩) :
    queryCost next oracle tape history=(trace.length : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro g
    exact_mod_cast (run_prefix_of_returned next oracle tape fuel history trace out h g).length_le
  · apply le_iSup_of_le fuel
    simp only [h]
    exact le_rfl

theorem returned_markedCost (mark : Query → Bool) (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (trace : History Query Reply) (out : Output)
    (h : run next oracle tape fuel history=⟨trace,.returned out⟩) :
    markedCost mark next oracle tape history=((trace.map Prod.fst).countP mark : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro g
    obtain ⟨tail,ht⟩ := run_prefix_of_returned next oracle tape fuel history trace out h g
    have hle : (((run next oracle tape g history).answered.map Prod.fst).countP mark) ≤
        ((trace.map Prod.fst).countP mark) := by
      rw [←ht,List.map_append,List.countP_append]
      omega
    exact_mod_cast hle
  · apply le_iSup_of_le fuel
    simp only [h]
    exact le_rfl

theorem returned_costs_finite (mark : Query → Bool) (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (trace : History Query Reply) (out : Output)
    (h : run next oracle tape fuel history=⟨trace,.returned out⟩) :
    queryCost next oracle tape history ≠ ∞ ∧ markedCost mark next oracle tape history ≠ ∞ := by
  rw [returned_queryCost next oracle tape fuel history trace out h,
    returned_markedCost mark next oracle tape fuel history trace out h]
  simp

end EnvyFreeResearch.Full.AdaptiveOracle
