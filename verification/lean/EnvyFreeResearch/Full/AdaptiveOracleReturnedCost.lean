import EnvyFreeResearch.Full.AdaptiveOracle
import Mathlib.Tactic

/-! Fuel stability for a single history-based adaptive protocol. These
properties concern its actual answered trace, not a dominating cost ledger. -/
namespace EnvyFreeResearch.Full.AdaptiveOracle
open OracleProtocol
universe u v w t
variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}

theorem run_answered_prefix_of_le (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (f g : ℕ) (hfg : f ≤ g)
    (history : History Query Reply) :
    (run next oracle tape f history).answered <+: (run next oracle tape g history).answered := by
  induction f generalizing g history with
  | zero =>
    cases hn : next tape history with
    | returned out => simp [hn]
    | diverge => simp [hn]
    | ask q => rw [run_zero_ask _ _ _ _ _ hn]; exact List.nil_prefix
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      cases hn : next tape history with
      | returned out => simp [hn]
      | diverge => simp [hn]
      | ask q =>
        cases ho : oracle history q with
        | none => simp [hn,ho]
        | some r =>
          simp only [run_succ_some _ _ _ _ _ _ _ hn ho]
          exact List.cons_prefix_cons.mpr ⟨rfl,ih g (by omega) (history++[(q,r)])⟩

theorem run_returned_add (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (out : Output)
    (h : (run next oracle tape fuel history).stop=.returned out) (extra : ℕ) :
    run next oracle tape (fuel+extra) history=run next oracle tape fuel history := by
  induction fuel generalizing history with
  | zero =>
    cases hn : next tape history with
    | returned o => simp [hn]
    | diverge => simp [hn] at h
    | ask q => simp [hn] at h
  | succ fuel ih =>
    cases hn : next tape history with
    | returned o => simp [hn]
    | diverge => simp [hn] at h
    | ask q =>
      cases ho : oracle history q with
      | none => simp [hn,ho] at h
      | some r =>
        have ht : (run next oracle tape fuel (history++[(q,r)])).stop=.returned out := by
          simpa only [run_succ_some _ _ _ _ _ _ _ hn ho] using h
        rw [Nat.succ_add,run_succ_some _ _ _ _ _ _ _ hn ho,run_succ_some _ _ _ _ _ _ _ hn ho,
          ih (history++[(q,r)]) ht]

theorem run_returned_stable (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (trace : History Query Reply) (out : Output)
    (h : run next oracle tape fuel history=⟨trace,.returned out⟩)
    (g : ℕ) (hfg : fuel ≤ g) : run next oracle tape g history=⟨trace,.returned out⟩ := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le hfg
  rw [run_returned_add next oracle tape fuel history out (congrArg Execution.stop h) extra,h]

theorem run_prefix_of_returned (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (trace : History Query Reply) (out : Output)
    (h : run next oracle tape fuel history=⟨trace,.returned out⟩) (g : ℕ) :
    (run next oracle tape g history).answered <+: trace := by
  rcases le_total g fuel with hle | hle
  · have hp := run_answered_prefix_of_le next oracle tape g fuel hle history
    simpa only [h] using hp
  · rw [run_returned_stable next oracle tape fuel history trace out h g hle]

end EnvyFreeResearch.Full.AdaptiveOracle
