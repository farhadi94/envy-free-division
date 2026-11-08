import EnvyFreeResearch.Full.ChoresSubCoreChain

/-!
# The equal-value part of the SubCore chain transition

Backward containment is derived from old and current cake-EF comparisons.
Forward equalities are then forced by the unused-parent guarantee. The proof
is order-theoretic: it applies to ordinary hungry suffix values and to strict
formal record values, without assuming the equalities it must establish.
-/

namespace EnvyFreeResearch.Full.Chores.SubCore

open Set

variable {Agent Parent Coord Value : Type*} [LinearOrder Coord] [LinearOrder Value]

/-- The source proof's backwards and forwards walks, including the equality
of the final freed suffix with its current whole input parent. -/
theorem equal_value_chain (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (hstrict : ∀ i p, StrictMonoOn (value i p) feasible)
    (h : ℕ) (hh : 0 < h) (agent : ℕ → Agent) (parent : ℕ → Parent)
    (old cap : Parent → Coord) (current : ℕ → Coord)
    (hold : ∀ r ≤ h, old (parent r) ∈ feasible)
    (hcap : ∀ r ≤ h, cap (parent r) ∈ feasible)
    (hcurrent : ∀ r < h, current r ∈ feasible)
    (hinside : ∀ r < h, current r ≤ cap (parent (r + 1)))
    (hstart : old (parent 0) ≤ cap (parent 0))
    (hlast : cap (parent h) ≤ old (parent h))
    (hOldEF : ∀ r < h, value (agent r) (parent (r + 1)) (old (parent (r + 1))) ≤
      value (agent r) (parent r) (old (parent r)))
    (hCurrentEF : ∀ r < h, ∀ s < h,
      value (agent r) (parent (s + 1)) (current s) ≤
        value (agent r) (parent (r + 1)) (current r))
    (hUnused : value (agent 0) (parent 0) (cap (parent 0)) ≤
      value (agent 0) (parent 1) (current 0)) :
    (∀ r < h, current r = old (parent (r + 1)) ∧
      value (agent r) (parent (r + 1)) (current r) = value (agent r) (parent r) (old (parent r))) ∧
    cap (parent 0) = old (parent 0) ∧ cap (parent h) = old (parent h) := by
  have backward : ∀ d r : ℕ, r + d = h → 0 < d → current r ≤ old (parent (r + 1)) := by
    intro d
    induction d with
    | zero => intro r heq hd; omega
    | succ d ih =>
      intro r heq hd
      have hr : r < h := by omega
      by_cases hz : d = 0
      · have hrh : r + 1 = h := by omega
        exact (hinside r hr).trans (hrh ▸ hlast)
      · have hr1 : r + 1 < h := by omega
        have hnext : current (r + 1) ≤ old (parent (r + 1 + 1)) := ih (r + 1) (by omega) (by omega)
        have hcompare := (hCurrentEF (r + 1) hr1 r hr).trans
          (((hstrict (agent (r + 1)) (parent (r + 1 + 1))).monotoneOn
            (hcurrent (r + 1) hr1) (hold (r + 1 + 1) (by omega)) hnext).trans (hOldEF (r + 1) hr1))
        exact ((hstrict (agent (r + 1)) (parent (r + 1))).le_iff_le
          (hcurrent r hr) (hold (r + 1) (by omega))).mp hcompare
  have hback : ∀ r < h, current r ≤ old (parent (r + 1)) :=
    fun r hr => backward (h - r) r (by omega) (by omega)
  have hupper : ∀ r < h, value (agent r) (parent (r + 1)) (current r) ≤
      value (agent r) (parent r) (old (parent r)) := by
    intro r hr
    exact ((hstrict (agent r) (parent (r + 1))).monotoneOn (hcurrent r hr)
      (hold (r + 1) (by omega)) (hback r hr)).trans (hOldEF r hr)
  have conclude : ∀ r < h,
      value (agent r) (parent r) (old (parent r)) ≤ value (agent r) (parent (r + 1)) (current r) →
      current r = old (parent (r + 1)) ∧
      value (agent r) (parent (r + 1)) (current r) = value (agent r) (parent r) (old (parent r)) := by
    intro r hr hlower
    have heq := le_antisymm ((hstrict (agent r) (parent (r + 1))).monotoneOn
      (hcurrent r hr) (hold (r + 1) (by omega)) (hback r hr)) ((hOldEF r hr).trans hlower)
    exact ⟨(hstrict (agent r) (parent (r + 1))).injOn (hcurrent r hr) (hold (r + 1) (by omega)) heq,
      le_antisymm (hupper r hr) hlower⟩
  have forward : ∀ r < h, current r = old (parent (r + 1)) ∧
      value (agent r) (parent (r + 1)) (current r) = value (agent r) (parent r) (old (parent r)) := by
    intro r
    induction r with
    | zero =>
      intro hr
      apply conclude 0 hr
      exact ((hstrict (agent 0) (parent 0)).monotoneOn (hold 0 (by omega))
        (hcap 0 (by omega)) hstart).trans hUnused
    | succ r ih =>
      intro hr
      obtain ⟨heq, _⟩ := ih (by omega)
      apply conclude (r + 1) hr
      have h := hCurrentEF (r + 1) hr r (by omega)
      simpa only [heq] using h
  refine ⟨forward, ?_, ?_⟩
  · apply le_antisymm ?_ hstart
    exact ((hstrict (agent 0) (parent 0)).le_iff_le (hcap 0 (by omega)) (hold 0 (by omega))).mp
      (hUnused.trans (forward 0 hh).2.le)
  · have hend := hinside (h - 1) (by omega)
    rw [(forward (h - 1) (by omega)).1, Nat.sub_add_cancel hh] at hend
    exact le_antisymm hlast hend

end EnvyFreeResearch.Full.Chores.SubCore
