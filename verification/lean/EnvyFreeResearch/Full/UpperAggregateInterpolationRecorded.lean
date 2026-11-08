import EnvyFreeResearch.Full.UpperAggregateInterpolationUnions
import Mathlib.Data.Finset.Sort

/-! Sort and deduplicate the actual component endpoints to eliminate the
auxiliary boundary-grid premise from the recorded-union theorem. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain

def componentEndpoints (cs : List Component) : Finset ℝ :=
  (cs.flatMap (fun c => [c.left, c.right])).toFinset

theorem mem_componentEndpoints (cs : List Component) (x : ℝ) :
    x ∈ componentEndpoints cs ↔ ∃ c ∈ cs, x = c.left ∨ x = c.right := by
  simp [componentEndpoints]

/-- Every literal finite component union obeys the telescoping estimate.
Its boundaries may be chosen after observing the entire generated list. The
proof constructs the strictly sorted distinct endpoint tuple itself. -/
theorem arbitrary_recorded_union_error_le {Term Generated : Type*} [Fintype Term] [Fintype Generated]
    (coeff : Term → ℝ) (μ : Term → Measure ℝ) [∀ t, IsFiniteMeasure (μ t)]
    [∀ t, NullSingletonClass (μ t)] (cs : List Component) (points : Generated → ℝ)
    (hendpoints : ∀ c ∈ cs,
      (signedValue coeff μ (Iic c.left) = 0 ∨ ∃ j, points j = c.left) ∧
      (signedValue coeff μ (Iic c.right) = 0 ∨ ∃ j, points j = c.right)) :
    |signedValue coeff μ (domain cs)| ≤ ∑ j, |signedValue coeff μ (Iic (points j))| := by
  by_cases hnil : cs = []
  · subst cs
    simp only [domain, signedValue, measureReal_empty, mul_zero, Finset.sum_const_zero, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · have hnonempty : (componentEndpoints cs).Nonempty := by
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hnil
      exact ⟨c.left, (mem_componentEndpoints cs c.left).mpr ⟨c, hc, Or.inl rfl⟩⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hnonempty)
    let iso : Fin (m + 1) ≃o (componentEndpoints cs) := (componentEndpoints cs).orderIsoOfFin hm
    let cuts : Fin (m + 1) → ℝ := fun p => (iso p).val
    have hcuts : StrictMono cuts := fun p q hpq => iso.strictMono hpq
    have hcontains (x : ℝ) (hx : x ∈ componentEndpoints cs) : ∃ p, cuts p = x := by
      obtain ⟨p, hp⟩ := iso.surjective ⟨x, hx⟩
      exact ⟨p, congrArg Subtype.val hp⟩
    apply recorded_union_error_le coeff μ cs cuts hcuts ?_ points ?_
    · intro c hc
      exact ⟨hcontains c.left ((mem_componentEndpoints cs _).mpr ⟨c, hc, Or.inl rfl⟩),
        hcontains c.right ((mem_componentEndpoints cs _).mpr ⟨c, hc, Or.inr rfl⟩)⟩
    · intro p
      obtain ⟨c, hc, hp | hp⟩ := (mem_componentEndpoints cs (cuts p)).mp (iso p).property
      · rw [hp]
        exact (hendpoints c hc).1
      · rw [hp]
        exact (hendpoints c hc).2

end EnvyFreeResearch.Full.UpperAggregateInterpolation
