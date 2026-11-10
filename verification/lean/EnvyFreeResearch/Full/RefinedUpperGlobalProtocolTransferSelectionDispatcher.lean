import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferSelectionSearch

/-! Measurable dispatch after the finite transfer search, including branches
that continue to use the original cached data. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer.Selection
open MeasureTheory Set
open scoped Classical

variable {k : ℕ}

theorem select_postcompose_measurable {Y : Type*} [MeasurableSpace Y]
    (tau : ℝ) (f : Option (Candidate k) → Y) :
    Measurable (fun data => f (select tau data)) :=
  Measurable.of_discrete.comp (select_measurable tau)

theorem select_dispatch_measurable {Y : Type*} [MeasurableSpace Y]
    (tau : ℝ) (next : Option (Candidate k) → CachedData k → Y)
    (hnext : ∀ c, Measurable (next c)) :
    Measurable (fun data => next (select tau data) data) := by
  intro s hs
  have heq : (fun data => next (select tau data) data) ⁻¹' s =
      ⋃ c : Option (Candidate k), (select tau) ⁻¹' {c} ∩ (next c) ⁻¹' s := by
    ext data
    simp only [Set.mem_preimage,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨select tau data,rfl,h⟩
    · rintro ⟨c,hc,h⟩
      simpa only [hc] using h
  rw [heq]
  exact MeasurableSet.iUnion (fun c =>
    ((select_measurable tau) (measurableSet_singleton c)).inter (hnext c hs))

end EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer.Selection
