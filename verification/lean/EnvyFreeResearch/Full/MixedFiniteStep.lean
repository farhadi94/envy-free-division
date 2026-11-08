import EnvyFreeResearch.Full.MixedFrontier
import EnvyFreeResearch.Full.FiniteStepDensity

/-! Explicit finite-step closure of the actual hard-input construction. -/

namespace EnvyFreeResearch.Full.MixedFiniteStep
open MixedFrontier FiniteStepDensity
open scoped Classical

variable {Agent : Type*} {α : ℝ}

def AllStep (S : State Agent α) : Prop := ∀ i, FiniteStep (S.rows i).density

theorem initial_allStep (Agent : Type*) (α : ℝ) : AllStep (initial Agent α) :=
  fun _ => cell_finiteStep 0 1 1

theorem advance_allStep (S : State Agent α) (hα : 0 < α) (j : Agent)
    (r : ℝ) (hlr : S.frontier < r) (hr : r < 1) (hs : AllStep S) :
    AllStep (advance S hα j r hlr hr) := by
  intro i
  by_cases hij : i = j
  · subst i
    rw [advance_fixed_row]
    exact hs j
  · change FiniteStep (if i = j then S.rows i else
      (S.rows i).rebuilt S.frontier r (-((1+α)/α)*S.tail j)).density
    rw [ite_eq_right hij]
    exact rebuilt_finiteStep (S.rows i) _ _ _ (hs i)

end EnvyFreeResearch.Full.MixedFiniteStep
