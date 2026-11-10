import EnvyFreeResearch.Full.RefinedUpperShrinkLegality

/-! Rejected attempts retain their complete query history while the physical
input domain is unchanged. Restarting therefore preserves its exact cache. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperShrink
open UpperShrink
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage RefinedUpperRepairProgram

def restart (origin : State n) (result : PhysicalResult n k) : State n :=
  ⟨origin.cells,result.2.1.history⟩

theorem restart_domain (origin : State n) (result : PhysicalResult n k) :
    domain (restart origin result).cells=domain origin.cells := rfl

variable {n k : ℕ} [Nonempty (Fin k)] (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (ho : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (G : ℝ) (hG : 1 ≤ G)
  (hmax : G ≤ (2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(k-1))

include hinj ho hpositive hG hmax in
theorem restart_wellFormed (policy : Policy n)
    (hp : Admissible (Chores.measureProfile μ) policy) (p : RefinedUpperRepair.Tape n k) :
    WellFormed μ (restart origin (execute policy (by omega) chores active origin G p)) := by
  have ht := final_history_truthful μ hk chores active hinj origin ho hpositive G hG hmax policy hp p
  obtain ⟨trace,_,hh,_,_⟩ := program_cost policy (by omega) chores active hinj origin G hG p
  apply UpperShrinkCarve.wellFormed_history_extend μ origin.cells origin.history _ ho ht
  rw [hh]
  exact List.subset_append_left _ _

include hinj ho hpositive hG hmax in
theorem restart_recorded_total (policy : Policy n)
    (hp : Admissible (Chores.measureProfile μ) policy) (p : RefinedUpperRepair.Tape n k) (i : Fin n) :
    total (restart origin (execute policy (by omega) chores active origin G p)) i = total origin i := by
  rw [total_correct μ _ (restart_wellFormed μ hk chores active hinj origin ho hpositive G hG hmax policy hp p),
    total_correct μ origin ho]
  rfl

end EnvyFreeResearch.Full.RefinedUpperShrink
