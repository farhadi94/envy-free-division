import EnvyFreeResearch.Full.UpperShrinkCarveRounds

/-! The actual starting color vectors are feasible, including zero target
fractions and the dummy. Thus the finite query ledger applies to initialized
carving without an input color-certificate assumption. -/
noncomputable section
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperCircularStage UpperQueryPrograms Chores.QueryProgram

theorem initial_fractions_valid {n k : ℕ} (origin : State n) (f : ℝ) (hf : 0 ≤ f)
    (hcapacity : (k : ℝ)*f ≤ 1) : (initial (k:=k) origin f).FractionsValid := by
  have hsum : (∑ _j : Fin k, f) ≤ 1 := by simpa using hcapacity
  intro p hp
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hp
  constructor
  · intro j
    have hb := UpperFloating.commonPlan_box (Cell:=Unit) (fun _j : Fin k => f) (fun _ => hf) hsum ((),j)
    cases j <;> simpa [UpperFloating.commonPlan] using hb
  · have hr := UpperFloating.commonPlan_row (fun _j : Fin k => f) ()
    simpa [UpperFloating.commonPlan] using hr

theorem initialized_query_bound (policy : Policy n) (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (J : ℕ) (origin : State n) (f : ℝ) (hf : 0 ≤ f) (hcapacity : (k : ℝ)*f ≤ 1) :
    (roundsExecute policy active normal J (initial origin f)).history.length ≤
      origin.history.length+J*k^3*(n+1) :=
  rounds_query_bound policy active normal J _ (initial_fractions_valid origin f hf hcapacity)

theorem initialized_cut_bound (policy : Policy n) (active : Fin k → Fin n) (normal : Fin k → ℝ)
    (J : ℕ) (origin : State n) (f : ℝ) (hf : 0 ≤ f) (hcapacity : (k : ℝ)*f ≤ 1) :
    cuts (roundsExecute policy active normal J (initial origin f)).history ≤ cuts origin.history+J*k^3 :=
  rounds_cut_bound policy active normal J _ (initial_fractions_valid origin f hf hcapacity)

end EnvyFreeResearch.Full.UpperShrinkCarve
