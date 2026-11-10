import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalOracleStability
import EnvyFreeResearch.Full.RefinedUpperGlobalOracleNext

/-! The least-observable-prefix selector agrees with every observable finite
prefix. Hence its choice of index has no effect on the actual next action. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.OracleNext
open RefinedUpperGlobalPhysical RefinedUpperGlobalTape UpperCircularStage OracleProtocol
variable {n : ℕ}

theorem observable_iff_stability (a : Action (Query n) (Phase n)) :
    observable a=true ↔ RefinedUpperGlobalOracleStability.Observable RefinedUpperGlobalOracleStability.Terminal a := by
  cases a <;> simp only [observable,RefinedUpperGlobalOracleStability.Observable,
    RefinedUpperGlobalOracleStability.Terminal,iff_self]

theorem prefixAction_stable (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n) (t s : ℕ) (hts : t ≤ s)
    (ht : observable (prefixAction fallback chores omega history t)=true) :
    prefixAction fallback chores omega history s=prefixAction fallback chores omega history t :=
  RefinedUpperGlobalOracleStability.unitPrefix_action_stable fallback chores omega history t s hts
    ((observable_iff_stability _).mp ht)

theorem observable_actions_eq (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n) (t s : ℕ)
    (ht : observable (prefixAction fallback chores omega history t)=true)
    (hs : observable (prefixAction fallback chores omega history s)=true) :
    prefixAction fallback chores omega history s=prefixAction fallback chores omega history t :=
  RefinedUpperGlobalOracleStability.unitPrefix_observable_actions_eq fallback chores omega history t s
    ((observable_iff_stability _).mp ht) ((observable_iff_stability _).mp hs)

theorem next_eq_prefixAction (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n) (t : ℕ)
    (ht : observable (prefixAction fallback chores omega history t)=true) :
    next fallback chores omega history=prefixAction fallback chores omega history t :=
  next_eq_of_observable fallback chores omega history t ht
    (fun s hs => observable_actions_eq fallback chores omega history t s ht hs)

end EnvyFreeResearch.Full.RefinedUpperGlobalRun.OracleNext
