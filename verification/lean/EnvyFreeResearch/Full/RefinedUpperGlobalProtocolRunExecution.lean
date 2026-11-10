import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolLegality

/-! Every finite prefix of the actual infinite-tape run is an ordinary legal
oracle program. Its complete query history accounts for every attempted stage. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperQueryPrograms Chores.QueryProgram IntervalOracle
variable {n : ℕ}

def prefixProgram (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) : ℕ → QProgram n (Phase n)
  | 0 => .returned initial
  | t+1 => (prefixProgram fallback chores initial omega t).bind
      (fun phase => phase.stepProgram fallback chores (omega t))

theorem prefix_option_executes (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (initial : Phase n) (hinit : initial.Valid μ chores whole)
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (fallback : Fin n) (omega : Stream (Universal n)) (t : ℕ) :
    ∃ trace, Executes oracle (prefixProgram fallback chores initial omega t) initial.history
      (Phase.run (AdaptiveOracle.answer oracle) fallback chores initial t omega) trace ∧
      (Phase.run (AdaptiveOracle.answer oracle) fallback chores initial t omega).history=initial.history++trace ∧
      trace.length ≤ ∑ s ∈ Finset.range t,
        (Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).queryCap ∧
      (trace.map Prod.fst).countP isCut ≤ ∑ s ∈ Finset.range t,
        (Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).cutCap ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧
        ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  induction t with
  | zero => exact ⟨[],Executes.returned _ _,by simp [Phase.run,RefinedUpperGlobalRun.run,RefinedUpperGlobalRun.finiteRun],
      by simp,by simp,by simp⟩
  | succ t ih =>
    obtain ⟨before,hbefore,hhbefore,hqbefore,hcbefore,hlbefore⟩ := ih
    have hvalid := run_valid μ whole chores initial hinit (AdaptiveOracle.answer oracle)
      (UpperQueryLegality.answer_admissible _ oracle horacle) fallback t omega
    obtain ⟨after,hafter,hhafter,hqafter,hcafter,hlafter⟩ := step_option_executes μ whole chores _
      hvalid oracle horacle fallback (omega t)
    rw [hhbefore] at hafter
    refine ⟨before++after,hbefore.bind _ hafter,?_,?_,?_,?_⟩
    · change (Phase.step (AdaptiveOracle.answer oracle) fallback chores
        (Phase.run (AdaptiveOracle.answer oracle) fallback chores initial t omega) (omega t)).history=
        initial.history++(before++after)
      rw [hhafter,hhbefore,List.append_assoc]
    · rw [List.length_append,Finset.sum_range_succ]
      exact Nat.add_le_add hqbefore hqafter
    · rw [List.map_append,List.countP_append,Finset.sum_range_succ]
      exact Nat.add_le_add hcbefore hcafter
    · intro entry he
      rcases List.mem_append.mp he with he | he
      · exact hlbefore entry he
      · exact hlafter entry he

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
