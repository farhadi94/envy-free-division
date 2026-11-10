import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolCostLedger
import EnvyFreeResearch.Full.RefinedUpperGlobalUnitEntry
import EnvyFreeResearch.Full.RefinedUpperGlobalUnitOutput

/-! The actual empty-history entry, finite global execution, and literal
finite-interval output on the closed unit domain. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperQueryPrograms Chores.QueryProgram IntervalOracle
variable {n : ℕ}

def unitInitial (policy : Policy n) : Phase n := .normalize (RefinedUpperGlobalUnit.execute policy)

def unitPrefixProgram (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n)) (t : ℕ) :
    QProgram n (Phase n) :=
  RefinedUpperGlobalUnit.program.bind (fun a => prefixProgram fallback chores (.normalize a) omega t)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)]

theorem unitInitial_valid (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (chores : Bool) : (unitInitial policy).Valid μ chores (Icc 0 1) := by
  have h := RefinedUpperGlobalUnit.entry_committed μ policy hpolicy (if chores then .chore else .cake)
  exact ⟨h.1,h.2,⟨fallback,Finset.mem_univ _⟩⟩

theorem unitPrefix_executes (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n)) (t : ℕ) :
    ∃ trace, Executes oracle (unitPrefixProgram fallback chores omega t) []
      (Phase.run (AdaptiveOracle.answer oracle) fallback chores (unitInitial (AdaptiveOracle.answer oracle)) t omega) trace ∧
      (Phase.run (AdaptiveOracle.answer oracle) fallback chores (unitInitial (AdaptiveOracle.answer oracle)) t omega).history=trace ∧
      trace.length ≤ 2*n + ∑ s ∈ Finset.range t,
        (Phase.run (AdaptiveOracle.answer oracle) fallback chores (unitInitial (AdaptiveOracle.answer oracle)) s omega).queryCap ∧
      (trace.map Prod.fst).countP isCut ≤ ∑ s ∈ Finset.range t,
        (Phase.run (AdaptiveOracle.answer oracle) fallback chores (unitInitial (AdaptiveOracle.answer oracle)) s omega).cutCap := by
  obtain ⟨boot,he,hboot,hqboot,hcboot⟩ := RefinedUpperGlobalUnit.program_executes (AdaptiveOracle.answer oracle)
  have hlegal : ∀ entry ∈ boot, Legal (Chores.measureProfile μ) entry.1 := by
    intro entry hm
    have hproj : boot.map Prod.fst=UpperInitialState.queries n := by
      rw [←hboot]
      exact UpperCircularStage.executeQueries_projection _ _ _
    apply UpperInitialState.queries_legal (Chores.measureProfile μ)
    rw [←hproj]
    exact List.mem_map.mpr ⟨entry,hm,rfl⟩
  have heboot := UpperQueryLegality.option_replay (Chores.measureProfile μ) oracle horacle he hlegal
  have hp := UpperQueryLegality.answer_admissible _ oracle horacle
  obtain ⟨tail,ht,hh,hq,hc,_⟩ := prefix_option_executes μ (Icc 0 1) chores _
    (unitInitial_valid μ (AdaptiveOracle.answer oracle) hp fallback chores) oracle horacle fallback omega t
  have hinit : (unitInitial (AdaptiveOracle.answer oracle)).history=boot := hboot
  rw [hinit] at ht hh
  refine ⟨boot++tail,?_,?_,?_,?_⟩
  · simpa only [unitPrefixProgram,List.nil_append] using heboot.bind
      (fun a => prefixProgram fallback chores (.normalize a) omega t) ht
  · exact hh
  · rw [List.length_append,hqboot]
    exact Nat.add_le_add_left hq _
  · rw [List.map_append,List.countP_append,hcboot,zero_add]
    exact hc

theorem unitRun_done_output (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n)) (t : ℕ) (a : Anchor n)
    (hdone : Phase.run policy fallback chores (unitInitial policy) t omega=.done a) :
    Pairwise (fun i j => Disjoint (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) i)
      (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)) ∧
      (⋃j, RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)=Icc 0 1 ∧
      GlobalCompletion.EnvyFree (if chores then .chore else .cake)
        (fun i j => (μ i).real (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)) := by
  apply RefinedUpperGlobalUnit.terminal_output μ chores a
  have hv := run_valid μ (Icc 0 1) chores _ (unitInitial_valid μ policy hpolicy fallback chores)
    policy hpolicy fallback t omega
  rw [hdone] at hv
  exact hv

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
