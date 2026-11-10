import EnvyFreeResearch.Full.RefinedUpperRepairSnapshotProbability
import EnvyFreeResearch.Full.UpperSnapshotProtocolRepair

/-! The existing recorded margin check, applied to the actual new Repair,
accepts with probability above 31/64 once its concrete failure estimate and
the candidate's old-label contrast are supplied. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotContrast UpperSnapshotRepair RefinedUpperRepairSnapshot UpperRepairPreparationChecks
variable {n k : ℕ} [Nonempty (Fin k)]

theorem acceptance_probability_of_failure_bound
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n))
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history ⊆ origin.history)
    (chosen : Preparation n k → Selection k) (hchosen : Measurable chosen)
    (hfailure : (RefinedUpperRepair.law n k).real (Success policy hk chores active origin old)ᶜ < 1/64)
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hbaseline : ∀ p ∈ Success policy hk chores active origin old,
      Lambda ≤ contrast (prepOld policy active origin old (view p).1)
        (chosen (view p).1).1.1 (chosen (view p).1).1.2
        (chosen (view p).1).2.1 (chosen (view p).1).2.2) :
    31/64 < (RefinedUpperRepair.law n k).real {p |
      (UpperSnapshotProtocol.finish (by omega) chores active (Lambda/8) origin old
        (RefinedUpperRepair.execute policy hk chores active origin old p)).2.2 = false} := by
  have hm := original_trial_margin_of_failure_bound μ policy hpolicy hmeas hk chores active hinj
    origin hgood hpositive old hold hnear holdpair holdbuffer holdHistory chosen hchosen hfailure Lambda hLambda hbaseline
  apply hm.trans_le
  apply measureReal_mono _ (measure_ne_top _ _)
  intro p hp
  obtain ⟨hs,a,b,_,_,hab⟩ := hp
  have hf := RefinedUpperRepair.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear
    holdpair holdbuffer holdHistory p hs
  have hr (i : Fin k) : 0 < (μ (active i)).real
      (domain (RefinedUpperRepair.execute policy hk chores active origin old p).2.1.cells) :=
    lt_trans (mul_pos (by norm_num) (hpositive i)) (hf.residue_mass i).1
  apply (UpperSnapshotProtocol.finish_accepted _ _ _ _ _ _ _).mpr
  exact UpperSnapshotRepair.passes_of_witness μ (by omega) chores active _ hf.allocation_wellFormed
    hf.residue_wellFormed hr (Lambda/8) (div_pos hLambda (by norm_num)) hs a b hab

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
