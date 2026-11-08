import EnvyFreeResearch.Full.UpperSnapshotProtocolRepair

/-! The actual cached margin check certifies a physical Snapshot witness.
Under a candidate contrast bound, the same ordinary fresh Repair trial passes
this check with probability greater than 31/64 on its original random tape. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotRepair UpperSnapshotContrast UpperRepairPreparationChecks
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (UpperRepair.nearError n))
  (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
  (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (holdHistory : ∀ j, (old j).history ⊆ origin.history)

include hpolicy hinj hgood hpositive hold hnear holdpair holdbuffer holdHistory

theorem success_facts (gamma : ℝ) (p : UpperRepair.Tape n k)
    (hs : (execute policy hk chores active gamma origin old p).2.2 = false) :
    UpperRepairProgram.SuccessFacts μ chores active origin old
      (execute policy hk chores active gamma origin old p) := by
  have hp := (finish_accepted (by omega) chores active gamma origin old
    (UpperRepair.execute policy hk chores active origin old p)).mp hs
  have he := finish_success_eq (by omega) chores active gamma origin old
    (UpperRepair.execute policy hk chores active origin old p) hs
  change UpperRepairProgram.SuccessFacts μ chores active origin old
    (finish (by omega) chores active gamma origin old (UpperRepair.execute policy hk chores active origin old p))
  rw [he]
  exact UpperRepair.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear
    holdpair holdbuffer holdHistory p ((passes_iff _ _ _ _ _).mp hp).1

theorem success_margin (gamma : ℝ) (p : UpperRepair.Tape n k)
    (hs : (execute policy hk chores active gamma origin old p).2.2 = false) :
    ∃ a b : Fin k, a ≠ b ∧
      0 < physicalGap chores (fun i => μ (active i))
        (fun j => domain ((execute policy hk chores active gamma origin old p).1 j).cells) a b ∧
      gamma * (μ (active a)).real (domain (execute policy hk chores active gamma origin old p).2.1.cells) ≤
        physicalGap chores (fun i => μ (active i))
          (fun j => domain ((execute policy hk chores active gamma origin old p).1 j).cells) a b := by
  have hf := success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear
    holdpair holdbuffer holdHistory gamma p hs
  have he := finish_success_eq (by omega) chores active gamma origin old
    (UpperRepair.execute policy hk chores active origin old p) hs
  have hp : passes (by omega) chores active gamma (execute policy hk chores active gamma origin old p) = true := by
    change passes _ _ _ _ (finish _ _ _ _ _ _ _) = true
    rw [he]
    exact (finish_accepted _ _ _ _ _ _ _).mp hs
  have hr (i : Fin k) : 0 < (μ (active i)).real
      (domain (execute policy hk chores active gamma origin old p).2.1.cells) :=
    lt_trans (mul_pos (by norm_num) (hpositive i)) (hf.residue_mass i).1
  exact ⟨_,_,checked_physical μ (by omega) chores active _ hf.allocation_wellFormed
    hf.residue_wellFormed hr gamma hp⟩

theorem acceptance_probability (hmeas : MeasurablePolicy policy)
    (chosen : UpperRepairSnapshot.Preparation n k → Selection k) (hchosen : Measurable chosen)
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hbaseline : ∀ p ∈ UpperRepairSnapshot.Success policy hk chores active origin old,
      Lambda / (UpperRepair.reserveMark n : ℝ) ≤
        contrast (UpperRepairSnapshot.prepOld policy active origin old (UpperRepairSnapshot.view p).1)
          (chosen (UpperRepairSnapshot.view p).1).1.1 (chosen (UpperRepairSnapshot.view p).1).1.2
          (chosen (UpperRepairSnapshot.view p).1).2.1 (chosen (UpperRepairSnapshot.view p).1).2.2) :
    31 / 64 < (UpperRepair.law n k).real
      {p | (execute policy hk chores active (Lambda/8) origin old p).2.2 = false} := by
  have hm := UpperRepairSnapshot.original_trial_margin μ policy hpolicy hmeas hk chores active hinj
    origin hgood hpositive old hold hnear holdpair holdbuffer holdHistory chosen hchosen Lambda hLambda hbaseline
  apply hm.trans_le
  apply measureReal_mono _ (measure_ne_top _ _)
  intro p hp
  obtain ⟨hs,a,b,_,_,hab⟩ := hp
  have hf := UpperRepair.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear
    holdpair holdbuffer holdHistory p hs
  have hr (i : Fin k) : 0 < (μ (active i)).real
      (domain (UpperRepair.execute policy hk chores active origin old p).2.1.cells) :=
    lt_trans (mul_pos (by norm_num) (hpositive i)) (hf.residue_mass i).1
  apply (finish_accepted _ _ _ _ _ _ _).mpr
  exact passes_of_witness μ (by omega) chores active _ hf.allocation_wellFormed hf.residue_wellFormed hr
    (Lambda/8) (div_pos hLambda (by norm_num)) hs a b hab

end EnvyFreeResearch.Full.UpperSnapshotProtocol
