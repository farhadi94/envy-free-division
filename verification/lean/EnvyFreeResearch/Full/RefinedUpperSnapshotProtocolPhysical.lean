import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolRepair

/-! The actual cached margin check certifies a physical Snapshot witness.
Under a candidate contrast bound, the same ordinary fresh Repair trial passes
this check with probability greater than 31/64 on its original random tape. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotRepair UpperSnapshotContrast UpperRepairPreparationChecks
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n))
  (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
  (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
  (holdHistory : ∀ j, (old j).history ⊆ origin.history)

include hpolicy hinj hgood hpositive hold hnear holdpair holdbuffer holdHistory

theorem success_facts (gamma : ℝ) (p : RefinedUpperRepair.Tape n k)
    (hs : (execute policy hk chores active gamma origin old p).2.2 = false) :
    RefinedUpperRepairProgram.SuccessFacts μ chores active origin old
      (execute policy hk chores active gamma origin old p) := by
  have hp := (finish_accepted (by omega) chores active gamma origin old
    (RefinedUpperRepair.execute policy hk chores active origin old p)).mp hs
  have he := finish_success_eq (by omega) chores active gamma origin old
    (RefinedUpperRepair.execute policy hk chores active origin old p) hs
  change RefinedUpperRepairProgram.SuccessFacts μ chores active origin old
    (finish (by omega) chores active gamma origin old (RefinedUpperRepair.execute policy hk chores active origin old p))
  dsimp only [finish]
  rw [he]
  exact RefinedUpperRepair.success_facts μ policy hpolicy hk chores active hinj origin hgood hpositive old hold hnear
    holdpair holdbuffer holdHistory p ((passes_iff _ _ _ _ _).mp hp).1

theorem success_margin (gamma : ℝ) (p : RefinedUpperRepair.Tape n k)
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
    (RefinedUpperRepair.execute policy hk chores active origin old p) hs
  have hp : passes (by omega) chores active gamma (execute policy hk chores active gamma origin old p) = true := by
    change passes _ _ _ _ (finish _ _ _ _ _ _ _) = true
    dsimp only [finish]
    rw [he]
    exact (finish_accepted _ _ _ _ _ _ _).mp hs
  have hr (i : Fin k) : 0 < (μ (active i)).real
      (domain (execute policy hk chores active gamma origin old p).2.1.cells) :=
    lt_trans (mul_pos (by norm_num) (hpositive i)) (hf.residue_mass i).1
  exact ⟨_,_,checked_physical μ (by omega) chores active _ hf.allocation_wellFormed
    hf.residue_wellFormed hr gamma hp⟩

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
