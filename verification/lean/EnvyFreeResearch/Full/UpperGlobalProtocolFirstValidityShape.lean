import EnvyFreeResearch.Full.UpperGlobalProtocolFirstValiditySelection

/-! An accepted actual first Shrink dispatches to a valid second Shrink or
final Repair. The finite selector succeeds from the saved Snapshot witness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage GlobalCompletion
open UpperGlobal.Transfer
variable {n : ℕ}

theorem firstShrinkAttempt_accepted_shape
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (chores : Bool) (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (tape : UpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by have := hp.population; omega) chores G tape).2.2=false) :
    ∃ next : Pending n, next.anchor=p.anchor ∧
      (p.firstShrinkAttempt policy (by have := hp.population; omega) chores G tape=.secondShrink next ∨
       p.firstShrinkAttempt policy (by have := hp.population; omega) chores G tape=.finalRepair next) := by
  obtain ⟨c,_,_,he⟩ := firstShrinkAttempt_accepted_selection μ whole chores p G hp policy hpolicy tape haccept
  rw [he]
  cases c with
  | commit alpha b h => exact ⟨(p.acceptShrink policy (by have := hp.population; omega) chores G tape).transferCandidate (.commit alpha b h),rfl,Or.inr rfl⟩
  | shrink b h => exact ⟨(p.acceptShrink policy (by have := hp.population; omega) chores G tape).transferCandidate (.shrink b h),rfl,Or.inl rfl⟩

end EnvyFreeResearch.Full.UpperGlobalPhysical
