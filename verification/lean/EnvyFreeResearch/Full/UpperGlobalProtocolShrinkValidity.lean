import EnvyFreeResearch.Full.UpperGlobalProtocolValidity
import EnvyFreeResearch.Full.UpperGlobalPendingMassShrinkAccepted
import EnvyFreeResearch.Full.UpperGlobalProtocolSelectionCommit

/-! The shared invariant across accepted shrinking and finite transfer. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage
variable {n : ℕ}

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)

theorem Pending.Basic.positive_local (hp : p.Basic μ chores whole) (i : Fin p.anchor.active.card) :
    0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells) := by
  rw [← total_correct μ p.buffer hp.physical.buffer_wf]
  exact hp.positive _ (enumerate_mem _ i)

theorem acceptShrink_basic [Nonempty (Fin p.anchor.active.card)] (hp : p.Basic μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (G : ℝ) (hG : 1 ≤ G)
    (hmax : G ≤ (2/UpperShrinkPrecision.theta n)*(8/UpperRepair.nearError n)^(p.anchor.active.card-1))
    (tape : UpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by have := hp.population; omega) chores G tape).2.2=false) :
    (p.acceptShrink policy (by have := hp.population; omega) chores G tape).Basic μ chores whole := by
  have hpos := hp.positive_local μ whole chores p
  have hphys := acceptShrink_physical μ whole p hp.physical policy hpolicy hp.population chores hpos
    G hG hmax tape haccept
  refine ⟨hphys,hp.anchor_valid,hp.population,hp.snapshot_ef,?_,?_,hp.strong⟩
  · exact acceptShrink_activeEF μ whole p hp.physical policy hpolicy hp.population chores hpos
      G hG hmax tape haccept hp.shrunk_ef
  · intro i hi
    rw [total_correct μ _ hphys.buffer_wf]
    exact acceptShrink_positive_active μ whole p hp.physical policy hpolicy hp.population chores hpos
      G hG hmax tape haccept i hi

theorem transferCandidate_basic (hp : p.Basic μ chores whole)
    (candidate : UpperGlobal.Transfer.Selection.Candidate p.anchor.active.card) :
    (p.transferCandidate candidate).Basic μ chores whole := by
  have hphys := transferCandidate_physical μ whole p hp.physical candidate
  cases candidate <;> exact ⟨hphys,hp.anchor_valid,hp.population,hp.snapshot_ef,
    hp.shrunk_ef,hp.positive,hp.strong⟩

end EnvyFreeResearch.Full.UpperGlobalPhysical
