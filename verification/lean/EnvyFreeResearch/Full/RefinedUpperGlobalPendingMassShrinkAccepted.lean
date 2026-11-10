import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalPendingMassShrink

/-! The actual accepted Shrink call preserves the accumulated EF allocation
and gives positive, quantitatively controlled buffer rows. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperComponentAssembly UpperZeroRows
  UpperCircularStage GlobalCompletion
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
  [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 3 ≤ p.anchor.active.card) (chores : Bool)
  (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
  (G : ℝ) (hG : 1 ≤ G)
  (hmax : G ≤ (2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1))
  (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
  (haccept : (p.shrinkResult policy (by omega) chores G tape).2.2=false)
include hp hpolicy hk hpositive hG hmax haccept

theorem acceptShrink_activeEF
    (hprior : ActiveEF (if chores then .chore else .cake) (value μ p.shrunk) p.anchor.active) :
    ActiveEF (if chores then .chore else .cake)
      (value μ (p.acceptShrink policy (by omega) chores G tape).shrunk) p.anchor.active := by
  have facts := RefinedUpperShrink.success_facts μ policy hpolicy hk (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive G hG hmax chores tape haccept
  let r := p.shrinkResult policy (by omega) chores G tape
  have hef : EnvyFree (if chores then .chore else .cake)
      (fun i j => (μ (enumerate p.anchor.active i)).real (domain (r.1 j).cells)) := by
    intro i j
    have he := facts.1.envyFree i j
    cases chores <;> simp only [Bool.false_eq_true, ↓reduceIte,margin] at he ⊢ <;>
      change _ ≤ _ at he <;> dsimp [r,Pending.shrinkResult] <;> linarith
  apply pending_addShrink_activeEF μ p _ _ hp.shrunk_sep _ _ hprior
  · exact extendPieces_activeEF μ _ p.anchor.active r.1 r.2.1.history hef
  · rw [extendPieces_domain]
    exact facts.2.1

theorem acceptShrink_residue_bounds (i : Fin p.anchor.active.card) :
    3*(μ (enumerate p.anchor.active i)).real (domain p.buffer.cells)/(8*G) ≤
      (μ (enumerate p.anchor.active i)).real
        (domain (p.acceptShrink policy (by omega) chores G tape).buffer.cells) ∧
    (μ (enumerate p.anchor.active i)).real
        (domain (p.acceptShrink policy (by omega) chores G tape).buffer.cells) ≤
      (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells)/G := by
  have facts := RefinedUpperShrink.success_facts μ policy hpolicy hk (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.buffer_wf hpositive G hG hmax chores tape haccept
  exact facts.2.2 i

theorem acceptShrink_positive (i : Fin p.anchor.active.card) :
    0 < (μ (enumerate p.anchor.active i)).real
      (domain (p.acceptShrink policy (by omega) chores G tape).buffer.cells) := by
  have hl := (acceptShrink_residue_bounds μ whole p hp policy hpolicy hk chores hpositive
    G hG hmax tape haccept i).1
  have hg : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hfrac : 0 < 3*(μ (enumerate p.anchor.active i)).real (domain p.buffer.cells)/(8*G) :=
    div_pos (mul_pos (by norm_num) (hpositive i)) (mul_pos (by norm_num) hg)
  exact hfrac.trans_le hl

theorem acceptShrink_positive_active (i : Fin n) (hi : i ∈ p.anchor.active) :
    0 < (μ i).real (domain (p.acceptShrink policy (by omega) chores G tape).buffer.cells) := by
  obtain ⟨a,rfl⟩ := enumerate_preimage _ i hi
  exact acceptShrink_positive μ whole p hp policy hpolicy hk chores hpositive G hG hmax tape haccept a

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
