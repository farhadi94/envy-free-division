import EnvyFreeResearch.Full.RefinedUpperRetryFailure

/-! Analytic stopping within one actual retry packet. Only good rejected
attempts and good accepted attempts carry analytic invariants forward. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperBatchChancePacket
open UpperCircularStage UpperStageMeasurable UpperCorrectionLoop RefinedUpperCorrectionRetries
  RefinedUpperBatchUnroll UpperSnapshotRepetition RefinedUpperFirstBad RefinedUpperFirstBadFinite
abbrev Circle := UpperCircular.Circle
variable {n : ℕ}

/-- A first bad endpoint, or exhaustion entirely through good rejections.
Bad accepted attempts are included in the first alternative. -/
def risk (policy : Policy n) (job : Job n) (bad : LoopState n → Circle → Bool)
    (r : ℕ) (s : LoopState n) (t : Fin r → Circle) : Prop :=
  hit (RefinedUpperRetryFailure.next policy job) bad
    (RefinedUpperRetryFailure.again policy job bad) r s (pack r t) ∨
  failed (RefinedUpperRetryFailure.next policy job)
    (RefinedUpperRetryFailure.again policy job bad) r s (pack r t)

theorem risk_measurable (policy : Policy n) (hp : MeasurablePolicy policy) (job : Job n)
    (bad : LoopState n → Circle → Bool) (hb : Measurable (Function.uncurry bad)) (r : ℕ) :
    MeasurableSet {p : LoopState n × (Fin r → Circle) | risk policy job bad r p.1 p.2} := by
  have hn := RefinedUpperRetryFailure.next_measurable policy hp job
  have ha := RefinedUpperRetryFailure.again_measurable policy hp job bad hb
  have hpack := (pack_preserves (volume : Measure Circle) r).measurable
  exact ((hit_joint_measurable _ _ _ hn hb ha r).union
    (failed_joint_measurable _ _ hn ha r)).preimage
      (measurable_fst.prodMk (hpack.comp measurable_snd))

/-- No analytic risk means that the literal executor accepts a good proposal.
The target invariant can differ from the retry invariant. -/
theorem safe_batch (policy : Policy n) (job : Job n)
    (bad : LoopState n → Circle → Bool) (Inv After : LoopState n → Prop)
    (hretry : ∀ s d, Inv s → s.stopped = false → bad s d = false →
      (step policy s (job, d)).1 = true → Inv (RefinedUpperRetryFailure.next policy job s d))
    (haccept : ∀ s d, Inv s → s.stopped = false → bad s d = false →
      (step policy s (job, d)).1 = false → After (RefinedUpperRetryFailure.next policy job s d))
    (r : ℕ) (s : LoopState n) (t : Fin r → Circle) (hs : Inv s) (ho : s.stopped = false)
    (hgood : ¬ risk policy job bad r s t) :
    (batch policy job s t).stopped = false ∧ After (batch policy job s t) := by
  induction r generalizing s with
  | zero => exact False.elim (hgood (Or.inr trivial))
  | succ r ih =>
    have hbad : bad s (t 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      exact hgood (Or.inl (Or.inl hb))
    rw [batch_succ policy job s t ho]
    by_cases hr : (step policy s (job, t 0)).1 = true
    · rw [if_pos hr]
      have ha : RefinedUpperRetryFailure.again policy job bad s (t 0) = true := by
        simp [RefinedUpperRetryFailure.again, hbad, hr]
      have htail : ¬ risk policy job bad r (RefinedUpperRetryFailure.next policy job s (t 0))
          (fun i => t i.succ) := by
        intro ht
        rcases ht with ht | ht
        · exact hgood (Or.inl (Or.inr ⟨ha, ht⟩))
        · exact hgood (Or.inr ⟨ha, ht⟩)
      exact ih _ _ (hretry s (t 0) hs ho hbad hr) rfl htail
    · rw [if_neg hr]
      exact ⟨rfl, haccept s (t 0) hs ho hbad (Bool.eq_false_iff.mpr hr)⟩

theorem stopped_subset_risk (policy : Policy n) (job : Job n)
    (bad : LoopState n → Circle → Bool) (r : ℕ) (s : LoopState n)
    (ho : s.stopped = false) :
    {t | (batch policy job s t).stopped = true} ⊆ {t | risk policy job bad r s t} := by
  intro t ht
  exact RefinedUpperRetryFailure.failure_cover policy job bad r s t ho ht

/-- The reached-state hypotheses are required only on open good prefixes. -/
theorem risk_probability (policy : Policy n) (hp : MeasurablePolicy policy) (job : Job n)
    (bad : LoopState n → Circle → Bool) (hb : Measurable (Function.uncurry bad))
    (Inv : LoopState n → Prop)
    (hretry : ∀ s d, Inv s → s.stopped = false → bad s d = false →
      (step policy s (job, d)).1 = true → Inv (RefinedUpperRetryFailure.next policy job s d))
    (a b B : ℝ≥0∞)
    (hbad : ∀ s, Inv s → s.stopped = false → (volume : Measure Circle) {d | bad s d = true} ≤ a)
    (hagain : ∀ s, Inv s → s.stopped = false →
      (volume : Measure Circle) {d | RefinedUpperRetryFailure.again policy job bad s d = true} ≤ b)
    (hfixed : a + B * b ≤ B)
    (r : ℕ) (s : LoopState n) (hs : Inv s) (ho : s.stopped = false) :
    UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r
      {t | risk policy job bad r s t} ≤ B + b ^ r := by
  let Good : LoopState n → Prop := fun s => Inv s ∧ s.stopped = false
  have hn : ∀ s d, Good s → RefinedUpperRetryFailure.again policy job bad s d = true →
      Good (RefinedUpperRetryFailure.next policy job s d) := by
    intro s d hs ha
    have hh : bad s d = false ∧ (step policy s (job, d)).1 = true := by
      simpa only [RefinedUpperRetryFailure.again, Bool.and_eq_true, Bool.not_eq_true'] using ha
    exact ⟨hretry s d hs.1 hs.2 hh.1 hh.2, rfl⟩
  apply (measure_union_le _ _).trans
  exact add_le_add
    (hit_bound volume _ _ _ (RefinedUpperRetryFailure.next_measurable policy hp job) hb
      (RefinedUpperRetryFailure.again_measurable policy hp job bad hb) Good hn a b B
      (fun s hs => hbad s hs.1 hs.2) (fun s hs => hagain s hs.1 hs.2) hfixed r s ⟨hs, ho⟩)
    (exhaustion_bound volume _ _ (RefinedUpperRetryFailure.next_measurable policy hp job)
      (RefinedUpperRetryFailure.again_measurable policy hp job bad hb) Good hn b
      (fun s hs => hagain s hs.1 hs.2) r s ⟨hs, ho⟩)

end EnvyFreeResearch.Full.RefinedUpperBatchChancePacket
