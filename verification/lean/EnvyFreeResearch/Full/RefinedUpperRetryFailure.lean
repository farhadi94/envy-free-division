import EnvyFreeResearch.Full.RefinedUpperFirstBadFinite
import EnvyFreeResearch.Full.RefinedUpperBatchUnroll

/-! Actual batch rejection is covered by a first bad endpoint or exhaustion
through good rejected attempts. The cover is proved for the literal executor. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperRetryFailure
open UpperCircularStage UpperStageMeasurable UpperCorrectionLoop RefinedUpperCorrectionRetries
  RefinedUpperBatchUnroll UpperSnapshotRepetition RefinedUpperFirstBad RefinedUpperFirstBadFinite
abbrev Circle := UpperCircular.Circle
variable {n : ℕ}

def next (policy : Policy n) (job : Job n) (s : LoopState n) (start : Circle) : LoopState n :=
  reopen (step policy s (job, start)).2

def again (policy : Policy n) (job : Job n) (bad : LoopState n → Circle → Bool)
    (s : LoopState n) (start : Circle) : Bool :=
  !bad s start && (step policy s (job, start)).1

theorem next_measurable (policy : Policy n) (hp : MeasurablePolicy policy) (job : Job n) :
    Measurable (Function.uncurry (next policy job)) :=
  reopen_measurable.comp (measurable_snd.comp ((step_measurable policy hp).comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))))

theorem again_measurable (policy : Policy n) (hp : MeasurablePolicy policy) (job : Job n)
    (bad : LoopState n → Circle → Bool) (hb : Measurable (Function.uncurry bad)) :
    Measurable (Function.uncurry (again policy job bad)) :=
  (measurable_of_countable (fun b : Bool × Bool => !b.1 && b.2)).comp
    (hb.prodMk (measurable_fst.comp ((step_measurable policy hp).comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))))

theorem failure_cover (policy : Policy n) (job : Job n) (bad : LoopState n → Circle → Bool)
    (r : ℕ) (s : LoopState n) (tape : Fin r → Circle) (ho : s.stopped = false)
    (hf : (batch policy job s tape).stopped = true) :
    hit (next policy job) bad (again policy job bad) r s (pack r tape) ∨
      failed (next policy job) (again policy job bad) r s (pack r tape) := by
  induction r generalizing s with
  | zero => exact Or.inr trivial
  | succ r ih =>
    by_cases hb : bad s (tape 0) = true
    · exact Or.inl (Or.inl hb)
    · have hb0 : bad s (tape 0) = false := Bool.eq_false_iff.mpr hb
      rw [batch_succ policy job s tape ho] at hf
      by_cases hr : (step policy s (job, tape 0)).1 = true
      · rw [if_pos hr] at hf
        have hg : again policy job bad s (tape 0) = true := by simp [again, hb0, hr]
        have hi := ih (next policy job s (tape 0)) (fun i => tape i.succ) rfl hf
        rcases hi with hi | hi
        · exact Or.inl (Or.inr ⟨hg, hi⟩)
        · exact Or.inr ⟨hg, hi⟩
      · rw [if_neg hr] at hf
        simp [reopen] at hf

/-- A finite independent packet has failure probability at most the first-bad
fixed-point allowance plus the geometric good-exhaustion term. -/
theorem failure_probability (policy : Policy n) (hp : MeasurablePolicy policy) (job : Job n)
    (bad : LoopState n → Circle → Bool) (hb : Measurable (Function.uncurry bad))
    (Inv : LoopState n → Prop)
    (hnext : ∀ s d, Inv s → again policy job bad s d = true → Inv (next policy job s d))
    (a b B : ℝ≥0∞)
    (hbad : ∀ s, Inv s → (volume : Measure Circle) {d | bad s d = true} ≤ a)
    (hagain : ∀ s, Inv s → (volume : Measure Circle) {d | again policy job bad s d = true} ≤ b)
    (hfixed : a + B * b ≤ B)
    (r : ℕ) (s : LoopState n) (hs : Inv s) (ho : s.stopped = false) :
    UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r
      {tape | (batch policy job s tape).stopped = true} ≤ B + b ^ r := by
  have hsub : {tape | (batch policy job s tape).stopped = true} ⊆
      {tape | hit (next policy job) bad (again policy job bad) r s (pack r tape)} ∪
      {tape | failed (next policy job) (again policy job bad) r s (pack r tape)} := by
    intro tape ht
    exact failure_cover policy job bad r s tape ho ht
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  exact add_le_add
    (hit_bound volume (next policy job) bad (again policy job bad) (next_measurable policy hp job)
      hb (again_measurable policy hp job bad hb) Inv hnext a b B hbad hagain hfixed r s hs)
    (exhaustion_bound volume (next policy job) (again policy job bad) (next_measurable policy hp job)
      (again_measurable policy hp job bad hb) Inv hnext b hagain r s hs)

end EnvyFreeResearch.Full.RefinedUpperRetryFailure
