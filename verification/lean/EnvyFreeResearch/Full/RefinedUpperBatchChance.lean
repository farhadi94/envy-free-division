import EnvyFreeResearch.Full.RefinedUpperBatchChanceLoop

/-! Full first-bad probability bound for the literal k-recipient retry loop.
All local assumptions concern good prefixes, including accepted proposals.
No invariant is required after an accepted bad endpoint. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperBatchChance
open UpperCircularStage UpperStageMeasurable UpperCorrectionLoop RefinedUpperCorrectionRetries
  UpperSnapshotRepetition RefinedUpperFirstBadFinite
abbrev Circle := UpperCircular.Circle
variable {n r k : ℕ}

/-- The event stops analytically at the first bad or exhausted batch even
if the physical executor would continue after accepting a bad proposal. -/
def failure (policy : Policy n) (jobs : Fin k → Job n)
    (bad : Fin k → LoopState n → Circle → Bool) (s : LoopState n) :
    Set (Fin k → Fin r → Circle) :=
  {t | RefinedUpperBatchChanceLoop.risk policy k jobs bad s (pack k t)}

theorem failure_measurable (policy : Policy n) (hp : MeasurablePolicy policy)
    (jobs : Fin k → Job n) (bad : Fin k → LoopState n → Circle → Bool)
    (hb : ∀ i, Measurable (Function.uncurry (bad i))) (s : LoopState n) :
    MeasurableSet (failure (r := r) policy jobs bad s) :=
  ((RefinedUpperBatchChanceLoop.risk_measurable (r := r) policy hp k jobs bad hb).preimage
    (measurable_const.prodMk measurable_id)).preimage
      (pack_preserves (UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r) k).measurable

/-- Uniform per-attempt bad and good-rejection bounds compose over all
actual history-dependent batches. The invariant may depend on the recipient
index and is transported only along good attempts. -/
theorem bound (policy : Policy n) (hp : MeasurablePolicy policy)
    (jobs : Fin k → Job n) (bad : Fin k → LoopState n → Circle → Bool)
    (hb : ∀ i, Measurable (Function.uncurry (bad i)))
    (Safe : Fin (k + 1) → LoopState n → Prop)
    (hretry : ∀ i s d, Safe i.castSucc s → s.stopped = false → bad i s d = false →
      (step policy s (jobs i, d)).1 = true →
      Safe i.castSucc (RefinedUpperRetryFailure.next policy (jobs i) s d))
    (haccept : ∀ i s d, Safe i.castSucc s → s.stopped = false → bad i s d = false →
      (step policy s (jobs i, d)).1 = false →
      Safe i.succ (RefinedUpperRetryFailure.next policy (jobs i) s d))
    (a b B : ℝ≥0∞)
    (hbad : ∀ i s, Safe i.castSucc s → s.stopped = false →
      (volume : Measure Circle) {d | bad i s d = true} ≤ a)
    (hagain : ∀ i s, Safe i.castSucc s → s.stopped = false →
      (volume : Measure Circle) {d | RefinedUpperRetryFailure.again policy (jobs i) (bad i) s d = true} ≤ b)
    (hfixed : a + B * b ≤ B)
    (s : LoopState n) (hs : Safe 0 s) (ho : s.stopped = false) :
    UpperAdaptiveProduct.tapeLaw (UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r) k
      (failure policy jobs bad s) ≤ (k : ℝ≥0∞) * (B + b ^ r) ∧
    ∀ t : Fin k → Fin r → Circle, t ∉ failure policy jobs bad s →
      (RefinedUpperBatchLoop.run policy jobs s t).2.stopped = false ∧
      Safe (Fin.last k) (RefinedUpperBatchLoop.run policy jobs s t).2 := by
  let Good : Fin (k + 1) → LoopState n → Prop := fun i s => Safe i s ∧ s.stopped = false
  have hpreserve : ∀ i s (t : Fin r → Circle), Good i.castSucc s →
      ¬ RefinedUpperBatchChancePacket.risk policy (jobs i) (bad i) r s t →
      Good i.succ (batch policy (jobs i) s t) := by
    intro i s t hs ht
    have h := RefinedUpperBatchChancePacket.safe_batch policy (jobs i) (bad i)
      (Safe i.castSucc) (Safe i.succ) (hretry i) (haccept i) r s t hs.1 hs.2 ht
    exact ⟨h.2, h.1⟩
  refine ⟨?_, ?_⟩
  · exact RefinedUpperBatchChanceLoop.probability_finite policy hp k jobs bad hb Good hpreserve
      (B + b ^ r) (fun i s hs => RefinedUpperBatchChancePacket.risk_probability policy hp
        (jobs i) (bad i) (hb i) (Safe i.castSucc) (hretry i) a b B
        (hbad i) (hagain i) hfixed r s hs.1 hs.2) s ⟨hs, ho⟩
  · intro t ht
    have h := RefinedUpperBatchChanceLoop.safe_run policy k jobs bad Good hpreserve s ⟨hs, ho⟩ t ht
    exact ⟨h.2, h.1⟩

/-- In particular, the actual physical loop's stopped outcome has the same
bound. This follows from the analytic event, not an invariant on bad paths. -/
theorem stopped_probability (policy : Policy n) (hp : MeasurablePolicy policy)
    (jobs : Fin k → Job n) (bad : Fin k → LoopState n → Circle → Bool)
    (hb : ∀ i, Measurable (Function.uncurry (bad i)))
    (Safe : Fin (k + 1) → LoopState n → Prop)
    (hretry : ∀ i s d, Safe i.castSucc s → s.stopped = false → bad i s d = false →
      (step policy s (jobs i, d)).1 = true →
      Safe i.castSucc (RefinedUpperRetryFailure.next policy (jobs i) s d))
    (haccept : ∀ i s d, Safe i.castSucc s → s.stopped = false → bad i s d = false →
      (step policy s (jobs i, d)).1 = false →
      Safe i.succ (RefinedUpperRetryFailure.next policy (jobs i) s d))
    (a b B : ℝ≥0∞)
    (hbad : ∀ i s, Safe i.castSucc s → s.stopped = false →
      (volume : Measure Circle) {d | bad i s d = true} ≤ a)
    (hagain : ∀ i s, Safe i.castSucc s → s.stopped = false →
      (volume : Measure Circle) {d | RefinedUpperRetryFailure.again policy (jobs i) (bad i) s d = true} ≤ b)
    (hfixed : a + B * b ≤ B)
    (s : LoopState n) (hs : Safe 0 s) (ho : s.stopped = false) :
    UpperAdaptiveProduct.tapeLaw (UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r) k
      {t | (RefinedUpperBatchLoop.run policy jobs s t).2.stopped = true} ≤
        (k : ℝ≥0∞) * (B + b ^ r) := by
  have h := bound (r := r) policy hp jobs bad hb Safe hretry haccept a b B hbad hagain hfixed s hs ho
  apply (measure_mono (show {t | (RefinedUpperBatchLoop.run policy jobs s t).2.stopped = true} ⊆
    failure policy jobs bad s from ?_)).trans h.1
  intro t ht
  by_contra hn
  have hopen := (h.2 t hn).1
  rw [ht] at hopen
  contradiction

end EnvyFreeResearch.Full.RefinedUpperBatchChance

#print axioms EnvyFreeResearch.Full.RefinedUpperBatchChance.bound

#print axioms EnvyFreeResearch.Full.RefinedUpperBatchChance.stopped_probability
