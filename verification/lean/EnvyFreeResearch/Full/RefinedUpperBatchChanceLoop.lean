import EnvyFreeResearch.Full.RefinedUpperBatchChancePacket

/-! First-failing-packet accounting on the actual recipient batch loop.
After a bad packet the analytic event stops; its successor need not be safe. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperBatchChanceLoop
open UpperCircularStage UpperStageMeasurable UpperCorrectionLoop RefinedUpperCorrectionRetries
  UpperSnapshotRepetition RefinedUpperFirstBadFinite
abbrev Circle := UpperCircular.Circle
variable {n r : ℕ}

/-- Analytic first failure along literal physical batch transitions. -/
def risk (policy : Policy n) : (k : ℕ) → (Fin k → Job n) →
    (Fin k → LoopState n → Circle → Bool) → LoopState n → Tape (Fin r → Circle) k → Prop
  | 0, _, _, _, _ => False
  | k + 1, jobs, bad, s, t =>
      RefinedUpperBatchChancePacket.risk policy (jobs 0) (bad 0) r s t.1 ∨
      (¬ RefinedUpperBatchChancePacket.risk policy (jobs 0) (bad 0) r s t.1 ∧
        risk policy k (fun i => jobs i.succ) (fun i => bad i.succ)
          (batch policy (jobs 0) s t.1) t.2)

theorem risk_measurable (policy : Policy n) (hp : MeasurablePolicy policy) (k : ℕ)
    (jobs : Fin k → Job n) (bad : Fin k → LoopState n → Circle → Bool)
    (hb : ∀ i, Measurable (Function.uncurry (bad i))) :
    MeasurableSet {p : LoopState n × Tape (Fin r → Circle) k | risk policy k jobs bad p.1 p.2} := by
  induction k with
  | zero => exact MeasurableSet.empty
  | succ k ih =>
    have hhead : Measurable (fun p : LoopState n × Tape (Fin r → Circle) (k + 1) =>
        (p.1, p.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hlocal := (RefinedUpperBatchChancePacket.risk_measurable policy hp (jobs 0) (bad 0) (hb 0) r).preimage hhead
    have hbatch : Measurable (fun p : LoopState n × Tape (Fin r → Circle) (k + 1) =>
        batch policy (jobs 0) p.1 p.2.1) :=
      (batch_measurable policy hp).comp
        ((measurable_const.prodMk measurable_fst).prodMk (measurable_fst.comp measurable_snd))
    exact hlocal.union (hlocal.compl.inter ((ih (fun i => jobs i.succ) (fun i => bad i.succ)
      (fun i => hb i.succ)).preimage (hbatch.prodMk (measurable_snd.comp measurable_snd))))

/-- Only the complement of a packet's risk must preserve the next invariant. -/
theorem probability (policy : Policy n) (hp : MeasurablePolicy policy) (k : ℕ)
    (jobs : Fin k → Job n) (bad : Fin k → LoopState n → Circle → Bool)
    (hb : ∀ i, Measurable (Function.uncurry (bad i)))
    (Safe : Fin (k + 1) → LoopState n → Prop)
    (hpreserve : ∀ i s t, Safe i.castSucc s →
      ¬ RefinedUpperBatchChancePacket.risk policy (jobs i) (bad i) r s t →
      Safe i.succ (batch policy (jobs i) s t))
    (C : ℝ≥0∞)
    (hchance : ∀ i s, Safe i.castSucc s →
      UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r
        {t | RefinedUpperBatchChancePacket.risk policy (jobs i) (bad i) r s t} ≤ C)
    (s : LoopState n) (hs : Safe 0 s) :
    law (UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r) k
      {t | risk policy k jobs bad s t} ≤ (k : ℝ≥0∞) * C := by
  induction k generalizing s with
  | zero => simp [risk]
  | succ k ih =>
    let rho := UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r
    let E := {t : Fin r → Circle | RefinedUpperBatchChancePacket.risk policy (jobs 0) (bad 0) r s t}
    have hE : MeasurableSet E :=
      (RefinedUpperBatchChancePacket.risk_measurable policy hp (jobs 0) (bad 0) (hb 0) r).preimage
        (measurable_const.prodMk measurable_id)
    have hm : MeasurableSet {t : Tape (Fin r → Circle) (k + 1) | risk policy (k + 1) jobs bad s t} :=
      (risk_measurable policy hp (k + 1) jobs bad hb).preimage
        (measurable_const.prodMk measurable_id)
    change (rho.prod (law rho k)) {t | risk policy (k + 1) jobs bad s t} ≤ _
    rw [Measure.prod_apply hm]
    calc
      _ ≤ ∫⁻ t, E.indicator (fun _ => (1 : ℝ≥0∞)) t + (k : ℝ≥0∞) * C ∂rho := by
        apply lintegral_mono
        intro t
        by_cases ht : t ∈ E
        · simp only [E, Set.mem_setOf_eq] at ht
          simp [risk, ht, E]
        · change ¬ RefinedUpperBatchChancePacket.risk policy (jobs 0) (bad 0) r s t at ht
          have hsafe := hpreserve 0 s t hs ht
          have hi := ih (fun i => jobs i.succ) (fun i => bad i.succ) (fun i => hb i.succ)
            (fun i => Safe i.succ)
            (fun i s t hs ht => hpreserve i.succ s t hs ht)
            (fun i s hs => hchance i.succ s hs) (batch policy (jobs 0) s t) hsafe
          simpa [risk, E, ht, rho] using hi
      _ = rho E + (k : ℝ≥0∞) * C := by
        rw [lintegral_add_left (measurable_const.indicator hE), lintegral_indicator_const hE]
        simp
      _ ≤ C + (k : ℝ≥0∞) * C := add_le_add (hchance 0 s hs) le_rfl
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * C := by push_cast; ring

/-- Transfer to the literal finite packet vector used by the physical loop. -/
theorem probability_finite (policy : Policy n) (hp : MeasurablePolicy policy) (k : ℕ)
    (jobs : Fin k → Job n) (bad : Fin k → LoopState n → Circle → Bool)
    (hb : ∀ i, Measurable (Function.uncurry (bad i)))
    (Safe : Fin (k + 1) → LoopState n → Prop)
    (hpreserve : ∀ i s t, Safe i.castSucc s →
      ¬ RefinedUpperBatchChancePacket.risk policy (jobs i) (bad i) r s t →
      Safe i.succ (batch policy (jobs i) s t))
    (C : ℝ≥0∞)
    (hchance : ∀ i s, Safe i.castSucc s →
      UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r
        {t | RefinedUpperBatchChancePacket.risk policy (jobs i) (bad i) r s t} ≤ C)
    (s : LoopState n) (hs : Safe 0 s) :
    UpperAdaptiveProduct.tapeLaw (UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r) k
      {t | risk policy k jobs bad s (pack k t)} ≤ (k : ℝ≥0∞) * C := by
  have hm : MeasurableSet {t : Tape (Fin r → Circle) k | risk policy k jobs bad s t} :=
    (risk_measurable policy hp k jobs bad hb).preimage (measurable_const.prodMk measurable_id)
  rw [show {t | risk policy k jobs bad s (pack k t)} =
      pack k ⁻¹' {t | risk policy k jobs bad s t} from rfl,
    (pack_preserves (UpperAdaptiveProduct.tapeLaw (volume : Measure Circle) r) k).measure_preimage
      hm.nullMeasurableSet]
  exact probability policy hp k jobs bad hb Safe hpreserve C hchance s hs

/-- Deterministic invariant transport on the complement of the stopped
analytic event, along exactly the states returned by the physical loop. -/
theorem safe_run (policy : Policy n) (k : ℕ)
    (jobs : Fin k → Job n) (bad : Fin k → LoopState n → Circle → Bool)
    (Safe : Fin (k + 1) → LoopState n → Prop)
    (hpreserve : ∀ i s t, Safe i.castSucc s →
      ¬ RefinedUpperBatchChancePacket.risk policy (jobs i) (bad i) r s t →
      Safe i.succ (batch policy (jobs i) s t))
    (s : LoopState n) (hs : Safe 0 s) (t : Fin k → Fin r → Circle)
    (hgood : ¬ risk policy k jobs bad s (pack k t)) :
    Safe (Fin.last k) (RefinedUpperBatchLoop.run policy jobs s t).2 := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih =>
    have hhead : ¬ RefinedUpperBatchChancePacket.risk policy (jobs 0) (bad 0) r s (t 0) :=
      fun hh => hgood (Or.inl hh)
    have htail : ¬ risk policy k (fun i => jobs i.succ) (fun i => bad i.succ)
        (batch policy (jobs 0) s (t 0)) (pack k (fun i => t i.succ)) :=
      fun ht => hgood (Or.inr ⟨hhead, ht⟩)
    exact ih (fun i => jobs i.succ) (fun i => bad i.succ) (fun i => Safe i.succ)
      (fun i s t hs ht => hpreserve i.succ s t hs ht)
      (batch policy (jobs 0) s (t 0)) (hpreserve 0 s (t 0) hs hhead)
      (fun i => t i.succ) htail

end EnvyFreeResearch.Full.RefinedUpperBatchChanceLoop
