import EnvyFreeResearch.Full.UpperSnapshotRepetitionInvariant

/-!
# First-bad-event accounting for adaptive correction retries

The invariant is required only until the first bad endpoint. A good rejected
attempt preserves it. A fixed-point bound sums the geometric probability of
reaching another attempt, so the bad-endpoint charge has no retry-count factor.
The state may contain the complete query history.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace EnvyFreeResearch.Full.RefinedUpperFirstBad

open UpperSnapshotRepetition

variable {State Draw : Type} [MeasurableSpace State] [MeasurableSpace Draw]

/-- `again` is the event that the current attempt is good and rejected. -/
def hit (next : State → Draw → State) (bad again : State → Draw → Bool) :
    (m : ℕ) → State → Tape Draw m → Prop
  | 0, _, _ => False
  | m + 1, s, t => bad s t.1 = true ∨ (again s t.1 = true ∧ hit next bad again m (next s t.1) t.2)

theorem hit_joint_measurable (next : State → Draw → State) (bad again : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next)) (hb : Measurable (Function.uncurry bad))
    (ha : Measurable (Function.uncurry again)) (m : ℕ) :
    MeasurableSet {p : State × Tape Draw m | hit next bad again m p.1 p.2} := by
  induction m with
  | zero => simp only [hit, Set.ofPred_false]; exact MeasurableSet.empty
  | succ m ih =>
    have hsd : Measurable (fun p : State × (Draw × Tape Draw m) => (p.1, p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hnext : Measurable (fun p : State × (Draw × Tape Draw m) =>
        (next p.1 p.2.1, p.2.2)) :=
      (hn.comp hsd).prodMk (measurable_snd.comp measurable_snd)
    exact (measurableSet_eq_fun (hb.comp hsd) measurable_const).union
      ((measurableSet_eq_fun (ha.comp hsd) measurable_const).inter (ih.preimage hnext))

/-- The bound is uniform in the number of retries. In the application,
`a` is the per-attempt bad-endpoint bound, `b=1/4`, and `B=4a/3`. -/
theorem hit_le_fixed_point (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (bad again : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next)) (hb : Measurable (Function.uncurry bad))
    (ha : Measurable (Function.uncurry again))
    (Inv : State → Prop) (hnext : ∀ s d, Inv s → again s d = true → Inv (next s d))
    (a b B : ℝ≥0∞)
    (hbad : ∀ s, Inv s → rho {d | bad s d = true} ≤ a)
    (hagain : ∀ s, Inv s → rho {d | again s d = true} ≤ b)
    (hfixed : a + B * b ≤ B)
    (m : ℕ) (s : State) (hs : Inv s) :
    law rho m {t | hit next bad again m s t} ≤ B := by
  induction m generalizing s with
  | zero => simp [hit]
  | succ m ih =>
    have hm : MeasurableSet {t : Tape Draw (m + 1) | hit next bad again (m + 1) s t} :=
      (hit_joint_measurable next bad again hn hb ha (m + 1)).preimage
        (measurable_const.prodMk measurable_id)
    have hbs : MeasurableSet {d | bad s d = true} :=
      measurableSet_eq_fun hb.of_uncurry_left measurable_const
    have has : MeasurableSet {d | again s d = true} :=
      measurableSet_eq_fun ha.of_uncurry_left measurable_const
    change (rho.prod (law rho m)) {t | hit next bad again (m + 1) s t} ≤ B
    rw [Measure.prod_apply hm]
    calc
      _ ≤ ∫⁻ d, ({d | bad s d = true}.indicator (fun _ => (1 : ℝ≥0∞))) d +
          ({d | again s d = true}.indicator (fun _ => B)) d ∂rho := by
        apply lintegral_mono
        intro d
        by_cases hbd : bad s d = true
        · simp [hit, hbd]
        · by_cases had : again s d = true
          · simpa [hit, hbd, had] using ih (next s d) (hnext s d hs had)
          · simp [hit, hbd, had]
      _ = rho {d | bad s d = true} + B * rho {d | again s d = true} := by
        rw [lintegral_add_left (measurable_const.indicator hbs),
          lintegral_indicator_const hbs, lintegral_indicator_const has, one_mul]
      _ ≤ a + B * b := add_le_add (hbad s hs) (mul_le_mul' le_rfl (hagain s hs))
      _ ≤ B := hfixed

/-- Surviving every attempt without either acceptance or a bad endpoint has
geometrically small probability. This uses the same reached-state invariant. -/
theorem exhaustion_le (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (again : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next)) (ha : Measurable (Function.uncurry again))
    (Inv : State → Prop) (hnext : ∀ s d, Inv s → again s d = true → Inv (next s d))
    (b : ℝ≥0∞) (hagain : ∀ s, Inv s → rho {d | again s d = true} ≤ b)
    (m : ℕ) (s : State) (hs : Inv s) :
    law rho m {t | failed next again m s t} ≤ b ^ m :=
  failure_geometric_invariant rho next again hn ha Inv hnext b hagain m s hs

end EnvyFreeResearch.Full.RefinedUpperFirstBad
