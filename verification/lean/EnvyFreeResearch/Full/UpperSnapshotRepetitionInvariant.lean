import EnvyFreeResearch.Full.UpperSnapshotRepetitionMeasurable
import EnvyFreeResearch.Full.UpperSnapshotRepetitionCounts

/-! Amplification only requires the chance estimate at valid reached states. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition

theorem failure_geometric_invariant {State Draw : Type}
    [MeasurableSpace State] [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next))
    (hr : Measurable (Function.uncurry reject))
    (Inv : State → Prop)
    (hnext : ∀ s d, Inv s → reject s d=true → Inv (next s d))
    (b : ℝ≥0∞) (hchance : ∀ s, Inv s → rho {d | reject s d=true} ≤ b)
    (m : ℕ) (s : State) (hs : Inv s) :
    law rho m {t | failed next reject m s t} ≤ b^m := by
  induction m generalizing s with
  | zero =>
    letI : IsProbabilityMeasure (law rho 0) := law_probability rho 0
    simpa only [failed,Set.setOf_true,pow_zero] using
      (le_of_eq (measure_univ : law rho 0 Set.univ=1))
  | succ m ih =>
    have hm : MeasurableSet {t | failed next reject (m+1) s t} :=
      (failed_joint_measurable next reject hn hr (m+1)).preimage
        (measurable_const.prodMk measurable_id)
    change (rho.prod (law rho m)) {t | failed next reject (m+1) s t} ≤ _
    rw [Measure.prod_apply hm]
    calc
      _ ≤ ∫⁻ d, ({d | reject s d=true}.indicator (fun _ => b^m)) d ∂rho := by
        apply lintegral_mono
        intro d
        by_cases hd : reject s d=true
        · simpa [failed, Set.preimage_setOf_eq, hd] using ih (next s d) (hnext s d hs hd)
        · simp [failed, Set.preimage_setOf_eq, hd]
      _ = b^m * rho {d | reject s d=true} := by
        rw [lintegral_indicator_const (measurableSet_eq_fun hr.of_uncurry_left measurable_const)]
      _ ≤ b^m*b := mul_le_mul' le_rfl (hchance s hs)
      _ = b^(m+1) := (pow_succ b m).symm

theorem sixteen_trials_failure {State Draw : Type}
    [MeasurableSpace State] [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (hn : Measurable (Function.uncurry next))
    (hr : Measurable (Function.uncurry reject))
    (Inv : State → Prop)
    (hnext : ∀ s d, Inv s → reject s d=true → Inv (next s d))
    (k : ℕ) (hk : 1 ≤ k)
    (hchance : ∀ s, Inv s → rho {d | reject s d=true} ≤ ENNReal.ofReal (1-1/(8*(k:ℝ))))
    (s : State) (hs : Inv s) :
    law rho (16*k) {t | failed next reject (16*k) s t} ≤ ENNReal.ofReal ((1:ℝ)/4) := by
  have hkpos : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hbase : 0 ≤ 1-1/(8*(k:ℝ)) := by
    have h : 1/(8*(k:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by norm_cast; omega)
    linarith
  calc
    _ ≤ (ENNReal.ofReal (1-1/(8*(k:ℝ))))^(16*k) :=
      failure_geometric_invariant rho next reject hn hr Inv hnext _ hchance _ s hs
    _ = ENNReal.ofReal ((1-1/(8*(k:ℝ)))^(16*k)) := (ENNReal.ofReal_pow hbase (16*k)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (sixteen_trials_quarter k hk)

end EnvyFreeResearch.Full.UpperSnapshotRepetition
