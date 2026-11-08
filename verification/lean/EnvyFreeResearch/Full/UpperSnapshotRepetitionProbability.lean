import Mathlib

/-! Fresh-product amplification with a state-dependent rejection event.
The state can contain the entire preceding oracle history. No independence
of the successive outputs is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition

@[reducible] def Tape (Draw : Type) : ℕ → Type
  | 0 => Unit
  | m+1 => Draw × Tape Draw m

@[reducible] instance tapeMeasurable (Draw : Type) [MeasurableSpace Draw] :
    (m : ℕ) → MeasurableSpace (Tape Draw m)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | m+1 => @Prod.instMeasurableSpace Draw (Tape Draw m) _ (tapeMeasurable Draw m)

def law {Draw : Type} [MeasurableSpace Draw] (rho : Measure Draw) :
    (m : ℕ) → Measure (Tape Draw m)
  | 0 => Measure.dirac ()
  | m+1 => rho.prod (law rho m)

theorem law_probability {Draw : Type} [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho] :
    (m : ℕ) → IsProbabilityMeasure (law rho m)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | m+1 => by
    haveI := law_probability rho m
    exact inferInstanceAs (IsProbabilityMeasure (rho.prod (law rho m)))

instance instLawProbability {Draw : Type} [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho] (m : ℕ) :
    IsProbabilityMeasure (law rho m) := law_probability rho m

def failed {State Draw : Type} (next : State → Draw → State)
    (reject : State → Draw → Bool) : (m : ℕ) → State → Tape Draw m → Prop
  | 0, _, _ => True
  | m+1, s, t => reject s t.1=true ∧ failed next reject m (next s t.1) t.2

theorem failure_geometric {State Draw : Type} [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (b : ℝ≥0∞)
    (hmeas : ∀ m s, MeasurableSet {t | failed next reject m s t})
    (hreject : ∀ s, MeasurableSet {d | reject s d=true})
    (hchance : ∀ s, rho {d | reject s d=true} ≤ b)
    (m : ℕ) (s : State) : law rho m {t | failed next reject m s t} ≤ b^m := by
  induction m generalizing s with
  | zero =>
    letI : IsProbabilityMeasure (law rho 0) := law_probability rho 0
    simpa only [failed, Set.setOf_true, pow_zero] using
      (le_of_eq (measure_univ : law rho 0 Set.univ=1))
  | succ m ih =>
    change (rho.prod (law rho m)) {t | failed next reject (m+1) s t} ≤ _
    rw [Measure.prod_apply (hmeas (m+1) s)]
    calc
      _ ≤ ∫⁻ d, ({d | reject s d=true}.indicator (fun _ => b^m)) d ∂rho := by
        apply lintegral_mono
        intro d
        by_cases hd : reject s d=true
        · simpa [failed, Set.preimage_setOf_eq, hd] using ih (next s d)
        · simp [failed, Set.preimage_setOf_eq, hd]
      _ = b^m * rho {d | reject s d=true} := by
        rw [lintegral_indicator_const (hreject s)]
      _ ≤ b^m*b := mul_le_mul' le_rfl (hchance s)
      _ = b^(m+1) := (pow_succ b m).symm

end EnvyFreeResearch.Full.UpperSnapshotRepetition
