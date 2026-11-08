import EnvyFreeResearch.Full.UpperSnapshotRepetitionEndpoints

/-! Endpoint charges accumulate by conditional expectation at each reached
history. Neither the endpoints within a circle nor later outputs are assumed
independent. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
variable {State Draw : Type} {L : ℕ}

theorem endpointCharge_expectation [MeasurableSpace State] [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (u : ℝ → ℝ≥0∞)
    (hn : Measurable (Function.uncurry next)) (hr : Measurable (Function.uncurry reject))
    (hp : ∀ j, Measurable (fun p : State × Draw => points p.1 p.2 j)) (hu : Measurable u)
    (Inv : State → Prop) (hnext : ∀ s d, Inv s → reject s d=true → Inv (next s d))
    (B : ℝ≥0∞) (hcharge : ∀ s, Inv s → (∫⁻ d, ∑ j, u (points s d j) ∂rho) ≤ B)
    (m : ℕ) (s : State) (hs : Inv s) :
    (∫⁻ tape, endpointCharge next reject points u m s tape ∂law rho m) ≤ (m:ℝ≥0∞)*B := by
  induction m generalizing s with
  | zero => simp [endpointCharge]
  | succ m ih =>
    letI : IsProbabilityMeasure (law rho m) := law_probability rho m
    have hm : Measurable (fun tape : Tape Draw (m+1) => endpointCharge next reject points u (m+1) s tape) :=
      (endpointCharge_measurable next reject points u hn hr hp hu (m+1)).comp
        (measurable_const.prodMk measurable_id)
    change (∫⁻ tape, endpointCharge next reject points u (m+1) s tape ∂rho.prod (law rho m)) ≤ _
    rw [lintegral_prod _ hm.aemeasurable]
    calc
      _ ≤ ∫⁻ d, (∑ j, u (points s d j)) + (m:ℝ≥0∞)*B ∂rho := by
        apply lintegral_mono
        intro d
        by_cases hd : reject s d=true
        · simp only [endpointCharge,hd,ite_true,lintegral_add_left measurable_const,
            lintegral_const,measure_univ,mul_one]
          exact add_le_add_right (ih (next s d) (hnext s d hs hd)) _
        · simp [endpointCharge,hd]
      _ = (∫⁻ d, ∑ j, u (points s d j) ∂rho)+(m:ℝ≥0∞)*B := by
        rw [lintegral_add_right _ measurable_const]
        simp
      _ ≤ B+(m:ℝ≥0∞)*B := add_le_add_left (hcharge s hs) _
      _ = ((m+1:ℕ):ℝ≥0∞)*B := by simp [Nat.cast_add,add_mul,add_comm]

theorem endpoints_expectation [MeasurableSpace State] [MeasurableSpace Draw]
    (rho : Measure Draw) [IsProbabilityMeasure rho]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (u : ℝ → ℝ≥0∞) (hu0 : u 0=0)
    (hn : Measurable (Function.uncurry next)) (hr : Measurable (Function.uncurry reject))
    (hp : ∀ j, Measurable (fun p : State × Draw => points p.1 p.2 j)) (hu : Measurable u)
    (Inv : State → Prop) (hnext : ∀ s d, Inv s → reject s d=true → Inv (next s d))
    (B : ℝ≥0∞) (hcharge : ∀ s, Inv s → (∫⁻ d, ∑ j, u (points s d j) ∂rho) ≤ B)
    (m : ℕ) (s : State) (hs : Inv s) :
    (∫⁻ tape, ((endpoints next reject points m s tape).map u).sum ∂law rho m) ≤ (m:ℝ≥0∞)*B := by
  simp only [endpoints_charge next reject points u hu0]
  exact endpointCharge_expectation rho next reject points u hn hr hp hu Inv hnext B hcharge m s hs

end EnvyFreeResearch.Full.UpperSnapshotRepetition
