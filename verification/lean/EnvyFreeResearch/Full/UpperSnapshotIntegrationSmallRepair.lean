import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallContrast
import EnvyFreeResearch.Full.UpperSnapshotIntegrationPhysical

/-! One fresh actual checked Repair accepts a verified small candidate with
probability greater than 31/64. All physical hypotheses here concern the
already constructed candidate, before any fresh Repair randomness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotContrast UpperRepairSnapshot UpperDomainDifference
  UpperRepairPreparationChecks UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem small_candidate_repair_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (buffer : State n) (hbuffer : WellFormed μ buffer)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain buffer.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active buffer old (UpperRepair.nearError n))
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain buffer.cells))
    (holdHistory : ∀ j, (old j).history ⊆ buffer.history)
    (foreign cutter first second : Fin k) (U A B : ℝ) (hU : 0 < U) (hA : 0 < A) (hB : 0 < B)
    (hbufferupper : (μ (active foreign)).real (domain buffer.cells) ≤ B*U)
    (hforeign : A*U ≤ (μ (active foreign)).real (domain (old first).cells) -
      (μ (active foreign)).real (domain (old second).cells))
    (hcutter : (μ (active cutter)).real (domain (old first).cells) =
      (μ (active cutter)).real (domain (old second).cells)) :
    31/64 < (UpperRepair.law n k).real
      {p | (execute policy hk chores active ((2*A/(3*B))/8) buffer old p).2.2 = false} := by
  have htheta : 0 < (UpperRepair.reserveMark n : ℝ) :=
    reserve_positive (scale_large n) (by exact_mod_cast logarithm_positive (scale_large n))
  apply acceptance_probability μ policy hpolicy hk chores active hinj buffer hbuffer hpositive old hold hnear
    holdpair holdbuffer holdHistory hmeas (fun _ => ((foreign,cutter),(first,second))) measurable_const
    (2*A/(3*B)) (by positivity)
  intro p hp
  have hr := original_reserve μ policy hpolicy hk chores active buffer hbuffer hpositive old p hp
  have hreserve := freshReserve_wellFormed μ policy hpolicy active buffer hbuffer hpositive (view p).1
  have hpos : 0 < (μ (active foreign)).real (domain (prepReserve policy active buffer (view p).1).cells) :=
    lt_of_lt_of_le (mul_pos (div_pos htheta (by norm_num)) (hpositive foreign)) (hr foreign).1
  have hu : (μ (active foreign)).real (domain (prepReserve policy active buffer (view p).1).cells) ≤
      3*(UpperRepair.reserveMark n : ℝ)/2*(B*U) :=
    (hr foreign).2.trans (mul_le_mul_of_nonneg_left hbufferupper (by positivity))
  exact equal_cutter_contrast μ active old hold (prepReserve policy active buffer (view p).1) hreserve
    foreign cutter first second U A B (UpperRepair.reserveMark n) hU hA.le hB htheta hpos hu hforeign hcutter
end EnvyFreeResearch.Full.UpperSnapshotProtocol
