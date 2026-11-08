import EnvyFreeResearch.Full.UpperSnapshotIntegrationReserve

/-! A physical unequal-foreign/equal-cutter pair supplies a fresh Repair
contrast. The reserve normalizer is bounded from the actual reserve check;
no successful Repair margin is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotContrast UpperRepairSnapshot UpperDomainDifference UpperLogicalIsolation
variable {n k : ℕ}

theorem equal_cutter_contrast (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Fin k → Fin n)
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (reserve : State n) (hreserve : WellFormed μ reserve) (foreign cutter first second : Fin k)
    (U A B theta : ℝ) (hU : 0 < U) (hA : 0 ≤ A) (hB : 0 < B) (htheta : 0 < theta)
    (hreservepos : 0 < (μ (active foreign)).real (domain reserve.cells))
    (hreserveupper : (μ (active foreign)).real (domain reserve.cells) ≤ 3*theta/2*(B*U))
    (hforeign : A*U ≤ (μ (active foreign)).real (domain (old first).cells) -
      (μ (active foreign)).real (domain (old second).cells))
    (hcutter : (μ (active cutter)).real (domain (old first).cells) =
      (μ (active cutter)).real (domain (old second).cells)) :
    (2*A/(3*B))/theta ≤ contrast (oldMatrix active old reserve) foreign cutter first second := by
  have hh : contrast (oldMatrix active old reserve) foreign cutter first second =
      ((μ (active foreign)).real (domain (old first).cells) - (μ (active foreign)).real (domain (old second).cells)) /
        (μ (active foreign)).real (domain reserve.cells) := by
    unfold contrast oldMatrix
    simp only [total_correct μ _ (hold first),total_correct μ _ (hold second),total_correct μ _ hreserve]
    rw [hcutter]
    ring
  rw [hh]
  apply (le_div_iff₀ hreservepos).mpr
  have hscale := mul_le_mul_of_nonneg_left hreserveupper (show 0 ≤ (2*A/(3*B))/theta by positivity)
  have halg : ((2*A/(3*B))/theta) * (3*theta/2*(B*U)) = A*U := by
    field_simp
    <;> ring
  rw [halg] at hscale
  exact hscale.trans hforeign

end EnvyFreeResearch.Full.UpperSnapshotProtocol
