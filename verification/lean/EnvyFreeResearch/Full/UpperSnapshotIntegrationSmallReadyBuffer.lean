import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationReady
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationPartition
import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationGapReady
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallParameters
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallRepair

/-! The actual small candidate's buffer is controlled by its observed row
variation. This bound is derived from the same supported interpolation event
used for its Near guarantee. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity UpperSnapshotSmall
variable {n m k : ℕ} {Generated : Type*} [Nonempty (Fin k)]

theorem actual_small_buffer_upper
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (hfit : (k:ℝ)*t<1) (first second : UpperSnapshotSmall.Circle)
    (points : Generated → ℝ)
    (hfirst : ∀ j, ∃ e, points e=(firstRun policy origin (active cutter) cuts selected t first).1 j)
    (hsecond : ∀ j, ∃ e, points e=(secondRun (J:=k) policy origin (active cutter) cuts selected t first second).1 j)
    (eps D K : ℝ) (heps : eps ≤ 1/2) (hD : 0 ≤ D)
    (hremain : 1-k*t=K*D)
    (hinterp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts points eps)
    (hk : 0<k) (i : Fin k)
    (hmax : distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter ≤ D) :
    (μ (active i)).real (domain (actualAllocation hk policy origin (active cutter) cuts selected t first second).2.1.cells) ≤
      ((K+2)*D)*(μ (active i)).real (domain origin.cells) := by
  let packet := actualAllocation hk policy origin (active cutter) cuts selected t first second
  have hw := actual_allocation_wellFormed μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
    cuts hzero hmono hsep selected t ht ht1 hk first second
  have he := (actualAllocation_normalized_errors (fun i => μ (active i)) policy origin hgood.2.1 (active cutter)
    cuts hzero hone hmono hsep selected t first second points hfirst hsecond eps hinterp hk i cutter
    (hpositive i) (hpositive cutter)).2
  rw [← total_correct μ _ hw.2.1 (active cutter),
    actual_buffer_cutter_mass μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
      cuts hzero hmono hsep selected t ht ht1 hk hfit first second,
    mul_div_cancel_right₀ (1-k*t) (hpositive cutter).ne',hremain] at he
  have hd : 0 ≤ distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have herr : (1/2+eps)*distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter ≤ D := by
    nlinarith
  apply (div_le_iff₀ (hpositive i)).mp
  have hu := (abs_le.mp he).2
  nlinarith

end EnvyFreeResearch.Full.UpperSnapshotProtocol
