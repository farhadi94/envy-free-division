import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationInterpolation
import EnvyFreeResearch.Full.UpperRepairPreparationChecks

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity
variable {n m J : ℕ} {Generated : Type*} [Nonempty (Fin J)]

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin J → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin J) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (hfit : (J:ℝ)*t<1) (first second : Circle)
    (points : Generated → ℝ)
    (hfirst : ∀ j, ∃ e, points e=(firstRun policy origin (active cutter) cuts selected t first).1 j)
    (hsecond : ∀ j, ∃ e, points e=(secondRun (J:=J) policy origin (active cutter) cuts selected t first second).1 j)
    (eps tau : ℝ) (htau : 0 ≤ tau)
    (hinterp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts points eps)
    (hsmall : ∀ i, (1/2+eps)*distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter ≤ (1-J*t)/2)
    (hbudget : ∀ i, 2*((1/2+eps)*distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter) ≤ tau*((1-J*t)/2))
include hpolicy hgood hpositive hzero hone hmono hsep ht ht1 hfit hfirst hsecond htau hinterp hsmall hbudget

theorem actualAllocation_ready (hJ : 0<J) (i : Fin J) :
    let packet := actualAllocation hJ policy origin (active cutter) cuts selected t first second
    (1-J*t)/2*(μ (active i)).real (domain origin.cells) ≤ total packet.2.1 (active i) ∧
    0 < total packet.2.1 (active i) ∧
    ∀ a b, |total (packet.1 a) (active i)-total (packet.1 b) (active i)| ≤ tau*total packet.2.1 (active i) := by
  let packet := actualAllocation hJ policy origin (active cutter) cuts selected t first second
  have hw := actual_allocation_wellFormed μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
    cuts hzero hmono hsep selected t ht ht1 hJ first second
  have he := actualAllocation_normalized_errors (fun i => μ (active i)) policy origin hgood.2.1 (active cutter)
    cuts hzero hone hmono hsep selected t first second points hfirst hsecond eps hinterp hJ i cutter (hpositive i) (hpositive cutter)
  have hshares : ∀ a, |total (packet.1 a) (active i)/(μ (active i)).real (domain origin.cells)-t| ≤
      (1/2+eps)*distance (physicalRows (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter := by
    intro a
    have hh := he.1 a
    rw [← total_correct μ _ (hw.1 a) (active i),← total_correct μ _ (hw.1 a) (active cutter),
      actual_allocation_cutter_mass μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
        cuts hzero hmono hsep selected t ht ht1 hJ hfit first second a,
      mul_div_cancel_right₀ t (hpositive cutter).ne'] at hh
    exact hh
  have hbuffer : |total packet.2.1 (active i)/(μ (active i)).real (domain origin.cells)-(1-J*t)| ≤
      (1/2+eps)*distance (physicalRows (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter := by
    have hh := he.2
    rw [← total_correct μ _ hw.2.1 (active i),← total_correct μ _ hw.2.1 (active cutter),
      actual_buffer_cutter_mass μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
        cuts hzero hmono hsep selected t ht ht1 hJ hfit first second,
      mul_div_cancel_right₀ (1-J*t) (hpositive cutter).ne'] at hh
    exact hh
  exact near_checks_of_normalized_errors (fun a => total (packet.1 a) (active i))
    (total packet.2.1 (active i)) _ t (1-J*t) _ tau (hpositive i) (by linarith) htau
    (hsmall i) (hbudget i) hshares hbuffer

end EnvyFreeResearch.Full.UpperSnapshotSmall
