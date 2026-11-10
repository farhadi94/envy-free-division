import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolSafety
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolSmallReady

/-! The actual candidate passes the executable buffer and near-EF guard. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity UpperSnapshotSmall
  UpperStageMeasurable UpperRepairPreparationChecks UpperRepairParameters
variable {n m k : ℕ} {Generated : Type*} [Nonempty (Fin k)]

theorem actual_small_candidate_safe
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) 
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (D t : ℝ) (hD : 0<D)
    (hsmall : D < RefinedUpperRepair.nearError n/16)
    (htdef : t=(1-(8/RefinedUpperRepair.nearError n)*D)/(k:ℝ))
    (first second : UpperSnapshotSmall.Circle) (points : Generated → ℝ)
    (hfirst : ∀ j, ∃ e, points e=(firstRun policy origin (active cutter) cuts selected t first).1 j)
    (hsecond : ∀ j, ∃ e, points e=(secondRun (J:=k) policy origin (active cutter) cuts selected t first second).1 j)
    (eps : ℝ) (heps : eps ≤ 1/2)
    (htau4 : RefinedUpperRepair.nearError n ≤ 4)
    (hinterp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts points eps)
    (hmax : ∀ i, distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter ≤ D)
 :
    let packet := actualAllocation (by omega : 0<k) policy origin (active cutter) cuts selected t first second
    candidateSafe chores active packet.1 packet.2.1 = true := by
  let tau := RefinedUpperRepair.nearError n
  have htau : 0 < tau := by
    change 0 < RefinedUpperRepair.nearError n
    unfold RefinedUpperRepair.nearError RefinedUpperParameterCounts.oldError
    positivity [UpperRepairParameters.s_positive (scale_large n)]
  have hkreal : (2:ℝ) ≤ k := by exact_mod_cast hk
  have htcheck := UpperSnapshotProtocol.small_amount_checks tau D (k:ℝ) htau hD hsmall hkreal
  rw [← htdef] at htcheck
  obtain ⟨ht,_,ht1,hfit,_,hremain⟩ := htcheck
  let packet := actualAllocation (by omega : 0<k) policy origin (active cutter) cuts selected t first second
  have hw := actual_allocation_wellFormed μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
    cuts hzero hmono hsep selected t ht ht1 (by omega : 0<k) first second
  have hd (i : Fin k) : 0 ≤ distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbudgets (i : Fin k) := UpperSnapshotProtocol.small_error_budgets tau D _ eps htau htau4 hD.le (hd i) (hmax i) heps
  have hready (i : Fin k) := actualAllocation_ready μ policy hpolicy active origin hgood hpositive cutter cuts
    hzero hone hmono hsep selected t ht ht1 hfit first second points hfirst hsecond eps tau htau.le hinterp
    (fun j => by rw [hremain]; exact (hbudgets j).1)
    (fun j => by rw [hremain]; exact (hbudgets j).2) (by omega : 0<k) i
  apply decide_eq_true
  refine ⟨fun i => (hready i).2.1,?_⟩
  intro i j
  cases chores
  · exact (le_abs_self _).trans ((hready i).2.2 j i)
  · exact (le_abs_self _).trans ((hready i).2.2 i j)

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
