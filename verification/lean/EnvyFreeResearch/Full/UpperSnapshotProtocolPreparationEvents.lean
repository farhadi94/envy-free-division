import EnvyFreeResearch.Full.UpperSnapshotProtocolLawProduct
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateZeroBound
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSmallProbability
import EnvyFreeResearch.Full.UpperSnapshotEndpointCandidateFailure

/-! Three actual preparation exceptions on the full original Snapshot tape.
Ignored branch coordinates are integrated out by measure-preserving maps;
only outer-measure inequalities are used for supported-union exceptions. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotCandidates UpperSnapshotEndpointAggregate UpperAggregateInterpolation UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

def preparationBadZero (policy : Policy n) (hk : 3 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) : Set (PreparationTape n k) :=
  {p | selectedDistance (by omega) (UpperGridCache.table policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) p.1) cutter=0 ∧
    (zeroExecute policy (by omega) chores active (UpperGridCache.aligned policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) p.1) cutter p.2.1).2.2=true}

def preparationBadCandidates (policy : Policy n) (hk : 3 ≤ k)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) : Set (PreparationTape n k) :=
  {p | smallBranch (by omega) policy active origin cutter (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.nearError n) p.1 ∧
    (UpperSnapshotEndpointCandidateFailure.packetResult (by omega) policy active origin cutter (UpperRepair.coarse n)
      (UpperRepair.fine n) (UpperRepair.nearError n) (p.1,p.2.2)).2=none}

def preparationBadInterpolation (μ : Fin n → Measure ℝ) (policy : Policy n) (hk : 3 ≤ k)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) : Set (PreparationTape n k) :=
  {p | BadSupportedRecordedUnion (fun i => μ (active i))
    (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
    (UpperGridMerge.cuts policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) p.1)
    (smallOriginalPoints (by omega) policy active origin cutter (UpperRepair.coarse n) (UpperRepair.fine n)
      (UpperRepair.nearError n) (p.1,p.2.2)) (snapshotAccuracy (scale n))}

theorem measurePreserving_preimage_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : MeasurePreserving f μ ν) (E : Set Y) :
    μ (f ⁻¹' E) ≤ ν E := by
  calc
    μ (f ⁻¹' E) ≤ μ.map f E := Measure.le_map_apply hf.measurable.aemeasurable E
    _ = ν E := by rw [hf.map_eq]

theorem preparation_bad_bounds
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (cutter : Fin k) :
    preparationLaw n k (preparationBadZero policy hk chores active origin cutter) ≤ ENNReal.ofReal ((1:ℝ)/64) ∧
    preparationLaw n k (preparationBadCandidates policy hk active origin cutter) ≤ ENNReal.ofReal ((1:ℝ)/4) ∧
    preparationLaw n k (preparationBadInterpolation μ policy hk active origin cutter) ≤ ENNReal.ofReal ((1:ℝ)/64) := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs : (4:ℝ) ≤ scale n := (by norm_num : (4:ℝ) ≤ 2^42).trans (scale_large n)
  have hell : (1:ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive (scale_large n)
  have hks : (k:ℝ) ≤ scale n := by nlinarith [active_scale n k hkn,Nat.cast_nonneg (α:=ℝ) k]
  have htau : 0 < UpperRepair.nearError n := oldError_positive (scale_large n) hell
  have hz := actual_zero_rejection_small (q:=UpperRepair.coarse n) μ active policy hpolicy hmeas origin hgood hpositive
    (by omega) chores cutter hs hell hks
  have hc := UpperSnapshotEndpointCandidateFailure.actual_original_exhaustion_quarter μ policy hpolicy hmeas active
    (by omega) origin hgood hpositive cutter (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.nearError n) htau
  have hi := actual_small_original_interpolation_small (q:=UpperRepair.coarse n) μ active (by omega) cutter policy hpolicy hmeas
    origin hgood hpositive (UpperRepair.nearError n) htau hs hell hks
  let Ez : Set (GridTape n k × UpperCircular.Circle) := {p |
    selectedDistance (by omega) (UpperGridCache.table policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) p.1) cutter=0 ∧
      (zeroExecute policy (by omega) chores active
        (UpperGridCache.aligned policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) p.1) cutter p.2).2.2=true}
  let Ec : Set (GridTape n k × CandidateTape k) := {p |
    smallBranch (by omega) policy active origin cutter (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.nearError n) p.1 ∧
      (UpperSnapshotEndpointCandidateFailure.packetResult (by omega) policy active origin cutter (UpperRepair.coarse n)
        (UpperRepair.fine n) (UpperRepair.nearError n) p).2=none}
  let Ei : Set (GridTape n k × CandidateTape k) := {p |
    BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells
      (UpperGridMerge.cuts policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) p.1)
      (smallOriginalPoints (by omega) policy active origin cutter (UpperRepair.coarse n) (UpperRepair.fine n)
        (UpperRepair.nearError n) p) (snapshotAccuracy (scale n))}
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ ((gridLaw n k).prod (volume : Measure UpperCircular.Circle)) Ez :=
        measurePreserving_preimage_le _ _ _ (preparation_zero_projection n k) Ez
      _ ≤ 1/64 := hz.le
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  · calc
      _ ≤ ((gridLaw n k).prod (candidateLaw k)) Ec :=
        measurePreserving_preimage_le _ _ _ (preparation_small_projection n k) Ec
      _ ≤ 1/4 := hc
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  · calc
      _ ≤ ((gridLaw n k).prod (candidateLaw k)) Ei :=
        measurePreserving_preimage_le _ _ _ (preparation_small_projection n k) Ei
      _ ≤ 1/64 := hi.le
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
end EnvyFreeResearch.Full.UpperSnapshotProtocol
