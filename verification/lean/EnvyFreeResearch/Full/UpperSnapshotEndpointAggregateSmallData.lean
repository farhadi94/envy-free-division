import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateGridBound
import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallEndpointVector
import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallParameters

/-! The small-branch endpoint data are taken from the actual original grid.
Outside the actual branch the endpoint vector is the immutable boundary zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotCandidates UpperSnapshotSmall UpperSnapshotRepetition Chores
variable {n k q m : ℕ}

abbrev GridSeed (k m : ℕ) := Fin m → Fin k × I

def smallD (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (cutter : Fin k) (q m : ℕ) (draw : GridSeed k m) : ℝ :=
  selectedDistance (by omega) (UpperGridCache.table policy active origin q m draw) cutter

def smallScore (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (cutter : Fin k) (q m : ℕ) (draw : GridSeed k m) :
    Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1) → ℝ :=
  fun e => let values := UpperGridCache.table policy active origin q m draw
    values (selectedRow (by omega) values cutter) e - values cutter e

def smallTarget (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (cutter : Fin k) (q m : ℕ) (tau : ℝ) (draw : GridSeed k m) : ℝ :=
  (1-(8/tau)*smallD hk policy active origin cutter q m draw)/k

def smallBranch (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (cutter : Fin k) (q m : ℕ) (tau : ℝ) (draw : GridSeed k m) : Prop :=
  0 < smallD hk policy active origin cutter q m draw ∧ smallD hk policy active origin cutter q m draw < tau/16

def smallOriginalPoints (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (cutter : Fin k) (q m : ℕ) (tau : ℝ)
    (p : GridSeed k m × Tape (UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle) (16*k)) :
    Fin ((16*k)*(2+k)) → ℝ :=
  if smallBranch hk policy active origin cutter q m tau p.1 then
    smallEndpointVector hk policy (active cutter) (UpperGridMerge.cuts policy active origin q m p.1)
      (smallScore hk policy active origin cutter q m p.1) (domain origin.cells)
      (smallTarget hk policy active origin cutter q m tau p.1)
      (UpperGridCache.aligned policy active origin q m p.1) p.2
  else fun _ => 0

theorem fixed_first_measurable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X × Y → Z) (hf : Measurable f) (x : X) : Measurable (fun y => f (x,y)) :=
  hf.comp (measurable_const.prodMk measurable_id)

theorem original_table_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (q m : ℕ) (i : Fin k)
    (e : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)) :
    Measurable (fun draw => UpperGridCache.table policy active origin q m draw i e) :=
  fixed_first_measurable (fun p : State n × GridSeed k m => UpperGridCache.table policy active p.1 q m p.2 i e)
    (UpperGridCache.table_measurable policy hmeas active q m i e) origin

theorem smallD_measurable (hk : 2 ≤ k) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (q m : ℕ) :
    Measurable (smallD hk policy active origin cutter q m) :=
  selectedDistance_measurable (by omega) _ cutter (original_table_measurable policy hmeas active origin q m)

theorem smallScore_measurable (hk : 2 ≤ k) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (q m : ℕ)
    (e : Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)) :
    Measurable (fun draw => smallScore hk policy active origin cutter q m draw e) :=
  (selected_value_measurable (by omega) _ cutter (original_table_measurable policy hmeas active origin q m) e).sub
    (original_table_measurable policy hmeas active origin q m cutter e)

theorem smallTarget_measurable (hk : 2 ≤ k) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (q m : ℕ) (tau : ℝ) :
    Measurable (smallTarget hk policy active origin cutter q m tau) :=
  (measurable_const.sub (measurable_const.mul (smallD_measurable hk policy hmeas active origin cutter q m))).div_const k

theorem smallBranch_measurableSet (hk : 2 ≤ k) (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (cutter : Fin k) (q m : ℕ) (tau : ℝ) :
    MeasurableSet {draw | smallBranch hk policy active origin cutter q m tau draw} :=
  (measurableSet_lt measurable_const (smallD_measurable hk policy hmeas active origin cutter q m)).inter
    (measurableSet_lt (smallD_measurable hk policy hmeas active origin cutter q m) measurable_const)

theorem actual_small_target_checks (hk : 2 ≤ k) (policy : Policy n) (active : Fin k → Fin n)
    (origin : State n) (cutter : Fin k) (q m : ℕ) (tau : ℝ) (htau : 0 < tau)
    (draw : GridSeed k m) (hbranch : smallBranch hk policy active origin cutter q m tau draw) :
    let t := smallTarget hk policy active origin cutter q m tau draw
    0 < t ∧ t ≤ 1/2 ∧ 1/(2*(k : ℝ)) ≤ t := by
  have h := UpperSnapshotProtocol.small_amount_checks tau (smallD hk policy active origin cutter q m draw)
    k htau hbranch.1 hbranch.2 (by exact_mod_cast hk)
  exact ⟨h.1,h.2.1,h.2.2.2.2.1⟩

theorem actual_small_initial_valid
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (q m : ℕ) (draw : GridSeed k m) :
    smallValid μ (domain origin.cells) (UpperGridMerge.cuts policy active origin q m draw)
      (UpperGridCache.aligned policy active origin q m draw) :=
  ⟨UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive q m draw,
    UpperGridCache.aligned_domain policy active origin q m draw,
    UpperGridCache.aligned_separated policy active origin q m draw⟩

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
