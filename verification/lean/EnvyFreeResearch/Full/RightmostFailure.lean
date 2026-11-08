import EnvyFreeResearch.Full.PhysicalReflection
import EnvyFreeResearch.Full.MixedSuccess

/-! Physical output obstruction for the reflected hard family. The argument
uses the actual signed densities and complete finite-interval outputs. -/

noncomputable section
namespace EnvyFreeResearch.Full.RightmostFailure
open Set MeasureTheory TranscriptAdversary MixedDensity MixedFrontier MixedObstruction
open IntervalAllocation PhysicalReflection MixedCoordinates MixedCaptureStep
open NonnegativeOutputMeasurable
open scoped Classical

variable {Agent : Type*} {α : ℝ}

def FrozenOutput (l : ℝ) (A : Allocation Agent) : Prop :=
  (∀ k, FrozenCoordinate l (1 - A.left k)) ∧
  (∀ k, FrozenCoordinate l (1 - A.right k))

def outputMaximum (A : Allocation Agent) : ℝ :=
  properMaximum (endpointCount A) (fun k => 1 - endpoint A k)

theorem outputMaximum_lt_one (A : Allocation Agent) : outputMaximum A < 1 :=
  properMaximum_lt_one _ _

theorem outputMaximum_frozen (A : Allocation Agent) (l : ℝ)
    (h : outputMaximum A ≤ l) : FrozenOutput l A := by
  constructor
  · intro k
    obtain ⟨hk, heq⟩ := left_endpoint_recorded A k
    have hb : 1 - endpoint A (2*k.val+2) ≤ 1 := by rw [heq]; linarith [(A.bounded k).1]
    simpa only [heq] using coordinate_frozen hk hb h
  · intro k
    obtain ⟨hk, heq⟩ := right_endpoint_recorded A k
    have hb : 1 - endpoint A (2*k.val+3) ≤ 1 := by
      rw [heq]
      linarith [(A.bounded k).1, (A.bounded k).2.1]
    simpa only [heq] using coordinate_frozen hk hb h

theorem frozenOutput_mono (A : Allocation Agent) {l r : ℝ} (hlr : l ≤ r)
    (h : FrozenOutput l A) : FrozenOutput r A :=
  ⟨fun k => MixedExecution.frozen_mono hlr (h.1 k),
    fun k => MixedExecution.frozen_mono hlr (h.2 k)⟩

theorem exists_initial_owner (A : Allocation Agent) (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hf : FrozenOutput l A) : ∃ i, Ioc (0 : ℝ) (1-l) ⊆ A.share i := by
  let x : ℝ := (1-l)/2
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hxl : x < 1-l := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hx : x ∈ Ioc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  rw [← A.covers] at hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  have hleft : A.left k = 0 := by
    rcases hf.1 k with h | h
    · linarith [hk.1]
    · linarith
  have hright : 1-l ≤ A.right k := by
    rcases hf.2 k with h | h
    · linarith
    · linarith [hk.2]
  refine ⟨A.owner k, ?_⟩
  intro y hy
  apply (A.mem_share _ _).mpr
  apply Or.inl
  apply (A.mem_positiveShare _ _).mpr
  exact ⟨k, rfl, by simpa only [hleft] using hy.1, hy.2.trans hright⟩

def ApproximateEF (S : State Agent α) (A : Allocation Agent) (ε : ℝ) : Prop :=
  ∀ i j, α * value (reflectRow (S.rows i)) (A.share j) -
    value (reflectRow (S.rows i)) (A.share i) ≤ ε

theorem frozen_output_failure [Fintype Agent] (S : State Agent α) (A : Allocation Agent)
    (ε : ℝ) (hn : 3 ≤ Fintype.card Agent) (hα : 0 ≤ α) (hε : ε < α)
    (hf : FrozenOutput S.frontier A) : ¬ ApproximateEF S A ε := by
  obtain ⟨c, htail⟩ := exists_initial_owner A S.frontier S.nonnegative S.proper hf
  obtain ⟨a, b, hac, hbc, hab⟩ := MixedPhysicalFailure.exists_two_nonowners c hn
  have hpoint : ∀ᵐ x ∂domainMeasure,
      transferDensity α (reflectRow (S.rows a)).density (reflectRow (S.rows b)).density
        (A.share a) (A.share b) (A.share c) x ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ := domainMeasure) (1 : ℝ)))] with x hx hx1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 (by simpa only [mem_singleton_iff] using hx1)
    by_cases hxl : x ≤ 1-S.frontier
    · rw [transferDensity_on_owner (A.share_disjoint hac) (A.share_disjoint hbc) (htail ⟨hx.1,hxl⟩)]
    · have hcoord : 1-x ∈ Ioc (0 : ℝ) S.frontier := ⟨by linarith, by linarith⟩
      exact transferDensity_nonpositive hα (A.share_disjoint hab)
        (A.share_disjoint hac) (A.share_disjoint hbc) x
        (S.prefix_coefficients a b hab (1-x) hcoord)
  have hnorm (i : Agent) : (reflectRow (S.rows i)).cumulative 1 = 1 := by
    simp only [reflectRow_cumulative, sub_self, Row.cumulative_zero, sub_zero, (S.ceiling i).1]
  have h := physical_envy_sum_of_nonpositive (reflectRow (S.rows a)) (reflectRow (S.rows b))
    α (A.share a) (A.share b) (A.share c)
    (A.share_measurable a) (A.share_measurable b) (A.share_measurable c)
    (hnorm a) (hnorm b) hpoint
  intro hef
  have ha := hef a c
  have hb := hef b c
  linarith

theorem outputMaximum_measurable [MeasurableSpace Agent] : Measurable (outputMaximum (Agent := Agent)) :=
  measurable_variableMaximum endpointCount (fun A k => 1 - endpoint A k)
    measurable_endpointCount (fun k => measurable_const.sub (measurable_endpoint k))

theorem approximateEF_measurable [Fintype Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] (S : State Agent α) (ε : ℝ) :
    MeasurableSet {A : Allocation Agent | ApproximateEF S A ε} := by
  have heq : {A : Allocation Agent | ApproximateEF S A ε} =
      ⋂ i, ⋂ j, {A | α * value (reflectRow (S.rows i)) (A.share j) -
        value (reflectRow (S.rows i)) (A.share i) ≤ ε} := by
    ext A
    simp [ApproximateEF]
  rw [heq]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    measurableSet_le
      (((MixedSuccess.physical_value_measurable (reflectRow (S.rows i)) j).const_mul α).sub
        (MixedSuccess.physical_value_measurable (reflectRow (S.rows i)) i)) measurable_const))

end EnvyFreeResearch.Full.RightmostFailure
