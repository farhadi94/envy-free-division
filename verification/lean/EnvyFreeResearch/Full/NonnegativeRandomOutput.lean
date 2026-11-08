import EnvyFreeResearch.Full.NonnegativeAllocation
import EnvyFreeResearch.Full.NonnegativeOutputMeasurable

namespace EnvyFreeResearch.Full.NonnegativeRandomOutput

open MeasureTheory Set IntervalAllocation NonnegativeAllocation NonnegativeOutputMeasurable
open scoped Classical

variable {Agent : Type*} [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [Countable Agent]

theorem measurable_ownerAt_joint :
    Measurable (fun z : Allocation Agent × ℝ => ownerAt z.1 z.2) := by
  apply measurable_to_countable'
  intro i
  have heq : (fun z : Allocation Agent × ℝ => ownerAt z.1 z.2) ⁻¹' {i} =
      {z : Allocation Agent × ℝ | z.2 ∈ z.1.share i} ∪
      ({z | z.2 ∉ Icc (0 : ℝ) 1} ∩ {z | z.1.endpointOwner = i}) := by
    ext z
    have h := Set.ext_iff.mp (ownerAt_preimage z.1 i) z.2
    by_cases hi : z.1.endpointOwner = i <;> simpa [hi] using h
  rw [heq]
  exact (measurable_share_membership i).union
    (((measurableSet_Icc.preimage measurable_snd).compl).inter
      ((measurableSet_singleton i).preimage (measurable_endpointOwner.comp measurable_fst)))

theorem measurable_circleOwner_joint :
    Measurable (fun z : Allocation Agent × NonnegativeCircle.Circle => circleOwner z.1 z.2) :=
  measurable_ownerAt_joint.comp
    (measurable_fst.prodMk (NonnegativeEndpointLaw.measurable_representative.comp measurable_snd))

/-- Bundle lengths are measurable on the actual variable-size output space;
this follows by integrating joint share indicators, not by imposing a size
bound on the finite interval encoding. -/
theorem measurable_share_length (i : Agent) :
    Measurable (fun A : Allocation Agent => volume.real (A.share i)) := by
  have h := measurable_measure_prodMk_left (ν := (volume : Measure ℝ))
    (measurable_share_membership i)
  exact h.ennreal_toReal

def UniformEF (A : Allocation Agent) : Prop :=
  ∀ i j, volume.real (A.share j) ≤ volume.real (A.share i)

theorem measurable_uniformEF : MeasurableSet {A : Allocation Agent | UniformEF A} := by
  have heq : {A : Allocation Agent | UniformEF A} =
      ⋂ i, ⋂ j, {A : Allocation Agent | volume.real (A.share j) ≤ volume.real (A.share i)} := by
    ext A
    simp [UniformEF]
  rw [heq]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    measurableSet_le (measurable_share_length j) (measurable_share_length i)))

noncomputable def uniformGap (A : Allocation Agent) : ℝ :=
  (⨆ i, volume.real (A.share i)) - ⨅ i, volume.real (A.share i)

theorem measurable_uniformGap : Measurable (uniformGap (Agent := Agent)) :=
  (Measurable.iSup measurable_share_length).sub (Measurable.iInf measurable_share_length)

/-- Every genuinely unfair complete finite output has a positive measurable
gap, so the general shrinking-gap loss theorem applies to its actual law. -/
theorem uniformGap_positive [Fintype Agent] (A : Allocation Agent)
    (hwrong : ¬ UniformEF A) : 0 < uniformGap A := by
  classical
  simp only [UniformEF, not_forall, not_le] at hwrong
  obtain ⟨i, j, hij⟩ := hwrong
  have hu : volume.real (A.share j) ≤ ⨆ k, volume.real (A.share k) :=
    le_ciSup (f := fun k => volume.real (A.share k))
      (Set.finite_range (fun k => volume.real (A.share k))).bddAbove j
  have hl : (⨅ k, volume.real (A.share k)) ≤ volume.real (A.share i) :=
    ciInf_le (f := fun k => volume.real (A.share k))
      (Set.finite_range (fun k => volume.real (A.share k))).bddBelow i
  unfold uniformGap
  linarith

/-- Actual measurable finite output rules automatically supply exactly the
count and padded endpoint-coordinate hypotheses used by the width theorem. -/
theorem measurable_output_endpoints {Ω : Type*} [MeasurableSpace Ω]
    (output : Ω → Allocation Agent) (houtput : Measurable output) :
    Measurable (fun tape => endpointCount (output tape)) ∧
      ∀ k, Measurable (fun tape => endpoint (output tape) k) :=
  ⟨measurable_endpointCount.comp houtput, fun k => (measurable_endpoint k).comp houtput⟩

end EnvyFreeResearch.Full.NonnegativeRandomOutput

#print axioms EnvyFreeResearch.Full.NonnegativeRandomOutput.measurable_ownerAt_joint
#print axioms EnvyFreeResearch.Full.NonnegativeRandomOutput.measurable_share_length
#print axioms EnvyFreeResearch.Full.NonnegativeRandomOutput.measurable_uniformGap
#print axioms EnvyFreeResearch.Full.NonnegativeRandomOutput.uniformGap_positive
