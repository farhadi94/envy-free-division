import EnvyFreeResearch.Full.NonnegativeRetainedFailure
import EnvyFreeResearch.Full.NonnegativeDecoder

namespace EnvyFreeResearch.Full.NonnegativeDecoderLedger

open MeasureTheory Set IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeAllocation NonnegativeRandomOutput NonnegativeRetainedFailure NonnegativeSuccess
open NonnegativeShift NonnegativeDetection NonnegativeExperiment
open scoped Classical ENNReal

abbrev Circle := NonnegativeCircle.Circle

noncomputable def factor (n : ℕ) (w : ℝ) : ℝ≥0∞ :=
  (1 - (n : ℝ≥0∞)⁻¹) * (1 - (ENNReal.ofReal (2 * w))⁻¹ * (n : ℝ≥0∞)⁻¹)

theorem measurable_favorable {n : ℕ} (chores : Bool) :
    MeasurableSet {z : Input n × Allocation (Fin n) | Favorable chores z.2 z.1.1 z.1.2} := by
  have hownerC : Measurable (fun z : Input n × Allocation (Fin n) =>
      circleOwner z.2 (first z.1.2)) := measurable_circleOwner_joint.comp
    (measurable_snd.prodMk (measurable_first.comp (measurable_snd.comp measurable_fst)))
  have hownerD : Measurable (fun z : Input n × Allocation (Fin n) =>
      circleOwner z.2 (second z.1.2)) := measurable_circleOwner_joint.comp
    (measurable_snd.prodMk (measurable_second.comp (measurable_snd.comp measurable_fst)))
  have hdiff := (measurableSet_eq_fun hownerC hownerD).compl
  cases chores with
  | false => exact hdiff.inter ((measurableSet_eq_fun (measurable_fst.comp measurable_fst) hownerC).compl)
  | true => exact hdiff.inter ((measurableSet_eq_fun (measurable_fst.comp measurable_fst) hownerD).compl)

def decoderGood {n : ℕ} (chores : Bool) : Set (Input n × Allocation (Fin n)) :=
  {z | UniformEF z.2 ∧ Favorable chores z.2 z.1.1 z.1.2}

theorem measurable_decoderGood {n : ℕ} (chores : Bool) : MeasurableSet (decoderGood (n := n) chores) :=
  (measurable_uniformEF.preimage measurable_snd).inter (measurable_favorable chores)

/-- The geometric probability applies to the actual complete physical
allocation, since uniform envy-freeness proves equal Haar ownership fibers. -/
theorem physical_decoder_probability {n : ℕ} (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (hwsmall : w ≤ 1 / 2) (chores : Bool) (A : Allocation (Fin n)) (hA : UniformEF A) :
    factor n w ≤ perturbLaw n w {z | Favorable chores A z.1 z.2} := by
  cases chores with
  | false =>
    exact NonnegativeDecoder.decoder_probability_lower hn w hw hwsmall (circleOwner A)
      (circleOwner_measurable A) (circle_fibers_of_uniformEF hn A hA) first measurable_first
  | true =>
    exact NonnegativeDecoder.decoder_probability_lower hn w hw hwsmall (circleOwner A)
      (circleOwner_measurable A) (circle_fibers_of_uniformEF hn A hA) second measurable_second

def decoded {n : ℕ} {Tape : Type*}
    (execution : Tape → Execution (Query (Fin n)) NonnegativeOracle.Reply (Allocation (Fin n)))
    (chores : Bool) : Set (Tape × Input n) :=
  {z | Successful {A | (z.2, A) ∈ decoderGood chores} (execution z.1)}

theorem measurable_decoded {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]
    (execution : Tape → Execution (Query (Fin n)) NonnegativeOracle.Reply (Allocation (Fin n)))
    (hexecution : Measurable execution) (chores : Bool) : MeasurableSet (decoded execution chores) :=
  (measurable_joint_successful (decoderGood chores) (measurable_decoderGood chores)).preimage
    (measurable_snd.prodMk (hexecution.comp measurable_fst))

theorem decoded_subset_success {n : ℕ} {Tape : Type*}
    (execution : Tape → Execution (Query (Fin n)) NonnegativeOracle.Reply (Allocation (Fin n)))
    (chores : Bool) : decoded execution chores ⊆
      {z | Successful {A | UniformEF A} (execution z.1)} := by
  rintro z ⟨A, hreturned, hA, _⟩
  exact ⟨A, hreturned, hA⟩

/-- Integrating the actual decoder over successful uniform tapes yields the
retained decoder mass. No measurable choice of returned allocation is needed:
the returned value is recovered from the actual stop code pointwise. -/
theorem integrated_physical_decoder {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]
    (μ : Measure Tape) [SFinite μ] (hn : 0 < n) (w : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    (execution : Tape → Execution (Query (Fin n)) NonnegativeOracle.Reply (Allocation (Fin n)))
    (hexecution : Measurable execution) (chores : Bool) :
    factor n w * μ {tape | Successful {A | UniformEF A} (execution tape)} ≤
      (μ.prod (perturbLaw n w)) (decoded execution chores) := by
  let := perturbLaw_probability n hn w hw
  let S : Set Tape := {tape | Successful {A | UniformEF A} (execution tape)}
  have hS : MeasurableSet S := (measurable_successful _ measurable_uniformEF).preimage hexecution
  rw [Measure.prod_apply (measurable_decoded execution hexecution chores)]
  rw [← lintegral_indicator_const hS (factor n w)]
  apply lintegral_mono
  intro tape
  by_cases ht : tape ∈ S
  · obtain ⟨A, hreturned, hA⟩ := ht
    rw [indicator_of_mem (show tape ∈ S from ⟨A, hreturned, hA⟩)]
    have heq : Prod.mk tape ⁻¹' decoded execution chores =
        {z | Favorable chores A z.1 z.2} := by
      ext z
      constructor
      · rintro ⟨B, hreturnedB, _, hfavorable⟩
        have hAB : A = B := Stop.returned.inj (hreturned.symm.trans hreturnedB)
        change Favorable chores A z.1 z.2
        simpa only [hAB] using hfavorable
      · intro hfavorable
        exact ⟨A, hreturned, hA, hfavorable⟩
    change factor n w ≤ perturbLaw n w (Prod.mk tape ⁻¹' decoded execution chores)
    rw [heq]
    exact physical_decoder_probability hn w hw hwsmall chores A hA
  · rw [indicator_of_notMem ht]
    exact bot_le

end EnvyFreeResearch.Full.NonnegativeDecoderLedger

#print axioms EnvyFreeResearch.Full.NonnegativeDecoderLedger.physical_decoder_probability
#print axioms EnvyFreeResearch.Full.NonnegativeDecoderLedger.integrated_physical_decoder
