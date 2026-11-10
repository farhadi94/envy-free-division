import EnvyFreeResearch.Full.MoatSelection
import EnvyFreeResearch.Full.MoatReplay

set_option maxHeartbeats 1200000

namespace EnvyFreeResearch.Full.MoatExperiment
open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeRandomOutput
open NonnegativeRetainedFailure NonnegativeAllocation NonnegativeEndpointLaw
open MoatSelection
open scoped Classical ENNReal

noncomputable def rows {n : ℕ} (two chores : Bool) (w h : ℝ) (z : Input n) : Fin n → MixedDensity.Row :=
  MoatFamily.rows chores w h (toFamily two z)
noncomputable def oracle {n : ℕ} (two flag chores : Bool) (w h : ℝ) (z : Input n) : Query (Fin n) → Option Reply :=
  MoatFamily.oracle flag chores w h (toFamily two z)

theorem oracle_measurable {n : ℕ} (two flag chores : Bool) {w h : ℝ}
    (hw : 0 < w) (hh : 0 ≤ h) (hhw : h ≤ w) :
    Measurable (fun z : Input n × Query (Fin n) => oracle two flag chores w h z.1 z.2) := by
  have hm : Measurable (fun z : Input n × Query (Fin n) => (toFamily two z.1,z.2)) :=
    (((toFamily_measurable two).comp measurable_fst).prodMk measurable_snd)
  exact (MoatFamily.oracle_measurable flag chores hw hh hhw).comp hm

def inputGood {n : ℕ} (two chores : Bool) (w h : ℝ) : Set (Input n × Allocation (Fin n)) :=
  {z | Fair chores (rows two chores w h z.1) z.2}

theorem inputGood_measurable {n : ℕ} (two chores : Bool) (w h : ℝ) :
    MeasurableSet (inputGood (n := n) two chores w h) := by
  have hm : Measurable (fun z : Input n × Allocation (Fin n) => (toFamily two z.1,z.2)) :=
    (((toFamily_measurable two).comp measurable_fst).prodMk measurable_snd)
  have hg := (MoatFamily.fair_measurable chores w h).preimage hm
  simpa only [inputGood, rows, Set.preimage_setOf_eq] using hg

def favorable {n : ℕ} (two : Bool) (A : Allocation (Fin n)) (z : Input n) : Prop :=
  two = true ∨ z.1 ≠ circleOwner A z.2

theorem measurable_favorable {n : ℕ} (two : Bool) :
    MeasurableSet {z : Input n × Allocation (Fin n) | favorable two z.2 z.1} := by
  have ho : Measurable (fun z : Input n × Allocation (Fin n) => circleOwner z.2 z.1.2) :=
    measurable_circleOwner_joint.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  cases two
  · simpa only [favorable, Bool.false_eq_true, false_or, Set.compl_setOf, Function.comp_def] using
      (measurableSet_eq_fun (measurable_fst.comp measurable_fst) ho).compl
  · simp only [favorable, true_or, Set.setOf_true]
    exact MeasurableSet.univ

def decoderGood {n : ℕ} (two : Bool) : Set (Input n × Allocation (Fin n)) :=
  {z | UniformEF z.2 ∧ favorable two z.2 z.1}

theorem measurable_decoderGood {n : ℕ} (two : Bool) :
    MeasurableSet (decoderGood (n := n) two) :=
  (measurable_uniformEF.preimage measurable_snd).inter (measurable_favorable two)

noncomputable def factor (two : Bool) (n : ℕ) : ℝ≥0∞ := if two then 1 else 1-(n:ℝ≥0∞)⁻¹

theorem physical_decoder_probability {n : ℕ} (hn : 0 < n) (two : Bool)
    (A : Allocation (Fin n)) :
    factor two n = MoatDetection.law n {z | favorable two A z} := by
  let := MoatDetection.law_probability n hn
  cases two
  · simpa only [factor, Bool.false_eq_true, ite_false, favorable, false_or] using
      (MoatDetection.decoder_probability hn (circleOwner A) (circleOwner_measurable A)).symm
  · simp [factor, favorable]

def decoded {n : ℕ} {Tape : Type*}
    (execution : Tape → Execution (Query (Fin n)) Reply (Allocation (Fin n)))
    (two : Bool) : Set (Tape × Input n) :=
  {z | Successful {A | (z.2,A) ∈ decoderGood two} (execution z.1)}

theorem measurable_decoded {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]
    (execution : Tape → Execution (Query (Fin n)) Reply (Allocation (Fin n)))
    (hexecution : Measurable execution) (two : Bool) : MeasurableSet (decoded execution two) :=
  (measurable_joint_successful (decoderGood two) (measurable_decoderGood two)).preimage
    (measurable_snd.prodMk (hexecution.comp measurable_fst))

theorem decoded_subset_success {n : ℕ} {Tape : Type*}
    (execution : Tape → Execution (Query (Fin n)) Reply (Allocation (Fin n))) (two : Bool) :
    decoded execution two ⊆ {z | Successful {A | UniformEF A} (execution z.1)} := by
  rintro z ⟨A,hA,hgood,_⟩
  exact ⟨A,hA,hgood⟩

theorem integrated_decoder {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]
    (μ : Measure Tape) [SFinite μ] (hn : 0 < n)
    (execution : Tape → Execution (Query (Fin n)) Reply (Allocation (Fin n)))
    (hexecution : Measurable execution) (two : Bool) :
    factor two n * μ {t | Successful {A | UniformEF A} (execution t)} ≤
      (μ.prod (MoatDetection.law n)) (decoded execution two) := by
  let := MoatDetection.law_probability n hn
  let S : Set Tape := {t | Successful {A | UniformEF A} (execution t)}
  have hS : MeasurableSet S := (measurable_successful _ measurable_uniformEF).preimage hexecution
  rw [Measure.prod_apply (measurable_decoded execution hexecution two)]
  rw [← lintegral_indicator_const hS (factor two n)]
  apply lintegral_mono
  intro tape
  by_cases ht : tape ∈ S
  · obtain ⟨A,hreturned,hA⟩ := ht
    rw [indicator_of_mem (show tape ∈ S from ⟨A,hreturned,hA⟩)]
    have heq : Prod.mk tape ⁻¹' decoded execution two = {z | favorable two A z} := by
      ext z
      constructor
      · rintro ⟨B,hB,_,hf⟩
        have hAB : A=B := Stop.returned.inj (hreturned.symm.trans hB)
        change favorable two A z
        simpa only [hAB] using hf
      · intro hf
        exact ⟨A,hreturned,hA,hf⟩
    change factor two n ≤ MoatDetection.law n (Prod.mk tape ⁻¹' decoded execution two)
    rw [heq, ← physical_decoder_probability hn two A]
  · rw [indicator_of_notMem ht]
    exact bot_le

end EnvyFreeResearch.Full.MoatExperiment
