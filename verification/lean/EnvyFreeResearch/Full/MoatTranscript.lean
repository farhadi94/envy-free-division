import EnvyFreeResearch.Full.MoatSelection
import EnvyFreeResearch.Full.NonnegativeCostLedger

namespace EnvyFreeResearch.Full.MoatTranscript
open Set MeasureTheory IntervalOracle OracleProtocol ProtocolMeasurable Metric
open NonnegativeOracle NonnegativeProfile NonnegativeDetection NonnegativeSuccess
open NonnegativeMeasurableDetection NonnegativeReplay NonnegativeCostLedger MoatSelection
open scoped Classical ENNReal
abbrev Circle := NonnegativeCircle.Circle

noncomputable def rate (two : Bool) (n : ℕ) (w : ℝ) : ℝ≥0∞ :=
  (if two then 4 else 2)*ENNReal.ofReal w/(n:ℝ≥0∞)

def detects {n : ℕ} (two : Bool) (w : ℝ) (r : Request n) : Set (Input n) :=
  if two then twoDetects w r else MoatDetection.detects w r

theorem detects_iff {n : ℕ} (two : Bool) (w : ℝ) (r : Request n) (z : Input n) :
    z ∈ detects two w r ↔ r.observer ∈ selected two z.1 ∧
      (z.2 ∈ MoatDetection.endpointEvent w r.left ∪
        MoatDetection.endpointEvent w r.right) := by
  cases two
  · simp only [detects, Bool.false_eq_true, ite_false, MoatDetection.detects,
      mem_prod, mem_singleton_iff, selected, Finset.mem_singleton]
    tauto
  · exact two_detects_iff w r z

theorem measurable_joint_detects {n : ℕ} (two : Bool) (w : ℝ) :
    MeasurableSet {z : Request n × Input n | z.2 ∈ detects two w z.1} := by
  have ho : Measurable (fun z : Request n × Input n => z.1.observer) :=
    measurable_request_observer.comp measurable_fst
  have hi : Measurable (fun z : Request n × Input n => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hr : Measurable (fun z : Request n × Input n => finRotate n z.2.1) :=
    (measurable_of_countable (finRotate n)).comp hi
  have hc : Measurable (fun z : Request n × Input n => z.2.2) :=
    measurable_snd.comp measurable_snd
  have hleft : Measurable (fun z : Request n × Input n => (z.1.left:Circle)) :=
    AddCircle.measurable_mk'.comp (measurable_request_left.comp measurable_fst)
  have hright : Measurable (fun z : Request n × Input n => (z.1.right:Circle)) :=
    AddCircle.measurable_mk'.comp (measurable_request_right.comp measurable_fst)
  have hends : MeasurableSet {z : Request n × Input n |
      z.2.2 ∈ MoatDetection.endpointEvent w z.1.left ∪
        MoatDetection.endpointEvent w z.1.right} :=
    (measurableSet_le (hc.dist hleft) measurable_const).union
      (measurableSet_le (hc.dist hright) measurable_const)
  have hselect : MeasurableSet {z : Request n × Input n | z.1.observer ∈ selected two z.2.1} := by
    cases two
    · simpa only [selected, Bool.false_eq_true, ite_false, Finset.mem_singleton] using measurableSet_eq_fun ho hi
    · simpa only [selected, ite_true, Finset.mem_insert, Finset.mem_singleton, Set.ofPred_or] using
        (measurableSet_eq_fun ho hi).union (measurableSet_eq_fun ho hr)
  simpa only [detects_iff, Set.ofPred_and] using hselect.inter hends

def detection {n : ℕ} (two : Bool) (w : ℝ) : List (Request n) → Set (Input n)
  | [] => ∅
  | r::rs => detects two w r ∪ detection two w rs

theorem mem_detection_iff {n : ℕ} (two : Bool) (w : ℝ) (rs : List (Request n)) (z : Input n) :
    z ∈ detection two w rs ↔ ∃ r ∈ rs, z ∈ detects two w r := by
  induction rs with
  | nil => simp [detection]
  | cons r rs ih => simp only [detection, mem_union, ih, List.mem_cons]; aesop

theorem measurable_joint_detection {n : ℕ} (two : Bool) (w : ℝ) :
    MeasurableSet {z : List (Request n) × Input n | z.2 ∈ detection two w z.1} := by
  have heq : {z : List (Request n) × Input n | z.2 ∈ detection two w z.1} =
      ⋃ k : ℕ, {z | ∃ r, z.1[k]? = some r ∧ z.2 ∈ detects two w r} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_detection_iff]
    constructor
    · rintro ⟨r,hr,hd⟩
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hr
      exact ⟨k,r,hk,hd⟩
    · rintro ⟨k,r,hk,hd⟩
      exact ⟨r,List.mem_iff_getElem?.mpr ⟨k,hk⟩,hd⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  exact (measurable_some_relation _ (measurable_joint_detects two w)).preimage
    (((measurable_list_getElem k).comp measurable_fst).prodMk measurable_snd)

theorem request_detection_le {n : ℕ} (hn : 0 < n) (two : Bool) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (r : Request n) :
    MoatDetection.law n (detects two w r) ≤ rate two n w := by
  cases two
  · exact MoatDetection.one_request_detection_le w hw1 r
  · exact two_request_detection_le hn w hw hw1 r

theorem transcript_detection_le {n : ℕ} (hn : 0 < n) (two : Bool) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (rs : List (Request n)) :
    MoatDetection.law n (detection two w rs) ≤ (rs.length:ℝ≥0∞)*rate two n w := by
  induction rs with
  | nil => simp [detection]
  | cons r rs ih =>
    calc
      _ ≤ _ + _ := measure_union_le _ _
      _ ≤ rate two n w + (rs.length:ℝ≥0∞)*rate two n w :=
        add_le_add (request_detection_le hn two w hw hw1 r) ih
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem integrated_detection_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n) (two : Bool) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (rs : Ω → List (Request n)) (hrs : Measurable rs) :
    (μ.prod (MoatDetection.law n)) {z | z.2 ∈ detection two w (rs z.1)} ≤
      rate two n w * ∫⁻ t, ((rs t).length:ℝ≥0∞) ∂μ := by
  let := MoatDetection.law_probability n hn
  have hjoint : MeasurableSet {z : Ω × Input n | z.2 ∈ detection two w (rs z.1)} :=
    (measurable_joint_detection (n := n) two w).preimage
    ((hrs.comp measurable_fst).prodMk measurable_snd)
  rw [Measure.prod_apply hjoint]
  calc
    _ ≤ ∫⁻ t, rate two n w * ((rs t).length:ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro t
      change MoatDetection.law n (detection two w (rs t)) ≤ _
      simpa only [mul_comm] using transcript_detection_le hn two w hw hw1 (rs t)
    _ = _ := lintegral_const_mul _ ((measurable_of_countable (fun k : ℕ => (k:ℝ≥0∞))).comp
      (measurable_list_length.comp hrs))

end EnvyFreeResearch.Full.MoatTranscript
