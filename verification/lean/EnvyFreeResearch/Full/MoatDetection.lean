import EnvyFreeResearch.Full.NonnegativeDetection

/-! Actual Haar moat detector. Its uniform-transcript probability is linear
in the moat width, with no narrow-pulse endpoint loss. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatDetection
open Set MeasureTheory Metric NonnegativeCircle NonnegativeDetection
open scoped ENNReal Classical
abbrev Circle := NonnegativeCircle.Circle

def law (n : ℕ) : Measure (Fin n × Circle) :=
  (observerLaw n).prod (volume : Measure Circle)

theorem law_probability (n : ℕ) (hn : 0 < n) : IsProbabilityMeasure (law n) := by
  let := observerLaw_probability n hn
  unfold law
  infer_instance

def endpointEvent (w a : ℝ) : Set Circle := closedBall (a : Circle) (w/2)

theorem endpointEvent_mass {w : ℝ} (hw : w ≤ 1) (a : ℝ) :
    volume (endpointEvent w a) = ENNReal.ofReal w := by
  rw [endpointEvent, circle_ball_mass _ _ (by linarith)]
  congr 1
  ring

def detects {n : ℕ} (w : ℝ) (request : Request n) : Set (Fin n × Circle) :=
  {request.observer} ×ˢ (endpointEvent w request.left ∪ endpointEvent w request.right)

theorem measurable_detects {n : ℕ} (w : ℝ) (request : Request n) :
    MeasurableSet (detects w request) :=
  (measurableSet_singleton _).prod (measurableSet_closedBall.union measurableSet_closedBall)

theorem one_request_detection_le {n : ℕ} (w : ℝ) (hw : w ≤ 1) (request : Request n) :
    law n (detects w request) ≤ 2 * ENNReal.ofReal w / (n : ℝ≥0∞) := by
  rw [law, detects, Measure.prod_prod]
  have hsingle : observerLaw n {request.observer} = (n : ℝ≥0∞)⁻¹ := by
    simp [observerLaw]
  rw [hsingle]
  calc
    _ ≤ (n : ℝ≥0∞)⁻¹ * (volume (endpointEvent w request.left) + volume (endpointEvent w request.right)) :=
      mul_le_mul_right (measure_union_le _ _) _
    _ = _ := by rw [endpointEvent_mass hw, endpointEvent_mass hw]; simp only [div_eq_mul_inv]; ring

def detection {n : ℕ} (w : ℝ) : List (Request n) → Set (Fin n × Circle)
  | [] => ∅
  | r :: rs => detects w r ∪ detection w rs

theorem measurable_detection {n : ℕ} (w : ℝ) (requests : List (Request n)) :
    MeasurableSet (detection w requests) := by
  induction requests with
  | nil => exact MeasurableSet.empty
  | cons r rs ih => exact (measurable_detects w r).union ih

theorem transcript_detection_le {n : ℕ} (w : ℝ) (hw : w ≤ 1) (requests : List (Request n)) :
    law n (detection w requests) ≤
      (requests.length : ℝ≥0∞) * (2 * ENNReal.ofReal w / (n : ℝ≥0∞)) := by
  induction requests with
  | nil => simp [detection]
  | cons r rs ih =>
    calc
      _ ≤ law n (detects w r) + law n (detection w rs) := measure_union_le _ _
      _ ≤ 2 * ENNReal.ofReal w / (n : ℝ≥0∞) +
          (rs.length : ℝ≥0∞) * (2 * ENNReal.ofReal w / (n : ℝ≥0∞)) :=
        add_le_add (one_request_detection_le w hw r) ih
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem integrated_detection_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n) (w : ℝ) (hw : w ≤ 1)
    (requests : Ω → List (Request n))
    (hjoint : MeasurableSet {z : Ω × (Fin n × Circle) | z.2 ∈ detection w (requests z.1)})
    (hcount : Measurable (fun tape => (requests tape).length)) :
    (μ.prod (law n)) {z | z.2 ∈ detection w (requests z.1)} ≤
      (2 * ENNReal.ofReal w / (n : ℝ≥0∞)) * ∫⁻ tape, ((requests tape).length : ℝ≥0∞) ∂μ := by
  let := law_probability n hn
  rw [Measure.prod_apply hjoint]
  calc
    (∫⁻ tape, law n (Prod.mk tape ⁻¹' {z | z.2 ∈ detection w (requests z.1)}) ∂μ) ≤
        ∫⁻ tape, (2 * ENNReal.ofReal w / (n : ℝ≥0∞)) * ((requests tape).length : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro tape
      change law n (detection w (requests tape)) ≤ _
      simpa only [mul_comm] using transcript_detection_le w hw (requests tape)
    _ = _ := lintegral_const_mul _ ((measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp hcount)

/-- The designated changed observer is independent and uniform even when the
owner is an arbitrary measurable function of the center. -/
theorem decoder_probability {n : ℕ} (hn : 0 < n)
    (owner : Circle → Fin n) (howner : Measurable owner) :
    law n {z | z.1 ≠ owner z.2} = 1 - (n : ℝ≥0∞)⁻¹ := by
  let := observerLaw_probability n hn
  have hm : MeasurableSet {z : Fin n × Circle | z.1 ≠ owner z.2} :=
    (measurableSet_eq_fun measurable_fst (howner.comp measurable_snd)).compl
  rw [law, Measure.prod_apply_symm hm]
  have hsection (x : Circle) : observerLaw n ((fun i => (i,x)) ⁻¹' {z | z.1 ≠ owner z.2}) =
      1 - (n : ℝ≥0∞)⁻¹ := by
    have heq : (fun i => (i,x)) ⁻¹' {z | z.1 ≠ owner z.2} = {owner x}ᶜ := by ext i; simp
    rw [heq, measure_compl (measurableSet_singleton _) (measure_ne_top _ _), measure_univ]
    simp [observerLaw]
  simp_rw [hsection]
  simp

end EnvyFreeResearch.Full.MoatDetection
