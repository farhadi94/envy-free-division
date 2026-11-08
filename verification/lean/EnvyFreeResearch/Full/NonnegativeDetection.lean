import EnvyFreeResearch.Full.NonnegativeShift

namespace EnvyFreeResearch.Full.NonnegativeDetection

open MeasureTheory Set
open scoped ENNReal

abbrev Circle := NonnegativeCircle.Circle
open NonnegativeShift (first second shiftLaw)
open NonnegativeGeometry (arc)

noncomputable def observerLaw (n : ℕ) : Measure (Fin n) :=
  Measure.uniformOfFinset Finset.univ

theorem observerLaw_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (observerLaw n) := by
  constructor
  simp only [observerLaw, Measure.uniformOfFinset_apply, Set.mem_univ,
    Finset.filter_true, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.div_self (by exact_mod_cast ne_of_gt hn) (by simp)

noncomputable def perturbLaw (n : ℕ) (w : ℝ) : Measure (Fin n × (ℝ × Circle)) :=
  (observerLaw n).prod (shiftLaw w)

theorem perturbLaw_probability (n : ℕ) (hn : 0 < n) (w : ℝ) (hw : 0 < w) :
    IsProbabilityMeasure (perturbLaw n w) := by
  let := observerLaw_probability n hn
  let := NonnegativeShift.shiftLaw_probability w hw
  exact inferInstanceAs (IsProbabilityMeasure ((observerLaw n).prod (shiftLaw w)))

/-- One determining interval, including the possible terminal illegal request. -/
structure Request (n : ℕ) where
  observer : Fin n
  left : ℝ
  right : ℝ

def detects {n : ℕ} (request : Request n) : Set (Fin n × (ℝ × Circle)) :=
  {request.observer} ×ˢ
    {z | (first z ∈ arc request.left request.right) ≠
      (second z ∈ arc request.left request.right)}

theorem measurable_detects {n : ℕ} (request : Request n) : MeasurableSet (detects request) :=
  (measurableSet_singleton request.observer).prod
    (NonnegativeShift.measurable_separation request.left request.right)

theorem one_request_detection_le {n : ℕ} (request : Request n) (w : ℝ) (hw : 0 < w) :
    perturbLaw n w (detects request) ≤ ENNReal.ofReal w / (n : ℝ≥0∞) := by
  let := NonnegativeShift.shiftLaw_probability w hw
  rw [perturbLaw, detects, Measure.prod_prod]
  have hsingle : observerLaw n {request.observer} = (n : ℝ≥0∞)⁻¹ := by
    simp [observerLaw]
  rw [hsingle, div_eq_mul_inv, mul_comm (ENNReal.ofReal w)]
  gcongr
  exact NonnegativeShift.separation_probability_le request.left request.right w hw

def detection {n : ℕ} : List (Request n) → Set (Fin n × (ℝ × Circle))
  | [] => ∅
  | request :: requests => detects request ∪ detection requests

theorem measurable_detection {n : ℕ} (requests : List (Request n)) :
    MeasurableSet (detection requests) := by
  induction requests with
  | nil => exact MeasurableSet.empty
  | cons request requests ih => exact (measurable_detects request).union ih

/-- A union bound over the full fixed baseline transcript. There is no
conditioning on previous nondetection and no adaptation assumption. -/
theorem transcript_detection_le {n : ℕ} (requests : List (Request n)) (w : ℝ) (hw : 0 < w) :
    perturbLaw n w (detection requests) ≤
      (requests.length : ℝ≥0∞) * (ENNReal.ofReal w / (n : ℝ≥0∞)) := by
  induction requests with
  | nil => simp [detection]
  | cons request requests ih =>
    calc
      perturbLaw n w (detection (request :: requests)) ≤
          perturbLaw n w (detects request) + perturbLaw n w (detection requests) :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal w / (n : ℝ≥0∞) +
          (requests.length : ℝ≥0∞) * (ENNReal.ofReal w / (n : ℝ≥0∞)) :=
        add_le_add (one_request_detection_le request w hw) ih
      _ = ((request :: requests).length : ℝ≥0∞) * (ENNReal.ofReal w / (n : ℝ≥0∞)) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Integration over arbitrary tapes gives the true unconditional expected
count bound. The only measurability premise concerns the actual joint event;
the detection inequality is proved from concrete interval geometry above. -/
theorem integrated_detection_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (requests : Ω → List (Request n))
    (hjoint : MeasurableSet {z : Ω × (Fin n × (ℝ × Circle)) |
      z.2 ∈ detection (requests z.1)})
    (hcount : Measurable (fun tape => (requests tape).length)) :
    (μ.prod (perturbLaw n w)) {z | z.2 ∈ detection (requests z.1)} ≤
      (ENNReal.ofReal w / (n : ℝ≥0∞)) * ∫⁻ tape, ((requests tape).length : ℝ≥0∞) ∂μ := by
  let := perturbLaw_probability n hn w hw
  rw [Measure.prod_apply hjoint]
  calc
    (∫⁻ tape, perturbLaw n w (Prod.mk tape ⁻¹'
        {z | z.2 ∈ detection (requests z.1)}) ∂μ) ≤
        ∫⁻ tape, (ENNReal.ofReal w / (n : ℝ≥0∞)) *
          ((requests tape).length : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro tape
      change perturbLaw n w (detection (requests tape)) ≤ _
      simpa only [mul_comm] using transcript_detection_le (requests tape) w hw
    _ = _ := lintegral_const_mul _ ((measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp hcount)

end EnvyFreeResearch.Full.NonnegativeDetection

#print axioms EnvyFreeResearch.Full.NonnegativeDetection.one_request_detection_le
#print axioms EnvyFreeResearch.Full.NonnegativeDetection.transcript_detection_le
#print axioms EnvyFreeResearch.Full.NonnegativeDetection.integrated_detection_le
