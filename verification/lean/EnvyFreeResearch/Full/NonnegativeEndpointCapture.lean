import EnvyFreeResearch.Full.NonnegativeMeasurableDetection
import EnvyFreeResearch.Full.NonnegativeRetainedFailure

namespace EnvyFreeResearch.Full.NonnegativeEndpointCapture

open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable
open NonnegativeOracle NonnegativeProfile NonnegativeReplay NonnegativeMeasurableDetection
open NonnegativeOutputMeasurable NonnegativeRandomOutput NonnegativeRetainedFailure
open NonnegativeEndpointLaw NonnegativeSuccess NonnegativeDetection NonnegativeExperiment Filter
open scoped Classical ENNReal Topology

variable {n : ℕ}

def returnedValue {Q R O B : Type*} (f : O → B) (default : B) (e : Execution Q R O) : B :=
  match e.stop with | .returned output => f output | _ => default

theorem measurable_returnedValue {Q R O B : Type*} [MeasurableSpace Q] [MeasurableSpace R]
    [MeasurableSpace O] [MeasurableSpace B] (f : O → B) (hf : Measurable f) (default : B) :
    Measurable (returnedValue (Q := Q) (R := R) f default) := by
  have hcode : Measurable (fun code : O ⊕ (Unit ⊕ (Q ⊕ Q)) =>
      Sum.elim f (fun _ => default) code) := hf.sumElim measurable_const
  convert hcode.comp ((comap_measurable stopCode).comp measurable_execution_stop) using 1
  funext e
  cases he : e.stop <;> simp [returnedValue, stopCode, he]

abbrev PhysicalExecution (n : ℕ) := Execution (Query (Fin n)) Reply (Allocation (Fin n))

noncomputable def queryEndpointCount (P : Profile (Fin n)) (e : PhysicalExecution n) : ℕ :=
  2 * (baselineRequests P e).length

noncomputable def queryEndpoint (P : Profile (Fin n)) (e : PhysicalExecution n) (k : ℕ) : ℝ :=
  match (baselineRequests P e)[k / 2]? with
  | some request => if k % 2 = 0 then request.left else request.right
  | none => 0

def outputEndpointCount (e : PhysicalExecution n) : ℕ := returnedValue endpointCount 0 e

def outputEndpoint (e : PhysicalExecution n) (k : ℕ) : ℝ :=
  returnedValue (fun A => endpoint A k) 0 e

/-- Every cap contributes its query endpoints, its actual returned finite
output endpoints, and the two physical boundaries. Output size is unbounded
across tapes, but this count is finite for each execution. -/
noncomputable def endpointCount (P : Profile (Fin n)) (e : PhysicalExecution n) : ℕ :=
  2 + queryEndpointCount P e + outputEndpointCount e

noncomputable def endpoint (P : Profile (Fin n)) (e : PhysicalExecution n) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then 1 else
    if k - 2 < queryEndpointCount P e then queryEndpoint P e (k - 2)
    else outputEndpoint e (k - 2 - queryEndpointCount P e)

theorem measurable_queryEndpointCount (P : Profile (Fin n))
    (hP : Measurable (IntervalOracle.oracle P)) : Measurable (queryEndpointCount P) :=
  (measurable_of_countable (fun k : ℕ => 2 * k)).comp
    (measurable_list_length.comp (measurable_baselineRequests P hP))

theorem measurable_queryEndpoint (P : Profile (Fin n))
    (hP : Measurable (IntervalOracle.oracle P)) (k : ℕ) : Measurable (fun e => queryEndpoint P e k) := by
  have hget : Measurable (fun e : PhysicalExecution n => (baselineRequests P e)[k / 2]?) :=
    (measurable_list_getElem _).comp (measurable_baselineRequests P hP)
  have hvalue : Measurable (fun q : NonnegativeDetection.Request n =>
      if k % 2 = 0 then q.left else q.right) := by
    by_cases hk : k % 2 = 0
    · simpa only [ite_eq_left hk] using measurable_request_left (n := n)
    · simpa only [ite_eq_right hk] using measurable_request_right (n := n)
  convert measurable_option_cases
    (present := fun (_ : PhysicalExecution n) (q : NonnegativeDetection.Request n) =>
      if k % 2 = 0 then q.left else q.right)
    (absent := fun (_ : PhysicalExecution n) => (0 : ℝ))
    hget (hvalue.comp measurable_snd) measurable_const using 1
  funext e
  cases hget : (baselineRequests P e)[k / 2]? <;> simp [queryEndpoint, hget]

theorem measurable_outputEndpointCount : Measurable (outputEndpointCount (n := n)) :=
  measurable_returnedValue _ NonnegativeOutputMeasurable.measurable_endpointCount _

theorem measurable_outputEndpoint (k : ℕ) : Measurable (fun e : PhysicalExecution n => outputEndpoint e k) :=
  measurable_returnedValue _ (NonnegativeOutputMeasurable.measurable_endpoint k) _

theorem measurable_endpointCount (P : Profile (Fin n))
    (hP : Measurable (IntervalOracle.oracle P)) : Measurable (endpointCount P) :=
  (measurable_of_countable (fun p : ℕ × ℕ => 2 + p.1 + p.2)).comp
    ((measurable_queryEndpointCount P hP).prodMk measurable_outputEndpointCount)

theorem measurable_endpoint (P : Profile (Fin n))
    (hP : Measurable (IntervalOracle.oracle P)) (k : ℕ) : Measurable (fun e => endpoint P e k) := by
  have hout : Measurable (fun z : PhysicalExecution n × ℕ => outputEndpoint z.1 z.2) :=
    measurable_from_prod_countable_left fun m => measurable_outputEndpoint m
  have hindex : Measurable (fun e => k - 2 - queryEndpointCount P e) :=
    (measurable_of_countable (fun m : ℕ => k - 2 - m)).comp (measurable_queryEndpointCount P hP)
  have htail := hout.comp (measurable_id.prodMk hindex)
  have htest : MeasurableSet {e : PhysicalExecution n | k - 2 < queryEndpointCount P e} :=
    measurableSet_lt measurable_const (measurable_queryEndpointCount P hP)
  unfold endpoint
  split_ifs with h0 h1
  · exact measurable_const
  · exact measurable_const
  · exact (measurable_queryEndpoint P hP (k - 2)).ite htest htail

theorem boundary_recorded (P : Profile (Fin n)) (e : PhysicalExecution n) :
    0 < endpointCount P e ∧ 1 < endpointCount P e ∧ endpoint P e 0 = 0 ∧ endpoint P e 1 = 1 := by
  constructor
  · unfold endpointCount
    omega
  constructor
  · unfold endpointCount
    omega
  simp [endpoint]

theorem query_pair_recorded (P : Profile (Fin n)) (e : PhysicalExecution n)
    (k : ℕ) (request : NonnegativeDetection.Request n)
    (hk : (baselineRequests P e)[k]? = some request) :
    2 + 2 * k < endpointCount P e ∧ 3 + 2 * k < endpointCount P e ∧
      endpoint P e (2 + 2 * k) = request.left ∧ endpoint P e (3 + 2 * k) = request.right := by
  have hkl : k < (baselineRequests P e).length := (List.getElem?_eq_some_iff.mp hk).1
  have hleft : 2 * k < queryEndpointCount P e := by unfold queryEndpointCount; omega
  have hright : 2 * k + 1 < queryEndpointCount P e := by unfold queryEndpointCount; omega
  constructor
  · unfold endpointCount
    omega
  constructor
  · unfold endpointCount
    omega
  have h20 : 2 + 2 * k ≠ 0 := by omega
  have h21 : 2 + 2 * k ≠ 1 := by omega
  have h30 : 3 + 2 * k ≠ 0 := by omega
  have h31 : 3 + 2 * k ≠ 1 := by omega
  constructor
  · simp [endpoint, h20, h21, hleft, queryEndpoint, hk]
  · have hsub : 3 + 2 * k - 2 = 2 * k + 1 := by omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    simp [endpoint, h30, h31, hsub, hright, queryEndpoint, hdiv, hmod, hk]

theorem output_recorded (P : Profile (Fin n)) (e : PhysicalExecution n)
    (A : Allocation (Fin n)) (hreturned : e.stop = .returned A)
    (k : ℕ) (hk : k < NonnegativeOutputMeasurable.endpointCount A) :
    2 + queryEndpointCount P e + k < endpointCount P e ∧
      endpoint P e (2 + queryEndpointCount P e + k) = NonnegativeOutputMeasurable.endpoint A k := by
  have hcount : outputEndpointCount e = NonnegativeOutputMeasurable.endpointCount A := by
    simp [outputEndpointCount, returnedValue, hreturned]
  constructor
  · unfold endpointCount
    omega
  · have h0 : 2 + queryEndpointCount P e + k ≠ 0 := by omega
    have h1 : 2 + queryEndpointCount P e + k ≠ 1 := by omega
    have hsub : 2 + queryEndpointCount P e + k - 2 = queryEndpointCount P e + k := by omega
    have hnot : ¬ queryEndpointCount P e + k < queryEndpointCount P e := by omega
    simp [endpoint, h0, h1, hsub, hnot, outputEndpoint, returnedValue, hreturned]

def CoordinatesSafe (P : Profile (Fin n)) (e : PhysicalExecution n) (h c d : ℝ) : Prop :=
  ∀ k < endpointCount P e, h / 2 < |c - endpoint P e k| ∧ h / 2 < |d - endpoint P e k|

theorem coordinatesSafe_query (P : Profile (Fin n)) (e : PhysicalExecution n) (h c d : ℝ)
    (hsafe : CoordinatesSafe P e h c d) : EndpointSafe h c d (determiningEndpoints P e) := by
  intro x hx
  obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hx
  have hrequest : determiningRequest P q ∈ baselineRequests P e := List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrequest
  obtain ⟨hlcount, hrcount, hl, hr⟩ := query_pair_recorded P e k (determiningRequest P q) hk
  have hleft := hsafe (2 + 2 * k) hlcount
  have hright := hsafe (3 + 2 * k) hrcount
  rw [hl] at hleft
  rw [hr] at hright
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxq
  rcases hxq with hxl | hxr
  · simpa only [hxl, determiningRequest] using hleft
  · simpa only [hxr, determiningRequest] using hright

theorem coordinatesSafe_output (P : Profile (Fin n)) (e : PhysicalExecution n) (h c d : ℝ)
    (A : Allocation (Fin n)) (hreturned : e.stop = .returned A)
    (hsafe : CoordinatesSafe P e h c d) : SafeOutput A h c d := by
  have hall (k : ℕ) (hk : k < NonnegativeOutputMeasurable.endpointCount A) :
      h / 2 < |c - NonnegativeOutputMeasurable.endpoint A k| ∧
        h / 2 < |d - NonnegativeOutputMeasurable.endpoint A k| := by
    obtain ⟨hcount, hvalue⟩ := output_recorded P e A hreturned k hk
    have hv := hsafe _ hcount
    simpa only [hvalue] using hv
  have hleft (k : Fin A.count) : h / 2 < |c - A.left k| ∧ h / 2 < |d - A.left k| := by
    obtain ⟨hcount, hvalue⟩ := left_endpoint_recorded A k
    simpa only [hvalue] using hall _ hcount
  have hright (k : Fin A.count) : h / 2 < |c - A.right k| ∧ h / 2 < |d - A.right k| := by
    obtain ⟨hcount, hvalue⟩ := right_endpoint_recorded A k
    simpa only [hvalue] using hall _ hcount
  exact ⟨fun k => (hleft k).1, fun k => (hright k).1,
    fun k => (hleft k).2, fun k => (hright k).2⟩

theorem coordinatesSafe_nonwrapping (P : Profile (Fin n)) (e : PhysicalExecution n) (h c d : ℝ)
    (hc : c ∈ Ioc (0 : ℝ) 1) (hd : d ∈ Ioc (0 : ℝ) 1)
    (hsafe : CoordinatesSafe P e h c d) :
    0 < c - h / 2 ∧ c + h / 2 < 1 ∧ 0 < d - h / 2 ∧ d + h / 2 < 1 := by
  obtain ⟨h0, h1, hv0, hv1⟩ := boundary_recorded P e
  have hs0 := hsafe 0 h0
  have hs1 := hsafe 1 h1
  rw [hv0, sub_zero, sub_zero, abs_of_pos hc.1, abs_of_pos hd.1] at hs0
  rw [hv1, abs_of_nonpos (sub_nonpos.mpr hc.2), abs_of_nonpos (sub_nonpos.mpr hd.2)] at hs1
  constructor
  · linarith [hs0.1]
  constructor
  · linarith [hs1.1]
  constructor <;> linarith [hs0.2, hs1.2]

noncomputable def outputGap (e : PhysicalExecution n) : ℝ := returnedValue uniformGap 1 e

theorem measurable_outputGap : Measurable (outputGap (n := n)) :=
  measurable_returnedValue _ measurable_uniformGap _

theorem outputGap_positive (e : PhysicalExecution n)
    (hwrong : NonnegativeSuccess.Successful {A | ¬ UniformEF A} e) : 0 < outputGap e := by
  obtain ⟨A, hreturned, hwrong⟩ := hwrong
  simpa only [outputGap, returnedValue, hreturned] using uniformGap_positive A hwrong

noncomputable def centerFirst (z : Input n) : ℝ := realFirst z.2
noncomputable def centerSecond (z : Input n) : ℝ := realSecond z.2

theorem measurable_centerFirst : Measurable (centerFirst (n := n)) :=
  measurable_realFirst.comp measurable_snd

theorem measurable_centerSecond : Measurable (centerSecond (n := n)) :=
  measurable_realSecond.comp measurable_snd

theorem centerFirst_atomless (w : ℝ) (hw : 0 < w) (a : ℝ) :
    perturbLaw n w {z | centerFirst z = a} = 0 := by
  let := NonnegativeShift.shiftLaw_probability w hw
  have heq : {z : Input n | centerFirst z = a} =
      Set.univ ×ˢ {z | realFirst z = a} := by ext z; simp [centerFirst]
  rw [heq, perturbLaw, Measure.prod_prod, realFirst_atomless w hw, mul_zero]

theorem centerSecond_atomless (w : ℝ) (hw : 0 < w) (a : ℝ) :
    perturbLaw n w {z | centerSecond z = a} = 0 := by
  let := NonnegativeShift.shiftLaw_probability w hw
  have heq : {z : Input n | centerSecond z = a} =
      Set.univ ×ˢ {z | realSecond z = a} := by ext z; simp [centerSecond]
  rw [heq, perturbLaw, Measure.prod_prod, realSecond_atomless w hw, mul_zero]

theorem coordinatesSafe_of_no_hit {Tape : Type*}
    (P : Profile (Fin n)) (execution : Tape → PhysicalExecution n)
    (tape : Tape) (input : Input n) (h : ℝ) (hh : 0 ≤ h)
    (hfirst : (tape, input) ∉ NonnegativeProbability.endpointHit
      (fun tape => endpointCount P (execution tape))
      (fun tape k => endpoint P (execution tape) k) centerFirst h)
    (hsecond : (tape, input) ∉ NonnegativeProbability.endpointHit
      (fun tape => endpointCount P (execution tape))
      (fun tape k => endpoint P (execution tape) k) centerSecond h) :
    CoordinatesSafe P (execution tape) h (centerFirst input) (centerSecond input) := by
  intro k hk
  have hc : h < |centerFirst input - endpoint P (execution tape) k| :=
    lt_of_not_ge (fun hdist => hfirst ⟨k, hk, hdist⟩)
  have hd : h < |centerSecond input - endpoint P (execution tape) k| :=
    lt_of_not_ge (fun hdist => hsecond ⟨k, hk, hdist⟩)
  constructor <;> linarith

/-- The width lemma is now instantiated with the actual variable finite
query/output endpoint code and actual wrong-output gap. Both centers use the
same observer/shift input law as the replay, detection and decoder lemmas. -/
theorem exists_actual_width {Tape : Type*} [MeasurableSpace Tape]
    (μ : Measure Tape) [IsFiniteMeasure μ] (hn : 0 < n) (w : ℝ) (hw : 0 < w)
    (P : Profile (Fin n)) (hP : Measurable (IntervalOracle.oracle P))
    (execution : Tape → PhysicalExecution n) (hexecution : Measurable execution)
    (width : ℕ → ℝ) (hwidth : ∀ m, 0 < width m)
    (hmono : Antitone width) (hlim : Tendsto width atTop (𝓝 0))
    (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ m, 0 < width m ∧ width m < 1 ∧
      (μ.prod (perturbLaw n w)) (NonnegativeProbability.endpointHit
        (fun tape => endpointCount P (execution tape))
        (fun tape k => endpoint P (execution tape) k) centerFirst (width m)) +
      (μ.prod (perturbLaw n w)) (NonnegativeProbability.endpointHit
        (fun tape => endpointCount P (execution tape))
        (fun tape k => endpoint P (execution tape) k) centerSecond (width m)) +
      μ ({tape | Successful {A | ¬ UniformEF A} (execution tape)} ∩
        {tape | outputGap (execution tape) ≤ width m}) < η := by
  let := perturbLaw_probability n hn w hw
  exact NonnegativeProbability.exists_one_width
    (fun tape => endpointCount P (execution tape))
    (fun tape k => endpoint P (execution tape) k) centerFirst centerSecond
    ((measurable_endpointCount P hP).comp hexecution)
    (fun k => (measurable_endpoint P hP k).comp hexecution)
    measurable_centerFirst measurable_centerSecond
    (centerFirst_atomless w hw) (centerSecond_atomless w hw)
    ((measurable_successful _ measurable_uniformEF.compl).preimage hexecution)
    (fun tape => outputGap (execution tape)) (measurable_outputGap.comp hexecution)
    (fun tape ht => outputGap_positive (execution tape) ht)
    width hwidth hmono hlim η hη

end EnvyFreeResearch.Full.NonnegativeEndpointCapture

#print axioms EnvyFreeResearch.Full.NonnegativeEndpointCapture.measurable_endpoint
#print axioms EnvyFreeResearch.Full.NonnegativeEndpointCapture.query_pair_recorded
#print axioms EnvyFreeResearch.Full.NonnegativeEndpointCapture.output_recorded
#print axioms EnvyFreeResearch.Full.NonnegativeEndpointCapture.coordinatesSafe_query
#print axioms EnvyFreeResearch.Full.NonnegativeEndpointCapture.coordinatesSafe_output
#print axioms EnvyFreeResearch.Full.NonnegativeEndpointCapture.exists_actual_width
