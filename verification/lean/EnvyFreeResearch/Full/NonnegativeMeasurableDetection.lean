import EnvyFreeResearch.Full.NonnegativeExperiment
import EnvyFreeResearch.Full.NonnegativeReplay

namespace EnvyFreeResearch.Full.NonnegativeMeasurableDetection

open MeasureTheory Set IntervalOracle OracleProtocol ProtocolMeasurable
open NonnegativeGeometry NonnegativeShift NonnegativeEndpointLaw NonnegativeDetection
open NonnegativeOracle NonnegativeProfile NonnegativeMeasurableOracle NonnegativeReplay
open scoped Classical

abbrev Circle := NonnegativeCircle.Circle

/-- Quotient arc membership has a countable ordinary-interval description,
valid for every finite real bracket, including malformed query coordinates. -/
theorem arc_membership_iff (a b : ℝ) (x : Circle) :
    x ∈ arc a b ↔ ∃ k : ℤ, a ≤ representative x + k ∧ representative x + k ≤ b := by
  constructor
  · rintro ⟨t, ht, heq⟩
    have hzero : ((t - representative x : ℝ) : Circle) = 0 := by
      rw [AddCircle.coe_sub, heq, representative_coe, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
    have htk : t = representative x + k := by
      simp only [zsmul_eq_mul, mul_one] at hk
      linarith
    exact ⟨k, by simpa only [← htk, Set.mem_Icc] using ht⟩
  · rintro ⟨k, hleft, hright⟩
    refine ⟨representative x + k, ⟨hleft, hright⟩, ?_⟩
    have hk : ((k : ℝ) : Circle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
    rw [AddCircle.coe_add, representative_coe, hk, add_zero]

theorem measurable_arc_membership :
    MeasurableSet {z : ℝ × ℝ × Circle | z.2.2 ∈ arc z.1 z.2.1} := by
  have heq : {z : ℝ × ℝ × Circle | z.2.2 ∈ arc z.1 z.2.1} =
      ⋃ k : ℤ, {z | z.1 ≤ representative z.2.2 + k} ∩
        {z | representative z.2.2 + k ≤ z.2.1} := by
    ext z
    simp only [mem_ofPred_eq, arc_membership_iff, mem_iUnion, mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  have hr : Measurable (fun z : ℝ × ℝ × Circle => representative z.2.2 + k) :=
    (measurable_representative.comp (measurable_snd.comp measurable_snd)).add_const k
  exact (measurableSet_le measurable_fst hr).inter
    (measurableSet_le hr (measurable_fst.comp measurable_snd))

def requestCode {n : ℕ} (q : Request n) : Fin n × ℝ × ℝ := (q.observer, q.left, q.right)

instance requestMeasurableSpace {n : ℕ} : MeasurableSpace (Request n) :=
  MeasurableSpace.comap requestCode inferInstance

theorem measurable_requestCode {n : ℕ} : Measurable (requestCode (n := n)) := comap_measurable _

theorem measurable_request_observer {n : ℕ} : Measurable (Request.observer (n := n)) :=
  measurable_fst.comp measurable_requestCode

theorem measurable_request_left {n : ℕ} : Measurable (Request.left (n := n)) :=
  measurable_fst.comp (measurable_snd.comp measurable_requestCode)

theorem measurable_request_right {n : ℕ} : Measurable (Request.right (n := n)) :=
  measurable_snd.comp (measurable_snd.comp measurable_requestCode)

theorem measurable_joint_detects {n : ℕ} :
    MeasurableSet {z : Request n × (Fin n × (ℝ × Circle)) | z.2 ∈ detects z.1} := by
  have hleft : Measurable (fun z : Request n × (Fin n × (ℝ × Circle)) => z.1.left) :=
    measurable_request_left.comp measurable_fst
  have hright : Measurable (fun z : Request n × (Fin n × (ℝ × Circle)) => z.1.right) :=
    measurable_request_right.comp measurable_fst
  have hc : Measurable (fun z : Request n × (Fin n × (ℝ × Circle)) => first z.2.2) :=
    measurable_first.comp (measurable_snd.comp measurable_snd)
  have hd : Measurable (fun z : Request n × (Fin n × (ℝ × Circle)) => second z.2.2) :=
    measurable_second.comp (measurable_snd.comp measurable_snd)
  have hC := measurable_arc_membership.preimage (hleft.prodMk (hright.prodMk hc))
  have hD := measurable_arc_membership.preimage (hleft.prodMk (hright.prodMk hd))
  have hobs : MeasurableSet {z : Request n × (Fin n × (ℝ × Circle)) | z.2.1 = z.1.observer} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (measurable_request_observer.comp measurable_fst)
  have heq : {z : Request n × (Fin n × (ℝ × Circle)) | z.2 ∈ detects z.1} =
      {z | z.2.1 = z.1.observer} ∩
        (({z | first z.2.2 ∈ arc z.1.left z.1.right} \ {z | second z.2.2 ∈ arc z.1.left z.1.right}) ∪
        ({z | second z.2.2 ∈ arc z.1.left z.1.right} \ {z | first z.2.2 ∈ arc z.1.left z.1.right})) := by
    ext z
    simp only [detects, mem_prod, mem_singleton_iff, mem_ofPred_eq, mem_inter_iff, mem_union,
      mem_sdiff]
    tauto
  rw [heq]
  exact hobs.inter ((hC.diff hD).union (hD.diff hC))

/-- Maps of finite lists are measurable in the shared length/padded-option
encoding. In particular, a query transcript is converted into determining
intervals without a measurability assumption on that conversion. -/
theorem measurable_list_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) : Measurable (List.map f) := by
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · simpa only [listCode, Function.comp_def, List.length_map] using
      (measurable_list_length (α := α))
  · apply Measurable.of_eval
    intro k
    have hopt : Measurable (fun xs : List α =>
        match xs[k]? with | some a => some (f a) | none => none) := by
      convert measurable_option_cases (value := fun xs : List α => xs[k]?)
        (present := fun (_ : List α) a => some (f a)) (absent := fun _ => none)
        (measurable_list_getElem k) (measurable_some.comp (hf.comp measurable_snd))
        measurable_const using 1
    simp only [listCode, Function.comp_def, List.getElem?_map]
    convert hopt using 1
    funext xs
    cases xs[k]? <;> rfl

theorem measurable_query_agent {Agent : Type*} [MeasurableSpace Agent] :
    Measurable (Query.agent (Agent := Agent)) := by
  apply measurable_query_cases <;> exact measurable_fst

theorem measurable_determiningRight {Agent : Type*} [MeasurableSpace Agent]
    (P : Profile Agent) (horacle : Measurable (IntervalOracle.oracle P)) :
    Measurable (determiningRight P) := by
  apply measurable_query_cases
  · exact measurable_snd.comp measurable_snd
  · have ho : Measurable (fun p : Agent × ℝ × ℝ × ℝ =>
        IntervalOracle.oracle P (.cut p.1 p.2.1 p.2.2.1 p.2.2.2)) :=
      horacle.comp measurable_query_cut
    have hr : Measurable (fun p : Agent × ℝ × ℝ × ℝ => p.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    convert measurable_option_cases (present := fun (_ : Agent × ℝ × ℝ × ℝ) r => r)
      (absent := fun p => p.2.2.1) ho measurable_snd hr using 1
    funext p
    cases hreply : IntervalOracle.oracle P (.cut p.1 p.2.1 p.2.2.1 p.2.2.2) <;>
      simp only [determiningRight, hreply, Query.right]

theorem measurable_determiningRequest {n : ℕ} (P : Profile (Fin n))
    (horacle : Measurable (IntervalOracle.oracle P)) : Measurable (determiningRequest P) := by
  apply measurable_comap_iff.mpr
  exact measurable_query_agent.prodMk
    (measurable_query_left.prodMk (measurable_determiningRight P horacle))

theorem measurable_some_relation {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (relation : Set (α × β)) (hrelation : MeasurableSet relation) :
    MeasurableSet {z : Option α × β | ∃ a, z.1 = some a ∧ (a, z.2) ∈ relation} := by
  let distribute := MeasurableEquiv.prodSumDistrib β α Unit
  let swapped : Set (β × α) := Prod.swap ⁻¹' relation
  have hcode : Measurable (fun z : Option α × β => (z.2, optionCode z.1)) :=
    measurable_snd.prodMk (measurable_optionCode.comp measurable_fst)
  have hinl (b : β) (a : α) : distribute (b, Sum.inl a) = Sum.inl (b, a) := rfl
  have hinr (b : β) (u : Unit) : distribute (b, Sum.inr u) = Sum.inr (b, u) := rfl
  have heq : {z : Option α × β | ∃ a, z.1 = some a ∧ (a, z.2) ∈ relation} =
      (fun z => distribute (z.2, optionCode z.1)) ⁻¹' (Sum.inl '' swapped) := by
    ext z
    rcases z with ⟨opt, b⟩
    cases opt <;> simp [optionCode, hinl, hinr, swapped]
  rw [heq]
  exact (hrelation.preimage measurable_swap).inl_image.preimage (distribute.measurable.comp hcode)

theorem measurable_joint_detection {n : ℕ} :
    MeasurableSet {z : List (Request n) × (Fin n × (ℝ × Circle)) | z.2 ∈ detection z.1} := by
  have heq : {z : List (Request n) × (Fin n × (ℝ × Circle)) | z.2 ∈ detection z.1} =
      ⋃ k : ℕ, {z | ∃ request, z.1[k]? = some request ∧ z.2 ∈ detects request} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_detection_iff]
    constructor
    · rintro ⟨request, hrequest, hdetect⟩
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrequest
      exact ⟨k, request, hk, hdetect⟩
    · rintro ⟨k, request, hk, hdetect⟩
      exact ⟨request, List.mem_iff_getElem?.mpr ⟨k, hk⟩, hdetect⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  exact (measurable_some_relation _ measurable_joint_detects).preimage
    (((measurable_list_getElem k).comp measurable_fst).prodMk measurable_snd)

def illegalList {Query Output : Type*} : Stop Query Output → List Query
  | .illegal q => [q]
  | _ => []

theorem measurable_illegalList {Query Output : Type*} [MeasurableSpace Query]
    [MeasurableSpace Output] : Measurable (illegalList (Query := Query) (Output := Output)) := by
  have hcode : Measurable (fun code : Output ⊕ (Unit ⊕ (Query ⊕ Query)) =>
      Sum.elim (fun _ => ([] : List Query))
        (Sum.elim (fun _ => []) (Sum.elim (fun q => [q]) (fun _ => []))) code) :=
    measurable_const.sumElim
      (measurable_const.sumElim (measurable_list_singleton.sumElim measurable_const))
  convert hcode.comp (comap_measurable stopCode) using 1
  funext stop
  cases stop <;> rfl

theorem measurable_determiningRequests {Query Reply Output : Type*}
    [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output] :
    Measurable (determiningRequests (Query := Query) (Reply := Reply) (Output := Output)) := by
  exact measurable_list_append.comp
    (((measurable_list_map Prod.fst measurable_fst).comp measurable_execution_answered).prodMk
      (measurable_illegalList.comp measurable_execution_stop))

theorem measurable_baselineRequests {n : ℕ} {Output : Type*} [MeasurableSpace Output]
    (P : Profile (Fin n)) (horacle : Measurable (IntervalOracle.oracle P)) :
    Measurable (baselineRequests (Output := Output) P) :=
  (measurable_list_map _ (measurable_determiningRequest P horacle)).comp measurable_determiningRequests

/-- The actual adaptive baseline trace automatically supplies the joint
detection measurability required by the sharp integrated detection theorem. -/
theorem actual_detection_measurable {n : ℕ} {Tape Output : Type*}
    [MeasurableSpace Tape] [MeasurableSpace Output]
    (next : Protocol Tape (Query (Fin n)) Reply Output)
    (P : Profile (Fin n)) (flag : Bool)
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (horacle : Measurable (IntervalOracle.oracle P))
    (hflagged : Measurable (flaggedOracle flag P)) (fuel : ℕ) :
    MeasurableSet {z : Tape × (Fin n × (ℝ × Circle)) | z.2 ∈ detection
      (baselineRequests P (run next (flaggedOracle flag P) z.1 fuel []))} := by
  exact measurable_joint_detection.preimage
    (((measurable_baselineRequests P horacle).comp
      ((measurable_run_at_history next (flaggedOracle flag P) hnext hflagged fuel []).comp
        measurable_fst)).prodMk measurable_snd)

end EnvyFreeResearch.Full.NonnegativeMeasurableDetection

#print axioms EnvyFreeResearch.Full.NonnegativeMeasurableDetection.measurable_joint_detects
#print axioms EnvyFreeResearch.Full.NonnegativeMeasurableDetection.measurable_determiningRequest
#print axioms EnvyFreeResearch.Full.NonnegativeMeasurableDetection.actual_detection_measurable
