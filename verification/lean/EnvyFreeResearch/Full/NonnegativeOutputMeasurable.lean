import EnvyFreeResearch.Full.IntervalAllocation

/-! The natural measurable finite-output encoding: a count, padded real
endpoint coordinates, padded owner coordinates, and the owner of point zero.
Proof fields impose geometric validity without altering the observable code.
-/

namespace EnvyFreeResearch.Full.NonnegativeOutputMeasurable

open MeasureTheory Set IntervalAllocation

variable {Agent : Type*}

def paddedLeft (A : Allocation Agent) (k : ℕ) : ℝ :=
  if hk : k < A.count then A.left ⟨k, hk⟩ else 0

def paddedRight (A : Allocation Agent) (k : ℕ) : ℝ :=
  if hk : k < A.count then A.right ⟨k, hk⟩ else 0

def paddedOwner (A : Allocation Agent) (k : ℕ) : Agent :=
  if hk : k < A.count then A.owner ⟨k, hk⟩ else A.endpointOwner

def encode (A : Allocation Agent) :
    ℕ × ((ℕ → ℝ) × ((ℕ → ℝ) × ((ℕ → Agent) × Agent))) :=
  (A.count, paddedLeft A, paddedRight A, paddedOwner A, A.endpointOwner)

instance allocationMeasurableSpace [MeasurableSpace Agent] : MeasurableSpace (Allocation Agent) :=
  MeasurableSpace.comap encode inferInstance

theorem measurable_encode [MeasurableSpace Agent] : Measurable (encode (Agent := Agent)) :=
  comap_measurable encode

theorem measurable_count [MeasurableSpace Agent] :
    Measurable (fun A : Allocation Agent => A.count) := measurable_fst.comp measurable_encode

theorem measurable_paddedLeft [MeasurableSpace Agent] (k : ℕ) :
    Measurable (fun A : Allocation Agent => paddedLeft A k) :=
  (measurable_pi_apply k).comp (measurable_fst.comp (measurable_snd.comp measurable_encode))

theorem measurable_paddedRight [MeasurableSpace Agent] (k : ℕ) :
    Measurable (fun A : Allocation Agent => paddedRight A k) :=
  (measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_encode)))

theorem measurable_paddedOwner [MeasurableSpace Agent] (k : ℕ) :
    Measurable (fun A : Allocation Agent => paddedOwner A k) :=
  (measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_encode))))

theorem measurable_endpointOwner [MeasurableSpace Agent] :
    Measurable (fun A : Allocation Agent => A.endpointOwner) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_encode)))

def endpointCount (A : Allocation Agent) : ℕ := 2 * A.count + 2

def endpoint (A : Allocation Agent) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then 1 else
    if (k - 2) % 2 = 0 then paddedLeft A ((k - 2) / 2) else paddedRight A ((k - 2) / 2)

theorem measurable_endpointCount [MeasurableSpace Agent] :
    Measurable (endpointCount (Agent := Agent)) :=
  (measurable_of_countable (fun n : ℕ => 2 * n + 2)).comp measurable_count

theorem measurable_endpoint [MeasurableSpace Agent] (k : ℕ) :
    Measurable (fun A : Allocation Agent => endpoint A k) := by
  unfold endpoint
  split_ifs
  · exact measurable_const
  · exact measurable_const
  · exact measurable_paddedLeft _
  · exact measurable_paddedRight _

theorem left_endpoint_recorded (A : Allocation Agent) (k : Fin A.count) :
    2 * k.val + 2 < endpointCount A ∧ endpoint A (2 * k.val + 2) = A.left k := by
  constructor
  · dsimp only [endpointCount]
    omega
  · have h0 : 2 * k.val + 2 ≠ 0 := by omega
    have h1 : 2 * k.val + 2 ≠ 1 := by omega
    simp [endpoint, h1, paddedLeft, k.isLt]

theorem right_endpoint_recorded (A : Allocation Agent) (k : Fin A.count) :
    2 * k.val + 3 < endpointCount A ∧ endpoint A (2 * k.val + 3) = A.right k := by
  constructor
  · dsimp only [endpointCount]
    omega
  · have h0 : 2 * k.val + 3 ≠ 0 := by omega
    have h1 : 2 * k.val + 3 ≠ 1 := by omega
    have hs : 2 * k.val + 3 - 2 = 2 * k.val + 1 := by omega
    have hd : (2 * k.val + 1) / 2 = k.val := by omega
    simp [endpoint, h1, hs, hd, paddedRight, k.isLt]

/-- Joint membership of an actual output share is measurable directly from
the output code, with a countable union over finite record coordinates. -/
theorem measurable_share_membership [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    (i : Agent) : MeasurableSet {z : Allocation Agent × ℝ | z.2 ∈ z.1.share i} := by
  have hpositive : MeasurableSet {z : Allocation Agent × ℝ | z.2 ∈ z.1.positiveShare i} := by
    have heq : {z : Allocation Agent × ℝ | z.2 ∈ z.1.positiveShare i} =
        ⋃ k : ℕ, {z : Allocation Agent × ℝ | k < z.1.count} ∩
          {z | paddedOwner z.1 k = i} ∩
          {z | paddedLeft z.1 k < z.2} ∩ {z | z.2 ≤ paddedRight z.1 k} := by
      ext z
      simp only [Allocation.mem_positiveShare, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_Ioc]
      constructor
      · rintro ⟨k, hk, hl, hr⟩
        exact ⟨k.val, ⟨⟨k.isLt, by simpa [paddedOwner, k.isLt] using hk⟩,
          by simpa [paddedLeft, k.isLt] using hl⟩, by simpa [paddedRight, k.isLt] using hr⟩
      · rintro ⟨k, ⟨⟨hk, ho⟩, hl⟩, hr⟩
        refine ⟨⟨k, hk⟩, ?_, ?_, ?_⟩
        · simpa [paddedOwner, hk] using ho
        · simpa [paddedLeft, hk] using hl
        · simpa [paddedRight, hk] using hr
    rw [heq]
    apply MeasurableSet.iUnion
    intro k
    exact (((measurableSet_lt measurable_const (measurable_count.comp measurable_fst)).inter
      ((measurableSet_singleton i).preimage ((measurable_paddedOwner k).comp measurable_fst))).inter
      (measurableSet_lt ((measurable_paddedLeft k).comp measurable_fst) measurable_snd)).inter
      (measurableSet_le measurable_snd ((measurable_paddedRight k).comp measurable_fst))
  have heq : {z : Allocation Agent × ℝ | z.2 ∈ z.1.share i} =
      {z : Allocation Agent × ℝ | z.2 ∈ z.1.positiveShare i} ∪
      ({z | z.1.endpointOwner = i} ∩ {z | z.2 = 0}) := by
    ext z
    simp [Allocation.mem_share, eq_comm]
  rw [heq]
  exact hpositive.union
    (((measurableSet_singleton i).preimage (measurable_endpointOwner.comp measurable_fst)).inter
      (measurableSet_eq_fun measurable_snd measurable_const))

end EnvyFreeResearch.Full.NonnegativeOutputMeasurable

#print axioms EnvyFreeResearch.Full.NonnegativeOutputMeasurable.measurable_share_membership
#print axioms EnvyFreeResearch.Full.NonnegativeOutputMeasurable.left_endpoint_recorded
#print axioms EnvyFreeResearch.Full.NonnegativeOutputMeasurable.right_endpoint_recorded
