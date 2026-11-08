import EnvyFreeResearch.Full.RawPartition
import EnvyFreeResearch.Full.MixedDensity

/-!
Unsorted finite interval records, with geometric proof fields removed.
Only the first `count` records are used. Validation checks boundedness,
disjointness and coverage, independently of valuations. A countable rational
coverage test is proved equivalent to exact coverage for finite half-open
records; no sorting or bound on the number of records is needed.
-/

noncomputable section
namespace EnvyFreeResearch.Full.RawIntervalPartition

open Set MeasureTheory IntervalAllocation NonnegativeOutputMeasurable ProtocolMeasurable
open scoped Classical

structure Raw (Agent : Type*) where
  count : ℕ
  left : ℕ → ℝ
  right : ℕ → ℝ
  owner : ℕ → Agent
  endpointOwner : Agent

variable {Agent : Type*}

def Bounded (r : Raw Agent) : Prop :=
  ∀ k < r.count, 0 ≤ r.left k ∧ r.left k ≤ r.right k ∧ r.right k ≤ 1

def Separated (r : Raw Agent) : Prop :=
  ∀ k < r.count, ∀ m < r.count, k ≠ m →
    min (r.right k) (r.right m) ≤ max (r.left k) (r.left m)

def RationalCover (r : Raw Agent) : Prop :=
  ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ 1 →
    ∃ k < r.count, r.left k < (q : ℝ) ∧ (q : ℝ) ≤ r.right k

def Valid (r : Raw Agent) : Prop := Bounded r ∧ Separated r ∧ RationalCover r

theorem intervals_disjoint (r : Raw Agent) (h : Separated r) :
    Pairwise (fun k m : Fin r.count =>
      Disjoint (Ioc (r.left k.val) (r.right k.val)) (Ioc (r.left m.val) (r.right m.val))) := by
  intro k m hkm
  exact Set.Ioc_disjoint_Ioc.mpr
    (h k.val k.isLt m.val m.isLt (fun he => hkm (Fin.ext he)))

/-- A missing point in a finite union of right-closed intervals forces a
missing rational immediately to its left. This also checks the endpoint 1. -/
theorem covers_of_rational (r : Raw Agent) (h : RationalCover r)
    (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∃ k : Fin r.count, x ∈ Ioc (r.left k.val) (r.right k.val) := by
  by_contra hmissing
  have hmiss : ∀ k : Fin r.count, ¬ (r.left k.val < x ∧ x ≤ r.right k.val) := by
    simpa only [not_exists, mem_Ioc] using hmissing
  let s : Finset ℝ := insert 0 ((Finset.range r.count).image
    (fun k => if r.right k < x then r.right k else 0))
  have hs : s.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hbelow : ∀ y ∈ s, y < x := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hzero | hy
    · simpa only [hzero] using hx.1
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
      split_ifs with hr
      · exact hr
      · exact hx.1
  have hb : s.max' hs < x := hbelow _ (Finset.max'_mem s hs)
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hb
  have hz : (0 : ℝ) ≤ s.max' hs := Finset.le_max' s 0 (Finset.mem_insert_self _ _)
  obtain ⟨k, hk, hl, hr⟩ := h q (hz.trans_lt hqlo) (hqhi.le.trans hx.2)
  have hrx : r.right k < x := by
    by_contra hn
    exact hmiss ⟨k, hk⟩ ⟨hl.trans hqhi, le_of_not_gt hn⟩
  have hmem : r.right k ∈ s := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_range.mpr hk, ite_eq_left hrx⟩
  have hrmax := Finset.le_max' s (r.right k) hmem
  exact (not_lt_of_ge hrmax) (hqlo.trans_le hr)

theorem intervals_cover (r : Raw Agent) (hb : Bounded r) (hc : RationalCover r) :
    (⋃ k : Fin r.count, Ioc (r.left k.val) (r.right k.val)) = Ioc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨(hb k.val k.isLt).1.trans_lt hk.1, hk.2.trans (hb k.val k.isLt).2.2⟩
  · intro hx
    exact mem_iUnion.mpr (covers_of_rational r hc x hx)

theorem rationalCover_of_cover (r : Raw Agent)
    (hc : (⋃ k : Fin r.count, Ioc (r.left k.val) (r.right k.val)) = Ioc (0 : ℝ) 1) :
    RationalCover r := by
  intro q hq0 hq1
  have hq : (q : ℝ) ∈ ⋃ k : Fin r.count, Ioc (r.left k.val) (r.right k.val) := by
    rw [hc]
    exact ⟨hq0, hq1⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp hq
  exact ⟨k.val, k.isLt, hk⟩

/-- The validation predicate is exactly the original geometric proof fields,
expressed in a measurable syntax. -/
theorem valid_iff_geometry (r : Raw Agent) :
    Valid r ↔ Bounded r ∧
      Pairwise (fun k m : Fin r.count =>
        Disjoint (Ioc (r.left k.val) (r.right k.val)) (Ioc (r.left m.val) (r.right m.val))) ∧
      (⋃ k : Fin r.count, Ioc (r.left k.val) (r.right k.val)) = Ioc (0 : ℝ) 1 := by
  constructor
  · rintro ⟨hb, hs, hc⟩
    exact ⟨hb, intervals_disjoint r hs, intervals_cover r hb hc⟩
  · rintro ⟨hb, hs, hc⟩
    refine ⟨hb, ?_, rationalCover_of_cover r hc⟩
    intro k hk m hm hkm
    have hne : (⟨k, hk⟩ : Fin r.count) ≠ ⟨m, hm⟩ :=
      fun he => hkm (congrArg Fin.val he)
    exact Set.Ioc_disjoint_Ioc.mp (hs hne)

def allocation (r : Raw Agent) (h : Valid r) : Allocation Agent where
  count := r.count
  left k := r.left k.val
  right k := r.right k.val
  owner k := r.owner k.val
  endpointOwner := r.endpointOwner
  bounded k := h.1 k.val k.isLt
  disjoint := intervals_disjoint r h.2.1
  covers := intervals_cover r h.1 h.2.2

def decode (r : Raw Agent) : Option (Allocation Agent) :=
  if h : Valid r then some (allocation r h) else none

theorem decode_some_iff (r : Raw Agent) (A : Allocation Agent) :
    decode r = some A ↔ ∃ h : Valid r, allocation r h = A := by
  unfold decode
  by_cases h : Valid r <;> simp [h]

theorem decode_none_iff (r : Raw Agent) : decode r = none ↔ ¬ Valid r := by
  unfold decode
  by_cases h : Valid r <;> simp [h]

def share (r : Raw Agent) (i : Agent) : Set ℝ :=
  (⋃ k : Fin r.count, if r.owner k.val = i then Ioc (r.left k.val) (r.right k.val) else ∅) ∪
    (if i = r.endpointOwner then {0} else ∅)

theorem share_measurable (r : Raw Agent) (i : Agent) : MeasurableSet (share r i) := by
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro k
    split_ifs
    · exact measurableSet_Ioc
    · exact MeasurableSet.empty
  · split_ifs
    · exact measurableSet_singleton 0
    · exact MeasurableSet.empty

theorem allocation_share (r : Raw Agent) (h : Valid r) (i : Agent) :
    (allocation r h).share i = share r i := rfl

theorem decoded_share (r : Raw Agent) (A : Allocation Agent) (hd : decode r = some A) (i : Agent) :
    A.share i = share r i := by
  obtain ⟨h, rfl⟩ := (decode_some_iff r A).mp hd
  rfl

theorem decoded_value (r : Raw Agent) (A : Allocation Agent) (hd : decode r = some A)
    (R : MixedDensity.Row) (i : Agent) :
    R.signedMeasure (A.share i) = R.signedMeasure (share r i) := by
  rw [decoded_share r A hd i]

def ofAllocation (A : Allocation Agent) : Raw Agent :=
  ⟨A.count, paddedLeft A, paddedRight A, paddedOwner A, A.endpointOwner⟩

theorem ofAllocation_valid (A : Allocation Agent) : Valid (ofAllocation A) := by
  apply (valid_iff_geometry _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    change k < A.count at hk
    simpa [ofAllocation, paddedLeft, paddedRight, hk] using A.bounded ⟨k, hk⟩
  · change Pairwise (fun k m : Fin A.count =>
      Disjoint (Ioc (paddedLeft A k.val) (paddedRight A k.val))
        (Ioc (paddedLeft A m.val) (paddedRight A m.val)))
    intro k m hkm
    simpa only [paddedLeft, paddedRight, dite_eq_left k.isLt, dite_eq_left m.isLt] using A.disjoint hkm
  · simpa [ofAllocation, paddedLeft, paddedRight] using A.covers

theorem allocation_ofAllocation (A : Allocation Agent) :
    allocation (ofAllocation A) (ofAllocation_valid A) = A := by
  cases A
  simp [allocation, ofAllocation, paddedLeft, paddedRight, paddedOwner]

theorem decode_ofAllocation (A : Allocation Agent) : decode (ofAllocation A) = some A := by
  exact (decode_some_iff _ _).mpr ⟨ofAllocation_valid A, allocation_ofAllocation A⟩

def code (r : Raw Agent) :
    ℕ × ((ℕ → ℝ) × ((ℕ → ℝ) × ((ℕ → Agent) × Agent))) :=
  (r.count, r.left, r.right, r.owner, r.endpointOwner)

instance [MeasurableSpace Agent] : MeasurableSpace (Raw Agent) :=
  MeasurableSpace.comap code inferInstance

theorem measurable_code [MeasurableSpace Agent] : Measurable (code (Agent := Agent)) :=
  comap_measurable _
theorem measurable_count [MeasurableSpace Agent] : Measurable (Raw.count (Agent := Agent)) :=
  measurable_fst.comp measurable_code
theorem measurable_left [MeasurableSpace Agent] (k : ℕ) : Measurable (fun r : Raw Agent => r.left k) :=
  (measurable_pi_apply k).comp (measurable_fst.comp (measurable_snd.comp measurable_code))
theorem measurable_right [MeasurableSpace Agent] (k : ℕ) : Measurable (fun r : Raw Agent => r.right k) :=
  (measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_code)))
theorem measurable_owner [MeasurableSpace Agent] (k : ℕ) : Measurable (fun r : Raw Agent => r.owner k) :=
  (measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_code))))
theorem measurable_endpointOwner [MeasurableSpace Agent] :
    Measurable (Raw.endpointOwner (Agent := Agent)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_code)))

theorem bounded_measurable [MeasurableSpace Agent] : MeasurableSet {r : Raw Agent | Bounded r} := by
  have heq : {r : Raw Agent | Bounded r} = ⋂ k : ℕ,
      ({r | k < r.count}ᶜ ∪ {r | 0 ≤ r.left k} ∩ {r | r.left k ≤ r.right k} ∩ {r | r.right k ≤ 1}) := by
    ext r
    simp [Bounded, imp_iff_not_or, and_assoc]
  rw [heq]
  exact MeasurableSet.iInter (fun k =>
    (measurableSet_lt measurable_const measurable_count).compl.union
      (((measurableSet_le measurable_const (measurable_left k)).inter
        (measurableSet_le (measurable_left k) (measurable_right k))).inter
        (measurableSet_le (measurable_right k) measurable_const)))

theorem separated_measurable [MeasurableSpace Agent] :
    MeasurableSet {r : Raw Agent | Separated r} := by
  have heq : {r : Raw Agent | Separated r} = ⋂ k : ℕ, ⋂ m : ℕ,
      ({r | k < r.count ∧ m < r.count ∧ k ≠ m}ᶜ ∪
        {r | min (r.right k) (r.right m) ≤ max (r.left k) (r.left m)}) := by
    ext r
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq, Separated]
    constructor
    · intro h k m
      by_cases ht : k < r.count ∧ m < r.count ∧ k ≠ m
      · exact Or.inr (h k ht.1 m ht.2.1 ht.2.2)
      · exact Or.inl ht
    · intro h k hk m hm hkm
      exact (h k m).resolve_left (fun hn => hn ⟨hk, hm, hkm⟩)
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro m
  have hconst : MeasurableSet {r : Raw Agent | k ≠ m} := by
    by_cases h : k ≠ m
    · have heq : {r : Raw Agent | k ≠ m} = Set.univ := by ext r; simp [h]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {r : Raw Agent | k ≠ m} = ∅ := by ext r; simp [h]
      rw [heq]
      exact MeasurableSet.empty
  have ht : MeasurableSet {r : Raw Agent | k < r.count ∧ m < r.count ∧ k ≠ m} :=
    (measurableSet_lt measurable_const measurable_count).inter
      ((measurableSet_lt measurable_const measurable_count).inter hconst)
  exact ht.compl.union (measurableSet_le
    ((measurable_right k).min (measurable_right m)) ((measurable_left k).max (measurable_left m)))

theorem rationalCover_measurable [MeasurableSpace Agent] :
    MeasurableSet {r : Raw Agent | RationalCover r} := by
  have heq : {r : Raw Agent | RationalCover r} = ⋂ q : ℚ,
      ({r : Raw Agent | ¬ (0 < (q : ℝ) ∧ (q : ℝ) ≤ 1)} ∪
        ⋃ k : ℕ, {r | k < r.count} ∩ {r | r.left k < (q : ℝ)} ∩ {r | (q : ℝ) ≤ r.right k}) := by
    ext r
    simp [RationalCover, imp_iff_not_or, or_assoc, and_assoc]
  rw [heq]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.union
  · by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) ≤ 1 <;> simp [h]
  · exact MeasurableSet.iUnion (fun k =>
      ((measurableSet_lt measurable_const measurable_count).inter
        (measurableSet_lt (measurable_left k) measurable_const)).inter
          (measurableSet_le measurable_const (measurable_right k)))

theorem valid_measurable [MeasurableSpace Agent] : MeasurableSet {r : Raw Agent | Valid r} :=
  bounded_measurable.inter (separated_measurable.inter rationalCover_measurable)

theorem allocation_measurable [MeasurableSpace Agent] :
    Measurable (fun r : {r : Raw Agent // Valid r} => allocation r.val r.property) := by
  apply measurable_comap_iff.mpr
  have hc : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.count) :=
    measurable_count.comp measurable_subtype_coe
  have he : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.endpointOwner) :=
    measurable_endpointOwner.comp measurable_subtype_coe
  have hl (k : ℕ) : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.left k) :=
    (measurable_left k).comp measurable_subtype_coe
  have hr (k : ℕ) : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.right k) :=
    (measurable_right k).comp measurable_subtype_coe
  have ho (k : ℕ) : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.owner k) :=
    (measurable_owner k).comp measurable_subtype_coe
  have ht (k : ℕ) : MeasurableSet {r : {r : Raw Agent // Valid r} | k < r.val.count} :=
    measurableSet_lt measurable_const hc
  have hleft : Measurable (fun r : {r : Raw Agent // Valid r} =>
      fun k => if k < r.val.count then r.val.left k else (0 : ℝ)) :=
    Measurable.of_eval (fun k => (hl k).ite (ht k) measurable_const)
  have hright : Measurable (fun r : {r : Raw Agent // Valid r} =>
      fun k => if k < r.val.count then r.val.right k else (0 : ℝ)) :=
    Measurable.of_eval (fun k => (hr k).ite (ht k) measurable_const)
  have howner : Measurable (fun r : {r : Raw Agent // Valid r} =>
      fun k => if k < r.val.count then r.val.owner k else r.val.endpointOwner) :=
    Measurable.of_eval (fun k => (ho k).ite (ht k) he)
  convert hc.prodMk (hleft.prodMk (hright.prodMk (howner.prodMk he))) using 1
  funext r
  simp [encode, allocation]
  constructor
  · funext k
    simp [paddedLeft]
  · constructor
    · funext k
      simp [paddedRight]
    · funext k
      simp [paddedOwner]

theorem decode_measurable [MeasurableSpace Agent] : Measurable (decode (Agent := Agent)) :=
  Measurable.dite (measurable_some.comp allocation_measurable) measurable_const valid_measurable

theorem ofAllocation_measurable [MeasurableSpace Agent] :
    Measurable (ofAllocation (Agent := Agent)) :=
  measurable_comap_iff.mpr measurable_encode

/-- Any alternate assignment of the finitely many record endpoints has the
same value under every actual integrable density row. -/
def endpoints (r : Raw Agent) : Set ℝ :=
  {0} ∪ Set.range (fun k : Fin r.count => r.left k.val) ∪
    Set.range (fun k : Fin r.count => r.right k.val)

theorem endpoints_finite (r : Raw Agent) : (endpoints r).Finite :=
  ((Set.finite_singleton 0).union (Set.finite_range _)).union (Set.finite_range _)

theorem value_eq_of_endpoint_change (r : Raw Agent) (R : MixedDensity.Row) (i : Agent)
    (S : Set ℝ) (hS : MeasurableSet S)
    (haway : ∀ x ∉ endpoints r, x ∈ S ↔ x ∈ share r i) :
    R.signedMeasure S = R.signedMeasure (share r i) := by
  rw [MixedDensity.Row.signedMeasure_apply R S hS,
    MixedDensity.Row.signedMeasure_apply R _ (share_measurable r i)]
  apply setIntegral_congr_set
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((endpoints_finite r).measure_zero volume)] with x hx
  exact propext (haway x hx)

end EnvyFreeResearch.Full.RawIntervalPartition

#print axioms EnvyFreeResearch.Full.RawIntervalPartition.valid_iff_geometry
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.decode_measurable
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.decode_ofAllocation
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.ofAllocation_measurable
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.value_eq_of_endpoint_change
