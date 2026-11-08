import EnvyFreeResearch.Full.NonnegativeOutputMeasurable
import EnvyFreeResearch.Full.ProtocolMeasurable

/-!
A concrete finite-coordinate output syntax. The first count+1 cut
coordinates and first count owners describe adjacent intervals. Trailing
coordinates are ignored. Invalid order, endpoints, or zero-count output
are rejected by a measurable geometric check; no valuation is inspected.
-/

noncomputable section
namespace EnvyFreeResearch.Full.RawPartition
open Set MeasureTheory IntervalAllocation NonnegativeOutputMeasurable ProtocolMeasurable
open scoped Classical

structure Raw (Agent : Type*) where
  count : ℕ
  cut : ℕ → ℝ
  owner : ℕ → Agent
  endpointOwner : Agent

variable {Agent : Type*}

def Valid (r : Raw Agent) : Prop :=
  r.cut 0 = 0 ∧ r.cut r.count = 1 ∧ ∀ k < r.count, r.cut k ≤ r.cut (k+1)

theorem cut_mono (r : Raw Agent) (h : Valid r) :
    Monotone (fun k : Fin (r.count+1) => r.cut k.val) :=
  Fin.monotone_iff_le_succ.mpr (fun k => h.2.2 k.val k.isLt)

theorem cut_le (r : Raw Agent) (h : Valid r) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ r.count) :
    r.cut a ≤ r.cut b :=
  cut_mono r h (a := ⟨a,by omega⟩) (b := ⟨b,by omega⟩) hab

theorem cut_bounds (r : Raw Agent) (h : Valid r) (k : Fin r.count) :
    0 ≤ r.cut k.val ∧ r.cut k.val ≤ r.cut (k.val+1) ∧ r.cut (k.val+1) ≤ 1 := by
  refine ⟨?_,h.2.2 k.val k.isLt,?_⟩
  · simpa only [h.1] using cut_le r h (a := 0) (b := k.val) (Nat.zero_le _) k.isLt.le
  · simpa only [h.2.1] using cut_le r h (a := k.val+1) (b := r.count)
      (by omega) le_rfl

theorem interval_disjoint (r : Raw Agent) (h : Valid r) :
    Pairwise (fun k m : Fin r.count => Disjoint
      (Ioc (r.cut k.val) (r.cut (k.val+1))) (Ioc (r.cut m.val) (r.cut (m.val+1)))) := by
  intro k m hkm
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hne : k.val ≠ m.val := fun he => hkm (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle := cut_le r h (a := k.val+1) (b := m.val) (by omega) m.isLt.le
    linarith [hx.2,hy.1]
  · have hle := cut_le r h (a := m.val+1) (b := k.val) (by omega) k.isLt.le
    linarith [hy.2,hx.1]

theorem intervals_cover (r : Raw Agent) (h : Valid r) :
    (⋃ k : Fin r.count, Ioc (r.cut k.val) (r.cut (k.val+1))) = Ioc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    exact ⟨(cut_bounds r h k).1.trans_lt hk.1, hk.2.trans (cut_bounds r h k).2.2⟩
  · intro hx
    have hex : ∃ k : ℕ, k ≤ r.count ∧ x ≤ r.cut k :=
      ⟨r.count,le_rfl,by simpa only [h.2.1] using hx.2⟩
    let k := Nat.find hex
    have hk : k ≤ r.count ∧ x ≤ r.cut k := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra hn
      have hz : k = 0 := by omega
      rw [hz,h.1] at hk
      linarith [hx.1]
    have hprev : r.cut (k-1) < x := by
      by_contra hn
      have hc := Nat.find_min hex (show k-1 < k by omega)
      exact hc ⟨by omega,le_of_not_gt hn⟩
    refine mem_iUnion.mpr ⟨⟨k-1,by omega⟩,hprev,?_⟩
    simpa only [show k-1+1 = k by omega] using hk.2

def allocation (r : Raw Agent) (h : Valid r) : Allocation Agent where
  count := r.count
  left k := r.cut k.val
  right k := r.cut (k.val+1)
  owner k := r.owner k.val
  endpointOwner := r.endpointOwner
  bounded := cut_bounds r h
  disjoint := interval_disjoint r h
  covers := intervals_cover r h

def decode (r : Raw Agent) : Option (Allocation Agent) :=
  if h : Valid r then some (allocation r h) else none

theorem decode_some_iff (r : Raw Agent) (A : Allocation Agent) :
    decode r = some A ↔ ∃ h : Valid r, allocation r h = A := by
  unfold decode
  by_cases h : Valid r <;> simp [h]

def code (r : Raw Agent) : ℕ × ((ℕ → ℝ) × ((ℕ → Agent) × Agent)) :=
  (r.count,r.cut,r.owner,r.endpointOwner)

instance [MeasurableSpace Agent] : MeasurableSpace (Raw Agent) :=
  MeasurableSpace.comap code inferInstance

theorem measurable_code [MeasurableSpace Agent] : Measurable (code (Agent := Agent)) := comap_measurable _
theorem measurable_raw_count [MeasurableSpace Agent] : Measurable (Raw.count (Agent := Agent)) :=
  measurable_fst.comp measurable_code
theorem measurable_raw_cut [MeasurableSpace Agent] (k : ℕ) : Measurable (fun r : Raw Agent => r.cut k) :=
  (measurable_pi_apply k).comp (measurable_fst.comp (measurable_snd.comp measurable_code))
theorem measurable_raw_owner [MeasurableSpace Agent] (k : ℕ) : Measurable (fun r : Raw Agent => r.owner k) :=
  (measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_code)))
theorem measurable_raw_endpointOwner [MeasurableSpace Agent] :
    Measurable (Raw.endpointOwner (Agent := Agent)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_code))

theorem valid_measurable [MeasurableSpace Agent] : MeasurableSet {r : Raw Agent | Valid r} := by
  have hjoint : Measurable (fun p : Raw Agent × ℕ => p.1.cut p.2) :=
    measurable_from_prod_countable_left measurable_raw_cut
  have hlast := hjoint.comp (measurable_id.prodMk measurable_raw_count)
  have heq : {r : Raw Agent | Valid r} = {r | r.cut 0 = 0} ∩
      {r | r.cut r.count = 1} ∩ ⋂ k : ℕ, ({r | k < r.count}ᶜ ∪ {r | r.cut k ≤ r.cut (k+1)}) := by
    ext r
    simp [Valid, and_assoc, imp_iff_not_or]
  rw [heq]
  refine ((measurableSet_eq_fun (measurable_raw_cut 0) measurable_const).inter
    (measurableSet_eq_fun hlast measurable_const)).inter ?_
  exact MeasurableSet.iInter (fun k =>
    (measurableSet_lt measurable_const measurable_raw_count).compl.union
      (measurableSet_le (measurable_raw_cut k) (measurable_raw_cut (k+1))))

theorem allocation_measurable [MeasurableSpace Agent] :
    Measurable (fun r : {r : Raw Agent // Valid r} => allocation r.val r.property) := by
  apply measurable_comap_iff.mpr
  have hc : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.count) :=
    measurable_raw_count.comp measurable_subtype_coe
  have he : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.endpointOwner) :=
    measurable_raw_endpointOwner.comp measurable_subtype_coe
  have hl (k : ℕ) : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.cut k) :=
    (measurable_raw_cut (Agent := Agent) k).comp measurable_subtype_coe
  have ho (k : ℕ) : Measurable (fun r : {r : Raw Agent // Valid r} => r.val.owner k) :=
    (measurable_raw_owner (Agent := Agent) k).comp measurable_subtype_coe
  have htest (k : ℕ) : MeasurableSet {r : {r : Raw Agent // Valid r} | k < r.val.count} :=
    measurableSet_lt measurable_const hc
  have hleft : Measurable (fun r : {r : Raw Agent // Valid r} =>
      fun k => if k < r.val.count then r.val.cut k else (0 : ℝ)) :=
    Measurable.of_eval (fun k => (hl k).ite (htest k) measurable_const)
  have hright : Measurable (fun r : {r : Raw Agent // Valid r} =>
      fun k => if k < r.val.count then r.val.cut (k+1) else (0 : ℝ)) :=
    Measurable.of_eval (fun k => (hl (k+1)).ite (htest k) measurable_const)
  have howner : Measurable (fun r : {r : Raw Agent // Valid r} =>
      fun k => if k < r.val.count then r.val.owner k else r.val.endpointOwner) :=
    Measurable.of_eval (fun k => (ho k).ite (htest k) he)
  convert hc.prodMk (hleft.prodMk (hright.prodMk (howner.prodMk he))) using 1
  funext r
  simp [encode,allocation]
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

end EnvyFreeResearch.Full.RawPartition
