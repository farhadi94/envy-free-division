import EnvyFreeResearch.Full.UpperDomainDifferenceCache
import EnvyFreeResearch.Full.UpperDomainDifferenceLists

/-!
# Borel refinement and subtraction for changing physical domains

A component is encoded by two real bounds and the two literal endpoint
ownership bits. Real endpoints retain their ordinary Borel structure.
The actual variable-list operations are proved measurable through the shared
length/padded-coordinate list encoding.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain UpperCircular ProtocolMeasurable

def componentCode (c : Component) : ℝ × ℝ × Bool × Bool :=
  (c.left, c.right, decide (c.left ∈ c.carrier), decide (c.right ∈ c.carrier))

instance componentMeasurableSpace : MeasurableSpace Component :=
  MeasurableSpace.comap componentCode inferInstance

theorem componentCode_measurable : Measurable componentCode := comap_measurable _

theorem component_left_measurable : Measurable Component.left :=
  measurable_fst.comp componentCode_measurable

theorem component_right_measurable : Measurable Component.right :=
  measurable_fst.comp (measurable_snd.comp componentCode_measurable)

theorem component_leftOwned_measurable : Measurable (fun c : Component => decide (c.left ∈ c.carrier)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp componentCode_measurable))

theorem component_rightOwned_measurable : Measurable (fun c : Component => decide (c.right ∈ c.carrier)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp componentCode_measurable))

/-- The measurable code determines literal membership, even for a degenerate
component. No endpoint fragment is discarded by this encoding. -/
theorem component_mem_iff (c : Component) (x : ℝ) :
    x ∈ c.carrier ↔ (c.left < x ∧ x < c.right) ∨
      (x = c.left ∧ c.left ∈ c.carrier) ∨ (x = c.right ∧ c.right ∈ c.carrier) := by
  constructor
  · intro hx
    by_cases hl : x = c.left
    · exact Or.inr (Or.inl ⟨hl, hl ▸ hx⟩)
    · by_cases hr : x = c.right
      · exact Or.inr (Or.inr ⟨hr, hr ▸ hx⟩)
      · exact Or.inl ⟨lt_of_le_of_ne (c.subset_closed hx).1 (Ne.symm hl),
          lt_of_le_of_ne (c.subset_closed hx).2 hr⟩
  · rintro (h | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact c.interior_subset h
    · exact h
    · exact h

variable {X : Type*} [MeasurableSpace X]

theorem decide_measurable (P : X → Prop) [DecidablePred P] (hP : MeasurableSet {z | P z}) :
    Measurable (fun z => decide (P z)) := by
  have h : Measurable (fun z => if P z then true else false) :=
    measurable_const.ite hP measurable_const
  convert h using 1
  funext z
  by_cases hp : P z <;> simp [hp]

theorem component_membership_measurable (c : X → Component) (p : X → ℝ)
    (hc : Measurable c) (hp : Measurable p) : MeasurableSet {z | p z ∈ (c z).carrier} := by
  have hl := component_left_measurable.comp hc
  have hr := component_right_measurable.comp hc
  have hlo : MeasurableSet {z | (c z).left ∈ (c z).carrier} := by
    simpa using measurableSet_eq_fun (component_leftOwned_measurable.comp hc)
      (show Measurable (fun _ : X => true) from measurable_const)
  have hro : MeasurableSet {z | (c z).right ∈ (c z).carrier} := by
    simpa using measurableSet_eq_fun (component_rightOwned_measurable.comp hc)
      (show Measurable (fun _ : X => true) from measurable_const)
  have h := ((measurableSet_lt hl hp).inter (measurableSet_lt hp hr)).union
    (((measurableSet_eq_fun hp hl).inter hlo).union ((measurableSet_eq_fun hp hr).inter hro))
  convert h using 1
  ext z
  exact component_mem_iff (c z) (p z)

theorem leftPart_measurable (c : X → Component) (p : X → ℝ)
    (hc : Measurable c) (hp : Measurable p)
    (hbound : ∀ z, (c z).left ≤ p z ∧ p z ≤ (c z).right) :
    Measurable (fun z => leftPart (c z) (p z) (hbound z)) := by
  have hcut := decide_measurable _ (component_membership_measurable c p hc hp)
  have ht := (component_left_measurable.comp hc).prodMk
    (hp.prodMk ((component_leftOwned_measurable.comp hc).prodMk hcut))
  apply measurable_comap_iff.mpr
  convert ht using 1
  funext z
  simp [componentCode, leftPart, (hbound z).1]

theorem rightPart_measurable (c : X → Component) (p : X → ℝ)
    (hc : Measurable c) (hp : Measurable p)
    (hbound : ∀ z, (c z).left ≤ p z ∧ p z ≤ (c z).right) :
    Measurable (fun z => rightPart (c z) (p z) (hbound z)) := by
  have hown : MeasurableSet {z | (c z).right ∈ (c z).carrier} := by
    simpa using measurableSet_eq_fun (component_rightOwned_measurable.comp hc)
      (show Measurable (fun _ : X => true) from measurable_const)
  have hbit := decide_measurable (fun z => (c z).right ∈ (c z).carrier ∧ p z < (c z).right)
    (hown.inter (measurableSet_lt hp (component_right_measurable.comp hc)))
  have ht := hp.prodMk ((component_right_measurable.comp hc).prodMk
    ((show Measurable (fun _ : X => false) from measurable_const).prodMk hbit))
  apply measurable_comap_iff.mpr
  convert ht using 1
  funext z
  change componentCode (rightPart (c z) (p z) (hbound z)) =
    (p z, (c z).right, false, decide ((c z).right ∈ (c z).carrier ∧ p z < (c z).right))
  simp [componentCode, rightPart]

theorem splitAt_measurable (c : X → Component) (p : X → ℝ)
    (hc : Measurable c) (hp : Measurable p) : Measurable (fun z => splitAt (p z) (c z)) := by
  let S : Set X := {z | (c z).left ≤ p z ∧ p z ≤ (c z).right}
  have hS : MeasurableSet S :=
    (measurableSet_le (component_left_measurable.comp hc) hp).inter
      (measurableSet_le hp (component_right_measurable.comp hc))
  have hleft := leftPart_measurable (fun z : S => c z) (fun z : S => p z)
    (hc.comp measurable_subtype_coe) (hp.comp measurable_subtype_coe) (fun z => z.property)
  have hright := rightPart_measurable (fun z : S => c z) (fun z : S => p z)
    (hc.comp measurable_subtype_coe) (hp.comp measurable_subtype_coe) (fun z => z.property)
  have hinside : Measurable (fun z : S =>
      [leftPart (c z) (p z) z.property, rightPart (c z) (p z) z.property]) :=
    measurable_list_cons.comp (hleft.prodMk (measurable_list_singleton.comp hright))
  have houtside : Measurable (fun z : (Sᶜ : Set X) => [c z]) :=
    measurable_list_singleton.comp (hc.comp measurable_subtype_coe)
  exact hinside.dite houtside hS

theorem refineAt_measurable (cs : X → List Component) (p : X → ℝ)
    (hcs : Measurable cs) (hp : Measurable p) :
    Measurable (fun z => refineAt (p z) (cs z)) :=
  list_flatMap_measurable (fun z c => splitAt (p z) c) cs
    (splitAt_measurable Prod.snd (fun q : X × Component => p q.1)
      measurable_snd (hp.comp measurable_fst)) hcs

theorem intervalAtoms_measurable (cs : X → List Component) (a b : X → ℝ)
    (hcs : Measurable cs) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun z => intervalAtoms (a z) (b z) (cs z)) := by
  apply list_filter_measurable
  · apply decide_measurable
    exact (measurableSet_lt (ha.comp measurable_fst)
      (component_right_measurable.comp measurable_snd)).inter
      (measurableSet_le (component_right_measurable.comp measurable_snd) (hb.comp measurable_fst))
  · exact hcs

theorem outsideAtoms_measurable (cs : X → List Component) (a b : X → ℝ)
    (hcs : Measurable cs) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun z => outsideAtoms (a z) (b z) (cs z)) := by
  apply list_filter_measurable
  · apply decide_measurable
    exact ((measurableSet_lt (ha.comp measurable_fst)
      (component_right_measurable.comp measurable_snd)).inter
      (measurableSet_le (component_right_measurable.comp measurable_snd) (hb.comp measurable_fst))).compl
  · exact hcs

/-- Borel measurability for a genuinely changing physical domain, including
all literal endpoint-ownership bits and every filter branch. -/
theorem removeCorrection_measurable (cs : X → List Component) (amount : X → I)
    (start : X → UpperCircular.Circle) (first last : X → ℝ)
    (hcs : Measurable cs) (hamount : Measurable amount) (hstart : Measurable start)
    (hfirst : Measurable first) (hlast : Measurable last) :
    Measurable (fun z => removeCorrection (cs z) (amount z) (start z) (first z) (last z)) := by
  classical
  have href := refineAt_measurable _ last (refineAt_measurable cs first hcs hfirst) hlast
  have hinside := intervalAtoms_measurable _ last first href hlast hfirst
  have houtside := outsideAtoms_measurable _ first last href hfirst hlast
  have hwrap : MeasurableSet {z | value (start z) < value (start z + project (amount z))} :=
    measurableSet_lt (measurable_value.comp hstart)
      (measurable_value.comp (hstart.add (measurable_project.comp hamount)))
  have hinner : Measurable (fun z =>
      if value (start z) < value (start z + project (amount z))
      then outsideAtoms (first z) (last z) (refineAt (last z) (refineAt (first z) (cs z)))
      else intervalAtoms (last z) (first z) (refineAt (last z) (refineAt (first z) (cs z)))) :=
    houtside.ite hwrap hinside
  have hone : MeasurableSet {z | amount z = 1} := measurableSet_eq_fun hamount measurable_const
  have hzero : MeasurableSet {z | amount z = 0} := measurableSet_eq_fun hamount measurable_const
  have hfull : Measurable (fun z => if amount z = 1 then [] else
      if value (start z) < value (start z + project (amount z))
      then outsideAtoms (first z) (last z) (refineAt (last z) (refineAt (first z) (cs z)))
      else intervalAtoms (last z) (first z) (refineAt (last z) (refineAt (first z) (cs z)))) :=
    (show Measurable (fun _ : X => ([] : List Component)) from measurable_const).ite hone hinner
  exact hcs.ite hzero hfull

end EnvyFreeResearch.Full.UpperDomainDifference
