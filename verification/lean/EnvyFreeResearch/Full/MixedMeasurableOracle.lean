import EnvyFreeResearch.Full.IntervalOracle
import EnvyFreeResearch.Full.ProtocolMeasurable

/-! Borel measurability of the actual least-root rule. Existence of a root
below a fixed coordinate is a closed event: it is a projection with compact
witness space [0,1]. This avoids assuming measurable root selection. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedMeasurableOracle
open Set MeasureTheory ExtremalRoots IntervalOracle
open scoped Classical

abbrev Parameters := ℝ × ℝ × ℝ
abbrev UnitInterval := Icc (0 : ℝ) 1

def RootBelow (F : ℝ → ℝ) (q : ℝ) (p : Parameters) : Prop :=
  ∃ x ∈ Icc (0 : ℝ) 1,
    p.1 ≤ x ∧ x ≤ p.2.1 ∧ x ≤ q ∧ F x = F p.1 + p.2.2

theorem rootBelow_closed (F : ℝ → ℝ) (hF : Continuous F) (q : ℝ) :
    IsClosed {p | RootBelow F q p} := by
  let C : Set (Parameters × UnitInterval) := {z |
    z.1.1 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ z.1.2.1 ∧ (z.2 : ℝ) ≤ q ∧
      F z.2 = F z.1.1 + z.1.2.2}
  have hc1 : IsClosed {z : Parameters × UnitInterval | z.1.1 ≤ (z.2 : ℝ)} := by
    apply isClosed_le <;> fun_prop
  have hc2 : IsClosed {z : Parameters × UnitInterval | (z.2 : ℝ) ≤ z.1.2.1} := by
    apply isClosed_le <;> fun_prop
  have hc3 : IsClosed {z : Parameters × UnitInterval | (z.2 : ℝ) ≤ q} := by
    apply isClosed_le <;> fun_prop
  have hc4 : IsClosed {z : Parameters × UnitInterval | F z.2 = F z.1.1 + z.1.2.2} := by
    apply isClosed_eq
    · exact hF.comp (by fun_prop)
    · exact (hF.comp (by fun_prop)).add (by fun_prop)
  have hC : IsClosed C := hc1.inter (hc2.inter (hc3.inter hc4))
  have heq : Prod.fst '' C = {p | RootBelow F q p} := by
    ext p
    constructor
    · rintro ⟨⟨p', x⟩, hx, rfl⟩
      exact ⟨x, x.property, hx⟩
    · rintro ⟨x, hx, hrest⟩
      exact ⟨(p, ⟨x, hx⟩), hrest, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace C hC

def PhysicalLegal (F : ℝ → ℝ) (p : Parameters) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧ LegalTarget F p.1 p.2.1 p.2.2

theorem physicalLegal_closed (F : ℝ → ℝ) (hF : Continuous F) :
    IsClosed {p | PhysicalLegal F p} := by
  have h0 : IsClosed {p : Parameters | 0 ≤ p.1} := by apply isClosed_le <;> fun_prop
  have h1 : IsClosed {p : Parameters | p.1 ≤ p.2.1} := by apply isClosed_le <;> fun_prop
  have h2 : IsClosed {p : Parameters | p.2.1 ≤ 1} := by apply isClosed_le <;> fun_prop
  have h3 : IsClosed {p : Parameters | min 0 (F p.2.1 - F p.1) ≤ p.2.2} := by
    apply isClosed_le
    · exact continuous_const.min ((hF.comp (by fun_prop)).sub (hF.comp (by fun_prop)))
    · fun_prop
  have h4 : IsClosed {p : Parameters | p.2.2 ≤ max 0 (F p.2.1 - F p.1)} := by
    apply isClosed_le
    · fun_prop
    · exact continuous_const.max ((hF.comp (by fun_prop)).sub (hF.comp (by fun_prop)))
  exact h0.inter (h1.inter (h2.inter (h3.inter h4)))

variable {Agent : Type*}

def boundedFirst (P : Profile Agent) (i : Agent) (p : Parameters) : ℝ :=
  if PhysicalLegal (P.cumulative i) p then firstCut P i p.1 p.2.1 p.2.2 else 0

theorem boundedFirst_lt_iff (P : Profile Agent) (i : Agent) (p : Parameters) (z : ℝ) :
    boundedFirst P i p < z ↔
      (¬ PhysicalLegal (P.cumulative i) p ∧ 0 < z) ∨
      (PhysicalLegal (P.cumulative i) p ∧
        ∃ q : ℚ, (q : ℝ) < z ∧ RootBelow (P.cumulative i) q p) := by
  by_cases hp : PhysicalLegal (P.cumulative i) p
  · simp only [boundedFirst, hp, not_true_eq_false, false_and,
      false_or, true_and]
    have hr := firstCut_spec P i p.1 p.2.1 p.2.2 hp.2.1 hp.2.2.2
    constructor
    · intro hlt
      obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlt
      exact ⟨q, hqhi, firstCut P i p.1 p.2.1 p.2.2,
        ⟨hp.1.trans hr.location.1, hr.location.2.trans hp.2.2.1⟩,
        hr.location.1, hr.location.2, hqlo.le, hr.equation⟩
    · rintro ⟨q, hq, x, hx, hax, hxb, hxq, heq⟩
      exact (hr.first x ⟨hax, hxb⟩ heq).trans_lt (hxq.trans_lt hq)
  · simp [boundedFirst, hp]

theorem boundedFirst_measurable (P : Profile Agent) (i : Agent) :
    Measurable (boundedFirst P i) := by
  apply measurable_of_Iio
  intro z
  have heq : boundedFirst P i ⁻¹' Iio z =
      ({p | ¬ PhysicalLegal (P.cumulative i) p} ∩ {p : Parameters | 0 < z}) ∪
      ({p | PhysicalLegal (P.cumulative i) p} ∩
        ⋃ q : ℚ, {p : Parameters | (q : ℝ) < z} ∩ {p | RootBelow (P.cumulative i) q p}) := by
    ext p
    simp only [mem_preimage, mem_Iio, boundedFirst_lt_iff, mem_union, mem_inter_iff,
      mem_ofPred_eq, mem_iUnion]
  rw [heq]
  have hlegal := (physicalLegal_closed (P.cumulative i) (P.continuous i)).measurableSet
  apply MeasurableSet.union
  · exact hlegal.compl.inter (by by_cases h : (0 : ℝ) < z <;> simp [h])
  · apply hlegal.inter
    apply MeasurableSet.iUnion
    intro q
    have hq : MeasurableSet {p : Parameters | (q : ℝ) < z} := by
      by_cases h : (q : ℝ) < z <;> simp [h]
    exact hq.inter (rootBelow_closed (P.cumulative i) (P.continuous i) q).measurableSet

/-- The standard shared disjoint-union encoding of a real reply or failure. -/
abbrev optionRealCode : Option ℝ → ℝ ⊕ Unit := ProtocolMeasurable.optionCode

abbrev optionRealMeasurable : MeasurableSpace (Option ℝ) :=
  ProtocolMeasurable.optionMeasurableSpace

theorem measurable_some_real : Measurable (some : ℝ → Option ℝ) :=
  ProtocolMeasurable.measurable_some

/-- Actual signed Cut replies, including the terminal illegal case, are Borel
functions of all three real query parameters. -/
theorem cut_oracle_measurable (P : Profile Agent) (i : Agent) :
    Measurable (fun p : Parameters => oracle P (.cut i p.1 p.2.1 p.2.2)) := by
  have heq : (fun p : Parameters => oracle P (.cut i p.1 p.2.1 p.2.2)) =
      (fun p => if PhysicalLegal (P.cumulative i) p then
        some (boundedFirst P i p) else none) := by
    funext p
    by_cases hp : PhysicalLegal (P.cumulative i) p
    · have hlegal : Legal P (.cut i p.1 p.2.1 p.2.2) := hp
      simp only [oracle, ite_eq_left hlegal, boundedFirst, ite_eq_left hp]
    · have hlegal : ¬ Legal P (.cut i p.1 p.2.1 p.2.2) := hp
      simp only [oracle, ite_eq_right hlegal, ite_eq_right hp]
  rw [heq]
  exact (measurable_some_real.comp (boundedFirst_measurable P i)).ite
    (physicalLegal_closed (P.cumulative i) (P.continuous i)).measurableSet measurable_const

end EnvyFreeResearch.Full.MixedMeasurableOracle
