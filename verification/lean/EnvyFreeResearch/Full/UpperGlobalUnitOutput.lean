import EnvyFreeResearch.Full.UpperGlobalProtocolMeasurable
import EnvyFreeResearch.Full.UpperGlobalNormalizeCorrectness

/-! Finite real endpoint output for the public closed unit interval.
Each interval records both endpoint ownership bits, including degenerate
components. Decoding retains every null fragment without extra queries. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalUnit
open UpperRecordedDomain UpperCorrectionExecution UpperDomainDifference UpperGlobalPhysical
variable {n : ℕ}

abbrev IntervalCode := ℝ × ℝ × Bool × Bool

def decode (c : IntervalCode) : Set ℝ :=
  Ioo c.1 c.2.1 ∪ (if c.2.2.1 then {c.1} else ∅) ∪
    (if c.2.2.2 then {c.2.1} else ∅)

def output (a : Anchor n) (j : Fin n) : List IntervalCode :=
  (a.bundles j).cells.map componentCode

def share (codes : Fin n → List IntervalCode) (j : Fin n) : Set ℝ :=
  ⋃ c ∈ codes j, decode c

theorem decode_component (c : Component) : decode (componentCode c)=c.carrier := by
  ext x
  rw [component_mem_iff]
  simp only [decode,componentCode,Set.mem_union,Set.mem_Ioo]
  by_cases hl : c.left ∈ c.carrier <;> by_cases hr : c.right ∈ c.carrier <;>
    simp [hl,hr,or_assoc]

theorem output_share (a : Anchor n) (j : Fin n) :
    share (output a) j=domain (a.bundles j).cells := by
  ext x
  simp only [share,output,Set.mem_iUnion,List.mem_map]
  constructor
  · rintro ⟨code,⟨c,hc,rfl⟩,hx⟩
    exact mem_domain.mpr ⟨c,hc,(decode_component c) ▸ hx⟩
  · intro hx
    obtain ⟨c,hc,hx⟩ := mem_domain.mp hx
    exact ⟨componentCode c,⟨c,hc,rfl⟩,(decode_component c).symm ▸ hx⟩

theorem output_measurable : Measurable (output (n := n)) := by
  apply Measurable.of_eval
  intro j
  apply list_map_measurable
  · exact componentCode_measurable.comp measurable_snd
  · exact state_cells_measurable.comp
      ((measurable_pi_apply j).comp anchor_bundles_measurable)

theorem output_bounds (a : Anchor n) (j : Fin n) (code : IntervalCode)
    (hc : code ∈ output a j) : 0 ≤ code.1 ∧ code.1 ≤ code.2.1 ∧ code.2.1 ≤ 1 := by
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hc
  exact ⟨c.left_nonneg,c.left_le_right,c.right_le_one⟩

theorem output_measurableSet (a : Anchor n) (j : Fin n) :
    MeasurableSet (share (output a) j) := by
  rw [output_share]
  exact domain_measurable _

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem terminal_output (chores : Bool) (a : Anchor n)
    (ha : UpperGlobalNormalize.Normalized μ chores (Icc 0 1) (.done a)) :
    Pairwise (fun i j => Disjoint (share (output a) i) (share (output a) j)) ∧
      (⋃ j, share (output a) j)=Icc 0 1 ∧
      GlobalCompletion.EnvyFree (if chores then .chore else .cake)
        (fun i j => (μ i).real (share (output a) j)) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [output_share] using ha.1.1.pairwise
  · simpa only [output_share] using ha.2.2
  · simp only [output_share]
    exact ha.1.2.2.2.1

end EnvyFreeResearch.Full.UpperGlobalUnit
