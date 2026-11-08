import EnvyFreeResearch.Full.UpperWholePayments
import Mathlib.MeasureTheory.Measure.Real

/-! Literal physical unions and Borel dependence of the rounded payments. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperWholePaymentsPhysical

open UpperWholePayments

variable {Agent Cell X : Type*} [Fintype Agent] [Fintype Cell]

section Measurability

variable [MeasurableSpace X]

theorem measurableSet_mem_split (x : X → Cell → Option Agent → ℝ)
    (hx : ∀ e c, Measurable (fun z => x z e c)) (e : Cell) :
    MeasurableSet {z | e ∈ splitCells (x z)} := by
  simp only [splitCells, Finset.mem_filter, Finset.mem_univ, true_and, ofPred_exists]
  exact MeasurableSet.iUnion (fun c =>
    (measurableSet_lt measurable_const (hx e c)).inter
      (measurableSet_lt (hx e c) measurable_const))

theorem splitCells_measurable (x : X → Cell → Option Agent → ℝ)
    (hx : ∀ e c, Measurable (fun z => x z e c)) : Measurable (fun z => splitCells (x z)) := by
  apply measurable_finset_iff.mpr
  intro e
  exact measurableSet_setOfPred.mp (measurableSet_mem_split x hx e)

omit [Fintype Agent] in
theorem integralCells_measurable (x : X → Cell → Option Agent → ℝ)
    (hx : ∀ e c, Measurable (fun z => x z e c)) (j : Agent) :
    Measurable (fun z => integralCells (x z) j) := by
  apply measurable_finset_iff.mpr
  intro e
  apply measurableSet_setOfPred.mp
  simpa only [integralCells, Finset.mem_filter, Finset.mem_univ, true_and] using
    measurableSet_eq_fun (hx e (some j)) measurable_const

theorem splitValues_measurable (a : X → Agent → Cell → ℝ)
    (x : X → Cell → Option Agent → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hx : ∀ e c, Measurable (fun z => x z e c)) (i : Agent) (e : Cell) :
    Measurable (fun z => splitValues (a z) (x z) i e) :=
  (ha i e).ite (measurableSet_mem_split x hx e) measurable_const

theorem splitFractions_measurable (x : X → Cell → Option Agent → ℝ)
    (hx : ∀ e c, Measurable (fun z => x z e c)) (j : Agent) (e : Cell) :
    Measurable (fun z => splitFractions (x z) j e) :=
  (hx e (some j)).ite (measurableSet_mem_split x hx e) measurable_const

theorem splitOwned_measurable (a : X → Agent → Cell → ℝ)
    (x : X → Cell → Option Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hx : ∀ e c, Measurable (fun z => x z e c)) (heta : Measurable eta) (j : Agent) :
    Measurable (fun z => splitOwned (a z) (x z) (eta z) j) := by
  have hselect := UpperRounding.select_measurable
    (fun z => splitValues (a z) (x z)) (fun z => splitFractions (x z)) eta
    (splitValues_measurable a x ha hx) (splitFractions_measurable x hx) heta
  apply measurable_finset_iff.mpr
  intro e
  have hmem := (measurable_finset_mem e).comp ((measurable_pi_apply j).comp hselect)
  have hsplit := measurableSet_setOfPred.mp (measurableSet_mem_split x hx e)
  simpa only [splitOwned, Finset.mem_filter, Function.comp_def] using hmem.and hsplit

/-- Restoring integral cells and clipping zero-weight matches remain finite
Borel computations on the actual cached real coordinates. -/
theorem owned_measurable (a : X → Agent → Cell → ℝ)
    (x : X → Cell → Option Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hx : ∀ e c, Measurable (fun z => x z e c)) (heta : Measurable eta) :
    Measurable (fun z => owned (a z) (x z) (eta z)) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (integralCells_measurable x hx j).union_finset
    (splitOwned_measurable a x eta ha hx heta j)

theorem value_measurable (a : X → Agent → Cell → ℝ)
    (x : X → Cell → Option Agent → ℝ) (eta : X → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e))
    (hx : ∀ e c, Measurable (fun z => x z e c)) (heta : Measurable eta) (i j : Agent) :
    Measurable (fun z => value (a z) (x z) (eta z) i j) := by
  have howned := (measurable_pi_apply j).comp (owned_measurable a x eta ha hx heta)
  have hv : (fun z => value (a z) (x z) (eta z) i j) =
      fun z => ∑ e, if e ∈ owned (a z) (x z) (eta z) j then a z i e else 0 := by
    funext z
    simp only [value, Finset.sum_ite_mem_eq]
  rw [hv]
  exact Finset.measurable_sum _ (fun e _ => (ha i e).ite
    ((measurableSet_mem_finset e).preimage howned) measurable_const)

end Measurability

def piece (cells : Cell → Set ℝ) (allocation : Agent → Finset Cell) (j : Agent) : Set ℝ :=
  ⋃ e, if e ∈ allocation j then cells e else ∅

omit [Fintype Agent] [Fintype Cell] in
theorem mem_piece (cells : Cell → Set ℝ) (allocation : Agent → Finset Cell)
    (j : Agent) (z : ℝ) : z ∈ piece cells allocation j ↔ ∃ e ∈ allocation j, z ∈ cells e := by
  simp only [piece, mem_iUnion]
  apply exists_congr
  intro e
  split_ifs <;> simp_all

omit [Fintype Agent] [Fintype Cell] in
theorem piece_subset (cells : Cell → Set ℝ) (allocation : Agent → Finset Cell) (j : Agent) :
    piece cells allocation j ⊆ ⋃ e, cells e := by
  intro z hz
  obtain ⟨e, _, he⟩ := (mem_piece cells allocation j z).mp hz
  exact mem_iUnion.mpr ⟨e, he⟩

omit [Fintype Agent] in
theorem piece_measurable (cells : Cell → Set ℝ) (hmeas : ∀ e, MeasurableSet (cells e))
    (allocation : Agent → Finset Cell) (j : Agent) : MeasurableSet (piece cells allocation j) := by
  apply MeasurableSet.iUnion
  intro e
  split_ifs
  · exact hmeas e
  · exact MeasurableSet.empty

omit [Fintype Agent] [Fintype Cell] in
theorem pieces_disjoint (cells : Cell → Set ℝ)
    (hdisjoint : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (allocation : Agent → Finset Cell)
    (howned : ∀ i j, i ≠ j → Disjoint (allocation i) (allocation j)) :
    Pairwise (fun i j => Disjoint (piece cells allocation i) (piece cells allocation j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨e, hei, hez⟩ := (mem_piece cells allocation i z).mp hzi
  obtain ⟨f, hfj, hfz⟩ := (mem_piece cells allocation j z).mp hzj
  have hef : e ≠ f := by
    intro hef
    subst f
    exact Finset.disjoint_left.mp (howned i j hij) hei hfj
  exact Set.disjoint_left.mp (hdisjoint hef) hez hfz

omit [Fintype Agent] in
theorem piece_mass (μ : Measure ℝ) [IsFiniteMeasure μ] (cells : Cell → Set ℝ)
    (hmeas : ∀ e, MeasurableSet (cells e))
    (hdisjoint : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (allocation : Agent → Finset Cell) (j : Agent) :
    μ.real (piece cells allocation j) = ∑ e ∈ allocation j, μ.real (cells e) := by
  unfold piece
  rw [measureReal_iUnion_fintype]
  · simp only [apply_ite, measureReal_empty, Finset.sum_ite_mem_eq]
  · intro e f hef
    dsimp only [Function.onFun]
    split_ifs <;> simp [hdisjoint hef]
  · intro e
    split_ifs
    · exact hmeas e
    · exact MeasurableSet.empty

/-- The arithmetic value table is exactly the measures of the selected
literal unions; no additional physical realization premise is needed. -/
theorem owned_piece_mass (cost : Agent → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)]
    (cells : Cell → Set ℝ) (hmeas : ∀ e, MeasurableSet (cells e))
    (hdisjoint : Pairwise (fun e f => Disjoint (cells e) (cells f)))
    (a : Agent → Cell → ℝ) (hcache : ∀ i e, a i e = (cost i).real (cells e))
    (x : Cell → Option Agent → ℝ) (eta : ℝ) (i j : Agent) :
    (cost i).real (piece cells (owned a x eta) j) = value a x eta i j := by
  rw [piece_mass (cost i) cells hmeas hdisjoint]
  simp only [value, hcache]

end EnvyFreeResearch.Full.UpperWholePaymentsPhysical
