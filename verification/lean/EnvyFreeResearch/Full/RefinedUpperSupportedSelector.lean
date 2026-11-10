import EnvyFreeResearch.Full.RefinedUpperSupportedRounding
import EnvyFreeResearch.Full.UpperRoundingMeasurable

/-! A finite Borel selector for supported sorted-slot rounding. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperSupportedSelector
open UpperRounding
variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def Valid (a x : Agent → Cell → ℝ) (eta : ℝ) (owned : Agent → Finset Cell) : Prop :=
  UpperRounding.Valid a x eta owned ∧ ∀ j e, e ∈ owned j → 0 < x j e

def firstValid (a x : Agent → Cell → ℝ) (eta : ℝ) :
    List (Agent → Finset Cell) → Agent → Finset Cell
  | [] => fun _ => ∅
  | owned::rest => if Valid a x eta owned then owned else firstValid a x eta rest

theorem firstValid_spec (a x : Agent → Cell → ℝ) (eta : ℝ)
    (candidates : List (Agent → Finset Cell))
    (hex : ∃ owned ∈ candidates, Valid a x eta owned) :
    Valid a x eta (firstValid a x eta candidates) := by
  induction candidates with
  | nil => simp at hex
  | cons owned rest ih =>
    by_cases h : Valid a x eta owned
    · simp [firstValid,h]
    · have hrest : ∃ other ∈ rest, Valid a x eta other := by
        obtain ⟨other,hmem,hvalid⟩ := hex
        rcases List.mem_cons.mp hmem with heq|hmem
        · exact False.elim (h (heq ▸ hvalid))
        · exact ⟨other,hmem,hvalid⟩
      simpa [firstValid,h] using ih hrest

def select (a x : Agent → Cell → ℝ) (eta : ℝ) : Agent → Finset Cell :=
  firstValid a x eta Finset.univ.toList

theorem select_full_spec (a x : Agent → Cell → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (hx : ∀ j e, 0 ≤ x j e) (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    Valid a x eta (select a x eta) := by
  apply firstValid_spec
  obtain ⟨owned,hd,hb,hs⟩ :=
    RefinedUpperSupportedRounding.exists_supported_rounding a x eta heta ha habound hx hcell
  exact ⟨owned,by simp,⟨hd,hb⟩,hs⟩

theorem select_spec (a x : Agent → Cell → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (hx : ∀ j e, 0 ≤ x j e) (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    UpperRounding.Valid a x eta (select a x eta) :=
  (select_full_spec a x eta heta ha habound hx hcell).1

section Measurability
variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_valid (a x : X → Agent → Cell → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (hx : ∀ j e, Measurable (fun z => x z j e)) (heta : Measurable eta)
    (owned : Agent → Finset Cell) : MeasurableSet {z | Valid (a z) (x z) (eta z) owned} := by
  have hs : MeasurableSet {z | ∀ j e, e ∈ owned j → 0 < x z j e} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro e
    by_cases he : e ∈ owned j
    · simpa [he] using measurableSet_lt (measurable_const (a := (0 : ℝ))) (hx j e)
    · simp [he]
  exact (UpperRounding.measurableSet_valid a x eta ha hx heta owned).inter hs

variable [MeasurableSpace (Agent → Finset Cell)]
theorem firstValid_measurable (a x : X → Agent → Cell → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (hx : ∀ j e, Measurable (fun z => x z j e)) (heta : Measurable eta)
    (candidates : List (Agent → Finset Cell)) :
    Measurable (fun z => firstValid (a z) (x z) (eta z) candidates) := by
  induction candidates with
  | nil => exact measurable_const
  | cons owned rest ih =>
    exact measurable_const.ite (measurableSet_valid a x eta ha hx heta owned) ih

theorem select_measurable (a x : X → Agent → Cell → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (hx : ∀ j e, Measurable (fun z => x z j e)) (heta : Measurable eta) :
    Measurable (fun z => select (a z) (x z) (eta z)) :=
  firstValid_measurable a x eta ha hx heta _
end Measurability
end EnvyFreeResearch.Full.RefinedUpperSupportedSelector
