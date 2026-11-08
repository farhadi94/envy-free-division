import EnvyFreeResearch.Full.UpperRounding
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Deterministic measurable whole-cell rounding

The sorted-slot construction proves that the finite set of acceptable
ownership tables is nonempty. Selecting the first such table in a fixed
finite enumeration gives a Borel map of the cached real data. It issues no
valuation queries and needs no measurable selection theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperRounding

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

/-- A finite candidate's directly decidable cached-data test. -/
def Valid (a x : Agent → Cell → ℝ) (eta : ℝ) (owned : Agent → Finset Cell) : Prop :=
  (∀ i j, i ≠ j → Disjoint (owned i) (owned j)) ∧
    ∀ j, target a x j - eta ≤ load a owned j ∧ load a owned j ≤ target a x j

/-- Fixed-order finite search, including a total default for infeasible
inputs. The default is unused under the hypotheses of the rounding theorem. -/
def firstValid (a x : Agent → Cell → ℝ) (eta : ℝ) :
    List (Agent → Finset Cell) → (Agent → Finset Cell)
  | [] => fun _ => ∅
  | owned :: rest => if Valid a x eta owned then owned else firstValid a x eta rest

omit [Fintype Agent] in
theorem firstValid_spec (a x : Agent → Cell → ℝ) (eta : ℝ)
    (candidates : List (Agent → Finset Cell))
    (hex : ∃ owned ∈ candidates, Valid a x eta owned) :
    Valid a x eta (firstValid a x eta candidates) := by
  induction candidates with
  | nil => simp at hex
  | cons owned rest ih =>
    by_cases h : Valid a x eta owned
    · simp [firstValid, h]
    · have hrest : ∃ other ∈ rest, Valid a x eta other := by
        obtain ⟨other, hmem, hvalid⟩ := hex
        rcases List.mem_cons.mp hmem with heq | hmem
        · exact False.elim (h (heq ▸ hvalid))
        · exact ⟨other, hmem, hvalid⟩
      simpa [firstValid, h] using ih hrest

/-- The first acceptable ownership table in the fixed enumeration of all
finite tables. -/
def select (a x : Agent → Cell → ℝ) (eta : ℝ) : Agent → Finset Cell :=
  firstValid a x eta Finset.univ.toList

theorem select_spec (a x : Agent → Cell → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (hx : ∀ j e, 0 ≤ x j e) (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    Valid a x eta (select a x eta) := by
  apply firstValid_spec
  obtain ⟨owned, hdisjoint, hbounds⟩ := exists_rounding a x eta heta ha habound hx hcell
  exact ⟨owned, by simp, hdisjoint, hbounds⟩

theorem select_deficit (a x : Agent → Cell → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (hx : ∀ j e, 0 ≤ x j e) (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    (∀ i j, i ≠ j → Disjoint (select a x eta i) (select a x eta j)) ∧
      ∀ j, 0 ≤ target a x j - load a (select a x eta) j ∧
        target a x j - load a (select a x eta) j ≤ min (target a x j) eta := by
  obtain ⟨hdisjoint, hbounds⟩ := select_spec a x eta heta ha habound hx hcell
  refine ⟨hdisjoint, fun j => ⟨sub_nonneg.mpr (hbounds j).2, le_min ?_ ?_⟩⟩
  · have hnonneg : 0 ≤ load a (select a x eta) j := Finset.sum_nonneg (fun e _ => ha j e)
    linarith
  · linarith [(hbounds j).1]

section Measurability

variable {X : Type*} [MeasurableSpace X]

/-- Only finite arithmetic in ordinary Borel real coordinates enters the
candidate test. -/
theorem measurableSet_valid (a x : X → Agent → Cell → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (hx : ∀ j e, Measurable (fun z => x z j e)) (heta : Measurable eta)
    (owned : Agent → Finset Cell) :
    MeasurableSet {z | Valid (a z) (x z) (eta z) owned} := by
  have htarget (j : Agent) : Measurable (fun z => target (a z) (x z) j) :=
    Finset.measurable_sum _ (fun e _ => (ha j e).mul (hx j e))
  have hload (j : Agent) : Measurable (fun z => load (a z) owned j) :=
    Finset.measurable_sum _ (fun e _ => ha j e)
  have hbounds : MeasurableSet {z | ∀ j,
      target (a z) (x z) j - eta z ≤ load (a z) owned j ∧
        load (a z) owned j ≤ target (a z) (x z) j} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j =>
      (measurableSet_le ((htarget j).sub heta) (hload j)).inter
        (measurableSet_le (hload j) (htarget j)))
  exact (MeasurableSet.const (∀ i j, i ≠ j → Disjoint (owned i) (owned j))).inter hbounds

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

/-- The deterministic selector is measurable even on infeasible inputs.
The output measurable space can be the usual finite discrete encoding. -/
theorem select_measurable (a x : X → Agent → Cell → ℝ) (eta : X → ℝ)
    (ha : ∀ j e, Measurable (fun z => a z j e))
    (hx : ∀ j e, Measurable (fun z => x z j e)) (heta : Measurable eta) :
    Measurable (fun z => select (a z) (x z) (eta z)) :=
  firstValid_measurable a x eta ha hx heta _

end Measurability

end EnvyFreeResearch.Full.UpperRounding
