import EnvyFreeResearch.Full.UpperQuantileExecution
import Mathlib.Data.Fin.Tuple.Sort

/-! A finite measurable sorting algorithm for recorded real endpoints. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperSortedGrid

variable {m : ℕ}

def SortedBy (values : Fin m → ℝ) (order : Equiv.Perm (Fin m)) : Prop :=
  Monotone (values ∘ order)

def firstSorted (values : Fin m → ℝ) : List (Equiv.Perm (Fin m)) → Equiv.Perm (Fin m)
  | [] => Equiv.refl _
  | order :: rest => if SortedBy values order then order else firstSorted values rest

theorem firstSorted_spec (values : Fin m → ℝ) (orders : List (Equiv.Perm (Fin m)))
    (hex : ∃ order ∈ orders, SortedBy values order) : SortedBy values (firstSorted values orders) := by
  induction orders with
  | nil => simp at hex
  | cons order rest ih =>
    by_cases h : SortedBy values order
    · simpa only [firstSorted, ite_eq_left h] using h
    · have he : ∃ other ∈ rest, SortedBy values other := by
        obtain ⟨other, hmem, hs⟩ := hex
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact False.elim (h hs)
        · exact ⟨other, hmem, hs⟩
      simpa only [firstSorted, ite_eq_right h] using ih he

def select (values : Fin m → ℝ) : Equiv.Perm (Fin m) := firstSorted values Finset.univ.toList

def sorted (values : Fin m → ℝ) : Fin m → ℝ := values ∘ select values

theorem sorted_monotone (values : Fin m → ℝ) : Monotone (sorted values) := by
  apply firstSorted_spec
  exact ⟨Tuple.sort values, by simp, Tuple.monotone_sort values⟩

theorem sorted_contains (values : Fin m → ℝ) (i : Fin m) :
    ∃ j, sorted values j = values i := by
  exact ⟨(select values).symm i, by simp [sorted]⟩

theorem sorted_bounds (values : Fin m → ℝ) (hvalues : ∀ i, 0 ≤ values i ∧ values i ≤ 1)
    (i : Fin m) : 0 ≤ sorted values i ∧ sorted values i ≤ 1 := hvalues (select values i)

theorem first_eq_zero (values : Fin (m + 1) → ℝ)
    (hvalues : ∀ i, 0 ≤ values i) (hzero : ∃ i, values i = 0) : sorted values 0 = 0 := by
  obtain ⟨i, hi⟩ := hzero
  obtain ⟨j, hj⟩ := sorted_contains values i
  have h := sorted_monotone values (Fin.zero_le j)
  rw [hj, hi] at h
  exact le_antisymm h (hvalues (select values 0))

theorem last_eq_one (values : Fin (m + 1) → ℝ)
    (hvalues : ∀ i, values i ≤ 1) (hone : ∃ i, values i = 1) : sorted values (Fin.last m) = 1 := by
  obtain ⟨i, hi⟩ := hone
  obtain ⟨j, hj⟩ := sorted_contains values i
  have h := sorted_monotone values (Fin.le_last j)
  rw [hj, hi] at h
  exact le_antisymm (hvalues (select values (Fin.last m))) h

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_sortedBy (values : X → Fin m → ℝ)
    (hvalues : ∀ i, Measurable (fun x => values x i)) (order : Equiv.Perm (Fin m)) :
    MeasurableSet {x | SortedBy (values x) order} := by
  simp only [SortedBy, Monotone, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hij
  exact measurableSet_le (hvalues (order i)) (hvalues (order j))

theorem firstSorted_measurable (values : X → Fin m → ℝ)
    (hvalues : ∀ i, Measurable (fun x => values x i)) (orders : List (Equiv.Perm (Fin m))) :
    Measurable (fun x => firstSorted (values x) orders) := by
  induction orders with
  | nil => exact measurable_const
  | cons order rest ih =>
    exact measurable_const.ite (measurableSet_sortedBy values hvalues order) ih

theorem select_measurable (values : X → Fin m → ℝ)
    (hvalues : ∀ i, Measurable (fun x => values x i)) : Measurable (fun x => select (values x)) :=
  firstSorted_measurable values hvalues _

/-- Real endpoints retain their standard Borel measurable structure. Only
the finite permutation search uses a discrete output. -/
theorem sorted_measurable (values : X → Fin m → ℝ)
    (hvalues : ∀ i, Measurable (fun x => values x i)) : Measurable (fun x => sorted (values x)) := by
  apply Measurable.of_eval
  intro i
  have hindex : Measurable (fun x => select (values x) i) :=
    (measurable_of_countable (fun order : Equiv.Perm (Fin m) => order i)).comp
      (select_measurable values hvalues)
  exact (UpperRepresentatives.score_eval_measurable values hvalues).comp
    (measurable_id.prodMk hindex)

end Measurability

end EnvyFreeResearch.Full.UpperSortedGrid
