import EnvyFreeResearch.Full.ChoresMulticolorKernel
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! A fractional variable belongs to at most r observer/color equations.
At a basic point there are at least half as many active equations as
fractional variables, so one active equation sees at most 2r variables. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Multicolor
open UpperFloating UpperFloatingStep
open scoped Classical BigOperators

variable {Observer Cell Color : Type*}
  [Fintype Observer] [Fintype Cell] [Fintype Color]

def rowSupport (free : Finset (Cell × Color)) (row : Observer × Color) : Finset (Cell × Color) :=
  free.filter (fun c => c.2=row.2)

theorem column_incidence_le (active : Finset (Observer × Color)) (c : Cell × Color) :
    (active.filter (fun row => c.2=row.2)).card ≤ Fintype.card Observer := by
  let f : (active.filter (fun row => c.2=row.2)) → Observer := fun row => row.val.1
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    exact (Finset.mem_filter.mp a.property).2.symm.trans (Finset.mem_filter.mp b.property).2
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem total_incidence_le (active : Finset (Observer × Color)) (free : Finset (Cell × Color)) :
    (∑ row ∈ active, (rowSupport free row).card) ≤ Fintype.card Observer*free.card := by
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := active) (t := free) (fun row c => c.2=row.2)
  change (∑ row ∈ active, (free.filter (fun c => c.2=row.2)).card) ≤ _
  rw [show (∑ row ∈ active, (free.filter (fun c => c.2=row.2)).card) =
      ∑ c ∈ free, (active.filter (fun row => c.2=row.2)).card from hdouble]
  calc
    _ ≤ ∑ _c ∈ free, Fintype.card Observer :=
      Finset.sum_le_sum (fun c _ => column_incidence_le active c)
    _ = _ := by simp [Nat.mul_comm]

theorem exists_sparse_equation (active : Finset (Observer × Color)) (free : Finset (Cell × Color))
    (hfree : 0 < free.card) (hbound : free.card ≤ 2*active.card) :
    ∃ row ∈ active, (rowSupport free row).card ≤ 2*Fintype.card Observer := by
  have hactive : active.Nonempty := Finset.card_pos.mp (by omega)
  by_contra h
  have hstrict : (∑ _row ∈ active, 2*Fintype.card Observer) <
      ∑ row ∈ active, (rowSupport free row).card :=
    Finset.sum_lt_sum_of_nonempty hactive (fun row hrow =>
      lt_of_not_ge (fun hsmall => h ⟨row,hrow,hsmall⟩))
  have hcount := total_incidence_le active free
  have hsize := Nat.mul_le_mul_left (Fintype.card Observer) hbound
  have heq : (∑ _row ∈ active, 2*Fintype.card Observer) =
      Fintype.card Observer*(2*active.card) := by simp [Nat.mul_comm,Nat.mul_left_comm]
  rw [heq] at hstrict
  exact (not_lt_of_ge (hcount.trans hsize)) hstrict

end EnvyFreeResearch.Full.Chores.Multicolor
