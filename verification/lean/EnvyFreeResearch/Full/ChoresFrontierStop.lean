import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! The zero-query stopping mark is computed from cached atom boundary
ranks. It is the first outside eligible mark, or the last eligible mark
when the entire eligible set belongs to the current component. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open scoped Classical

variable {n : ℕ}

inductive Stop (n : ℕ)
  | outside : Fin n → Stop n
  | exhausted : Fin n → Stop n

def Stop.agent : Stop n → Fin n
  | .outside q => q
  | .exhausted q => q

def stop (rank : Fin n → ℕ) (E C : Finset (Fin n)) (owner : Fin n) : Stop n :=
  match (E \ C).toList.argmax rank with
  | some q => .outside q
  | none => .exhausted ((E.toList.argmin rank).getD owner)

def Stop.Valid (rank : Fin n → ℕ) (E C : Finset (Fin n)) : Stop n → Prop
  | .outside q => q ∈ E \ C ∧ ∀ i ∈ E \ C, rank i ≤ rank q
  | .exhausted q => q ∈ E ∧ E ⊆ C ∧ ∀ i ∈ E, rank q ≤ rank i

theorem stop_valid (rank : Fin n → ℕ) (E C : Finset (Fin n)) (owner : Fin n) (howner : owner ∈ E) :
    (stop rank E C owner).Valid rank E C := by
  cases hmax : (E \ C).toList.argmax rank with
  | some q =>
    simp only [stop,hmax,Stop.Valid]
    have hq : q ∈ (E \ C).toList := List.argmax_mem (f := rank) (by simp [hmax])
    refine ⟨Finset.mem_toList.mp hq,?_⟩
    intro i hi
    exact List.le_of_mem_argmax (f := rank) (Finset.mem_toList.mpr hi) (by simp [hmax])
  | none =>
    have hempty : E \ C=∅ := by simpa using List.argmax_eq_none.mp hmax
    have hsub : E ⊆ C := Finset.sdiff_eq_empty_iff_subset.mp hempty
    cases hmin : E.toList.argmin rank with
    | none =>
      have hn : E=∅ := by simpa using List.argmin_eq_none.mp hmin
      simp only [hn,Finset.notMem_empty] at howner
    | some q =>
      simp only [stop,hmax,hmin,Option.getD_some,Stop.Valid]
      have hq : q ∈ E.toList := List.argmin_mem (f := rank) (by simp [hmin])
      refine ⟨Finset.mem_toList.mp hq,hsub,?_⟩
      intro i hi
      exact List.le_of_mem_argmin (f := rank) (Finset.mem_toList.mpr hi) (by simp [hmin])

theorem stop_eligible (rank : Fin n → ℕ) (E C : Finset (Fin n)) (s : Stop n)
    (h : s.Valid rank E C) : s.agent ∈ E := by
  cases s with
  | outside q => exact (Finset.mem_sdiff.mp h.1).1
  | exhausted q => exact h.1

theorem before_stop_internal (rank : Fin n → ℕ) (E C : Finset (Fin n)) (s : Stop n)
    (h : s.Valid rank E C) (i : Fin n) (hi : i ∈ E) (hrank : rank s.agent < rank i) : i ∈ C := by
  cases s with
  | outside q =>
    by_contra hn
    exact not_lt_of_ge (h.2 i (Finset.mem_sdiff.mpr ⟨hi,hn⟩)) hrank
  | exhausted q => exact h.2.1 hi

end EnvyFreeResearch.Full.Chores.Frontier
