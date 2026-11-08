import Mathlib

/-! Finite simple paths and the physical-label permutation obtained by
closing such a path into a cycle. No oracle operations occur here. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Transfer
open scoped Classical

structure SimplePath {k : ℕ} (E : Fin k → Fin k → Prop) (a b : Fin k) where
  length : ℕ
  vertex : Fin (length+1) → Fin k
  injective : Function.Injective vertex
  source : vertex 0=a
  target : vertex (Fin.last length)=b
  edge : ∀ i : Fin length, E (vertex i.castSucc) (vertex i.succ)

namespace SimplePath
variable {k : ℕ} {E : Fin k → Fin k → Prop} {a b : Fin k} (path : SimplePath E a b)

def cycle : Equiv.Perm (Fin k) := (List.ofFn path.vertex).formPerm

theorem cycle_vertex (i : Fin (path.length+1)) :
    path.cycle (path.vertex i)=path.vertex ⟨(i.val+1)%(path.length+1),Nat.mod_lt _ (by omega)⟩ := by
  have hnodup : (List.ofFn path.vertex).Nodup := List.nodup_ofFn.mpr path.injective
  have h := List.formPerm_apply_getElem (List.ofFn path.vertex) hnodup i.val
    (by simpa using i.isLt)
  simpa only [List.length_ofFn, List.getElem_ofFn, cycle] using h

theorem cycle_last : path.cycle b=a := by
  calc
    path.cycle b = path.cycle (path.vertex (Fin.last path.length)) := congrArg path.cycle path.target.symm
    _ = a := by
      rw [path.cycle_vertex]
      simpa using path.source

theorem cycle_step (i : Fin path.length) :
    path.cycle (path.vertex i.castSucc)=path.vertex i.succ := by
  rw [path.cycle_vertex]
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by simpa using i.succ.isLt)

theorem cycle_fixed (i : Fin k) (hi : i ∉ Set.range path.vertex) : path.cycle i=i := by
  apply List.formPerm_apply_of_notMem
  simpa only [List.mem_ofFn, Set.mem_range] using hi

/-- Any finite directed path whose endpoints lie on opposite sides has a
crossing edge. This argument does not require edge symmetry. -/
theorem crossing (P : Fin k → Prop) (ha : P a) (hb : ¬P b) :
    ∃ i : Fin path.length, P (path.vertex i.castSucc) ∧ ¬P (path.vertex i.succ) := by
  by_contra! hn
  have all : ∀ t (ht : t < path.length+1), P (path.vertex ⟨t,ht⟩) := by
    intro t
    induction t with
    | zero => intro ht; change P (path.vertex 0); rw [path.source]; exact ha
    | succ t ih =>
      intro ht
      have hi : t < path.length := by omega
      exact hn ⟨t,hi⟩ (ih (by omega))
  have hx := all path.length (by omega)
  exact hb (path.target ▸ hx)

theorem cycle_small (d : Fin k → Fin k → ℝ) (rho : Fin k → ℝ) (tau : ℝ)
    (hdiag : ∀ i, d i i=0) (hnonneg : ∀ i, 0 ≤ tau*rho i)
    (hclose : d b a ≤ tau*rho b)
    (hstep : ∀ i : Fin path.length,
      d (path.vertex i.castSucc) (path.vertex i.succ) ≤ tau*rho (path.vertex i.castSucc)) :
    ∀ i, d i (path.cycle i) ≤ tau*rho i := by
  intro i
  by_cases hm : i ∈ Set.range path.vertex
  · obtain ⟨v,rfl⟩ := hm
    by_cases hv : v.val=path.length
    · have heq : v=Fin.last path.length := Fin.ext hv
      rw [heq, path.target, path.cycle_last]
      exact hclose
    · have hlt : v.val < path.length := by omega
      have heq : v=(⟨v.val,hlt⟩ : Fin path.length).castSucc := Fin.ext rfl
      rw [heq,path.cycle_step]
      exact hstep ⟨v.val,hlt⟩
  · rw [path.cycle_fixed i hm,hdiag]
    exact hnonneg i

end SimplePath
end EnvyFreeResearch.Full.UpperGlobal.Transfer
