import EnvyFreeResearch.Full.UpperAssignmentIsolation
import Mathlib.Data.Fintype.List
import Mathlib.GroupTheory.Perm.List

/-!
# Finite simple-path potentials

All simple paths are explicitly finite and their maximum is selected by
`List.argmax`. Nonpositive permutation cycles imply that removing a closed
part of a path cannot decrease its weight. This proves the payment
inequalities for the actual maximizing paths.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperPotentials

open UpperRepresentatives

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def walkWeight (w : Agent → Agent → ℝ) : Agent → List Agent → ℝ
  | _, [] => 0
  | i, j :: rest => w i j + walkWeight w j rest

omit [Fintype Agent] [DecidableEq Agent] in
theorem walkWeight_append (w : Agent → Agent → ℝ) (start last : Agent)
    (left right : List Agent) :
    walkWeight w start (left ++ last :: right) =
      walkWeight w start (left ++ [last]) + walkWeight w last right := by
  induction left generalizing start with
  | nil => simp [walkWeight]
  | cons j rest ih => simp only [List.cons_append, walkWeight, ih]; ring

omit [Fintype Agent] [DecidableEq Agent] in
theorem walkWeight_zip (w : Agent → Agent → ℝ) (start last : Agent) (rest : List Agent) :
    walkWeight w start (rest ++ [last]) =
      (List.zipWith w (start :: rest) (rest ++ [last])).sum := by
  induction rest generalizing start with
  | nil => simp [walkWeight]
  | cons j rest ih => simp [walkWeight, ih]

/-- The closing walk of a simple path is exactly the weighted cycle of its
concrete `List.formPerm` permutation. -/
theorem closed_walk_eq_formPerm (w : Agent → Agent → ℝ) (start : Agent) (rest : List Agent)
    (hnodup : (start :: rest).Nodup) :
    walkWeight w start (rest ++ [start]) =
      ∑ i ∈ (start :: rest).toFinset, w i ((start :: rest).formPerm i) := by
  rw [walkWeight_zip, List.sum_toFinset _ hnodup]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_zipWith, List.getElem_map]
    congr 1
    by_cases hbefore : i < rest.length
    · rw [List.getElem_append_left hbefore]
      have hstep := List.formPerm_apply_lt_getElem (start :: rest) hnodup i
        (by simpa using Nat.succ_lt_succ hbefore)
      have htail : (start :: rest)[i + 1]'(by simpa using Nat.succ_lt_succ hbefore) = rest[i] := rfl
      rw [htail] at hstep
      exact hstep.symm
    · have hi' : i < rest.length + 1 := by simpa using hj
      have heq : i = rest.length := by omega
      subst i
      simp

def NoPositivePermutation (w : Agent → Agent → ℝ) : Prop :=
  ∀ transfer : Equiv.Perm Agent, (∑ i ∈ transfer.support, w i (transfer i)) ≤ 0

theorem closed_walk_nonpositive (w : Agent → Agent → ℝ) (hdiag : ∀ i, w i i = 0)
    (hcycles : NoPositivePermutation w) (start : Agent) (rest : List Agent)
    (hnodup : (start :: rest).Nodup) : walkWeight w start (rest ++ [start]) ≤ 0 := by
  rw [closed_walk_eq_formPerm w start rest hnodup]
  have hsum : (∑ i ∈ (start :: rest).formPerm.support, w i ((start :: rest).formPerm i)) =
      ∑ i ∈ (start :: rest).toFinset, w i ((start :: rest).formPerm i) := by
    apply Finset.sum_subset (List.support_formPerm_le (start :: rest))
    intro i _ hi
    rw [Equiv.Perm.notMem_support.mp hi, hdiag]
  rw [← hsum]
  exact hcycles _

abbrev PathFrom (i : Agent) := {p : {l : List Agent // l.Nodup} // i ∉ p.val}

def emptyPath (i : Agent) : PathFrom i := ⟨⟨[], List.nodup_nil⟩, List.not_mem_nil⟩

def pathList (i : Agent) : List (PathFrom i) := Finset.univ.toList

theorem pathList_nonempty (i : Agent) : pathList i ≠ [] := by
  have h : emptyPath i ∈ pathList i := by simp [pathList]
  intro heq
  simp [heq] at h

def bestPath (w : Agent → Agent → ℝ) (i : Agent) : PathFrom i :=
  ((pathList i).argmax (fun p => walkWeight w i p.val.val)).getD (emptyPath i)

def potential (w : Agent → Agent → ℝ) (i : Agent) : ℝ :=
  walkWeight w i (bestPath w i).val.val

theorem path_le_potential (w : Agent → Agent → ℝ) (i : Agent) (p : PathFrom i) :
    walkWeight w i p.val.val ≤ potential w i := by
  obtain ⟨best, hbest⟩ := argmax_exists (fun p : PathFrom i => walkWeight w i p.val.val)
    (pathList i) (pathList_nonempty i)
  have h := List.le_of_mem_argmax (f := fun p : PathFrom i => walkWeight w i p.val.val)
    (show p ∈ pathList i by simp [pathList]) (show best ∈ (pathList i).argmax _ by simp [hbest])
  simpa [potential, bestPath, hbest] using h

theorem potential_nonnegative (w : Agent → Agent → ℝ) (i : Agent) : 0 ≤ potential w i :=
  path_le_potential w i (emptyPath i)

/-- Prepending an edge either gives another simple path or creates a
nonpositive initial cycle, whose deletion improves the candidate path. -/
theorem prepend_le_potential (w : Agent → Agent → ℝ) (hdiag : ∀ i, w i i = 0)
    (hcycles : NoPositivePermutation w) (i j : Agent) (p : PathFrom j) :
    w i j + walkWeight w j p.val.val ≤ potential w i := by
  have hnodup : (j :: p.val.val).Nodup := List.nodup_cons.mpr ⟨p.property, p.val.property⟩
  by_cases hmem : i ∈ j :: p.val.val
  · obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp hmem
    have hsplitNodup : (before ++ i :: after).Nodup := hsplit ▸ hnodup
    have hparts := List.nodup_append.mp hsplitNodup
    have hiBefore : i ∉ before := by
      intro hi
      exact hparts.2.2 i hi i (by simp) rfl
    have hcycle := closed_walk_nonpositive w hdiag hcycles i before
      (List.nodup_cons.mpr ⟨hiBefore, hparts.1⟩)
    let shorter : PathFrom i := ⟨⟨after, (List.nodup_cons.mp hparts.2.1).2⟩,
      (List.nodup_cons.mp hparts.2.1).1⟩
    have hshort := path_le_potential w i shorter
    have hwalk := walkWeight_append w i i before after
    rw [← hsplit] at hwalk
    simp only [walkWeight] at hwalk
    change walkWeight w i after ≤ potential w i at hshort
    linarith
  · let longer : PathFrom i := ⟨⟨j :: p.val.val, hnodup⟩, hmem⟩
    exact path_le_potential w i longer

/-- Actual maximizing simple-path potentials satisfy every desired
difference inequality on the no-positive-cycle branch. -/
theorem potential_inequality (w : Agent → Agent → ℝ) (hdiag : ∀ i, w i i = 0)
    (hcycles : NoPositivePermutation w) (i j : Agent) :
    w i j + potential w j ≤ potential w i :=
  prepend_le_potential w hdiag hcycles i j (bestPath w j)

omit [Fintype Agent] in
theorem walkWeight_bound (w : Agent → Agent → ℝ) (regret : Agent → ℝ) (delta : ℝ)
    (hregret : ∀ i, 0 ≤ regret i) (hedge : ∀ i j, w i j ≤ regret i + delta)
    (i : Agent) (rest : List Agent) (hnodup : (i :: rest).Nodup) :
    walkWeight w i rest ≤ (∑ j ∈ (i :: rest).toFinset, regret j) + rest.length * delta := by
  induction rest generalizing i with
  | nil => simpa [walkWeight] using hregret i
  | cons j rest ih =>
    obtain ⟨hi, htail⟩ := List.nodup_cons.mp hnodup
    have ht := ih j htail
    have he := hedge i j
    rw [walkWeight, List.toFinset_cons, Finset.sum_insert (by simpa using hi)]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- The path uses each charged row at most once and at most `k-1` margins. -/
theorem potential_bound (w : Agent → Agent → ℝ) (regret : Agent → ℝ) (delta : ℝ)
    (hregret : ∀ i, 0 ≤ regret i) (hdelta : 0 ≤ delta)
    (hedge : ∀ i j, w i j ≤ regret i + delta) (i : Agent) :
    potential w i ≤ (∑ j, regret j) + (Fintype.card Agent - 1 : ℕ) * delta := by
  let p := bestPath w i
  have hn : (i :: p.val.val).Nodup := List.nodup_cons.mpr ⟨p.property, p.val.property⟩
  have h := walkWeight_bound w regret delta hregret hedge i p.val.val hn
  have hsum : (∑ j ∈ (i :: p.val.val).toFinset, regret j) ≤ ∑ j, regret j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hregret j)
  have hlen : p.val.val.length ≤ Fintype.card Agent - 1 := by
    have := hn.length_le_card
    simp only [List.length_cons] at this
    omega
  have hlenReal : (p.val.val.length : ℝ) ≤ (Fintype.card Agent - 1 : ℕ) := by exact_mod_cast hlen
  have hm := mul_le_mul_of_nonneg_right hlenReal hdelta
  change walkWeight w i p.val.val ≤ _
  linarith

end EnvyFreeResearch.Full.UpperPotentials
