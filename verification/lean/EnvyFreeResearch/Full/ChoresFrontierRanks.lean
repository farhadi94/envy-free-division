import EnvyFreeResearch.Full.ChoresFrontierTail
import EnvyFreeResearch.Full.ChoresOriginalAtomTable

/-! Atom boundary ranks are computed from the actual original mark table.
The owner receives the full rank n because its equalizer is the complete
original share. Other marks keep their deterministic sorted-table rank;
all coincident and zero-cost atoms remain present. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open OriginalAtoms Equalizers
open scoped Classical BigOperators

variable {n : ℕ}

def originalMark (table : Table n) (p i : Fin n) : Mark n :=
  ⟨(table (p,i)).point,(table (p,i)).values⟩

theorem original_mark_mem (table : Table n) (p i : Fin n) :
    originalMark table p i ∈ sortedMarks (marksFromTable table p) := by
  apply (sorted_marks_perm _).mem_iff.mpr
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

def rawRank (table : Table n) (p i : Fin n) : ℕ :=
  (sortedMarks (marksFromTable table p)).idxOf (originalMark table p i)+1

def rankOf (table : Table n) (p i : Fin n) : ℕ := if i=p then n else rawRank table p i

theorem raw_rank_positive (table : Table n) (p i : Fin n) : 0 < rawRank table p i := Nat.zero_lt_succ _

theorem raw_rank_le (table : Table n) (p i : Fin n) : rawRank table p i ≤ n := by
  have hi := List.idxOf_lt_length_iff.mpr (original_mark_mem table p i)
  have hlen : (sortedMarks (marksFromTable table p)).length=n :=
    ((sorted_marks_perm _).length_eq).trans List.length_ofFn
  unfold rawRank
  omega

theorem rank_owner (table : Table n) (p : Fin n) : rankOf table p p=n := by simp [rankOf]

theorem rank_le (table : Table n) (p i : Fin n) : rankOf table p i ≤ n := by
  by_cases h : i=p
  · simp [rankOf,h]
  · simpa [rankOf,h] using raw_rank_le table p i

theorem indexed_tail_sum {α : Type*} (xs : List α) (value : α → ℝ) (t : ℕ) :
    (∑ a : Fin xs.length, if t ≤ a.val then value (xs.get a) else 0)=((xs.drop t).map value).sum := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    cases t with
    | zero =>
      simpa only [List.length_cons,Fin.sum_univ_succ,List.get_cons_zero,List.get_cons_succ',
        Nat.zero_le,ite_true,List.drop_zero,List.map_cons,List.sum_cons] using
          congrArg (fun v => value x+v) (ih 0)
    | succ t =>
      have hz : ¬ t+1 ≤ 0 := by omega
      simpa only [List.length_cons,Fin.sum_univ_succ,List.get_cons_zero,List.get_cons_succ',
        Fin.val_zero,Fin.val_succ,hz,ite_false,Nat.add_le_add_iff_right,
        zero_add,List.drop_succ_cons] using ih t

theorem fromMarks_take_sum (previous : Mark n) (marks : List (Mark n)) (j : ℕ)
    (hj : j < marks.length) (i : Fin n) :
    (((fromMarks previous marks).take (j+1)).map (fun a => a.values i)).sum=
      (marks.get ⟨j,hj⟩).values i-previous.values i := by
  induction marks generalizing previous j with
  | nil => simp at hj
  | cons current rest ih =>
    cases j with
    | zero => simp [fromMarks]
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      have h := ih current j hj'
      simp only [fromMarks,List.take_succ_cons,List.map_cons,List.sum_cons]
      rw [h]
      simp only [List.get_cons_succ]
      ring

theorem prefix_sum_rawRank (table : Table n) (p observer i : Fin n) :
    (((atomsFromTable table p).take (rawRank table p observer)).map (fun a => a.values i)).sum=
      (table (p,observer)).values i := by
  let marks := sortedMarks (marksFromTable table p)
  have hm : originalMark table p observer ∈ marks := original_mark_mem table p observer
  have hi : marks.idxOf (originalMark table p observer) < marks.length := List.idxOf_lt_length_iff.mpr hm
  have h := fromMarks_take_sum (emptyMark n) marks (marks.idxOf (originalMark table p observer)) hi i
  have hget : marks.get ⟨marks.idxOf (originalMark table p observer),hi⟩=originalMark table p observer :=
    List.getElem_idxOf hi
  rw [hget] at h
  simpa only [atomsFromTable,rawRank,marks,originalMark,emptyMark,sub_zero] using h

end EnvyFreeResearch.Full.Chores.Frontier
