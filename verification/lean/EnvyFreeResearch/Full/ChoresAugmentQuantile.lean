import EnvyFreeResearch.Full.ChoresAugmentSelection
import Mathlib.Data.Finset.Card

/-! The augmentation threshold and its designated smallest public bundles
are computed from the current cached cost row. Ties remain designated;
the order statistic is bounded by any cap satisfied by sufficiently many
untouched original public pieces. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open scoped Classical

variable {Piece : Type*} [DecidableEq Piece]

def quantile (cost : Piece → ℝ) (a : ℕ) (available : List Piece) : List Piece × ℝ :=
  let picked := (takeTop (fun p => -cost p) (a+1) available).1
  match picked.getLast? with
  | none => ([],0)
  | some p => (picked.dropLast,cost p)

theorem quantile_correct (cost : Piece → ℝ) (a : ℕ) (available : List Piece)
    (hlen : a+1 ≤ available.length) (hnodup : available.Nodup) :
    ∃ designated threshold, quantile cost a available=(designated,threshold) ∧
      designated.length=a ∧ designated.Nodup ∧ (∀ p ∈ designated, p ∈ available) ∧
      (∀ p ∈ designated, cost p ≤ threshold) ∧
      (∀ p ∈ available, p ∉ designated → threshold ≤ cost p) ∧
      ∃ p ∈ available, cost p=threshold := by
  obtain ⟨selected,remaining,heq,hcount,_,hperm,hnd,horder,hgap⟩ :=
    take_top_partition (fun p => -cost p) (a+1) available hlen hnodup
  rcases List.eq_nil_or_concat' selected with hempty | ⟨designated,last,hsel⟩
  · simp only [hempty,List.length_nil] at hcount
    omega
  · subst selected
    have hDcount : designated.length=a := by simpa only [List.length_append,List.length_singleton,Nat.add_right_cancel_iff] using hcount
    have hDnodup : designated.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
    have hDinside : ∀ p ∈ designated, p ∈ available :=
      fun p hp => hperm.mem_iff.mp (List.mem_append_left _ (List.mem_append_left _ hp))
    have hlast : last ∈ designated++[last] := List.mem_append_right _ (by simp)
    have hlastIn : last ∈ available := hperm.mem_iff.mp (List.mem_append_left _ hlast)
    refine ⟨designated,cost last,?_,hDcount,hDnodup,hDinside,?_,?_,last,hlastIn,rfl⟩
    · simp only [quantile,heq,List.getLast?_append_cons,List.getLast?_singleton,List.dropLast_concat]
    · intro p hp
      have h := (List.pairwise_append.mp horder).2.2 p hp last (by simp)
      linarith
    · intro p hp hnot
      have hm := hperm.mem_iff.mpr hp
      rcases List.mem_append.mp hm with hselected | hremaining
      · rcases List.mem_append.mp hselected with hD | hp
        · exact (hnot hD).elim
        · have heq : p=last := List.mem_singleton.mp hp
          exact heq.symm ▸ le_rfl
      · have h := hgap last hlast p hremaining
        linarith

theorem threshold_le_of_many (cost : Piece → ℝ) (available designated : List Piece)
    (hDnodup : designated.Nodup) (threshold cap : ℝ)
    (hthreshold : ∀ p ∈ available, p ∉ designated → threshold ≤ cost p)
    (low : Finset Piece) (hcount : designated.length < low.card)
    (hinside : ∀ p ∈ low, p ∈ available) (hlow : ∀ p ∈ low, cost p ≤ cap) : threshold ≤ cap := by
  by_contra h
  have hstrict : cap < threshold := lt_of_not_ge h
  have hsub : low ⊆ designated.toFinset := by
    intro p hp
    apply List.mem_toFinset.mpr
    by_contra hn
    exact (not_lt_of_ge (hlow p hp)) (hstrict.trans_le (hthreshold p (hinside p hp) hn))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hDnodup] at hcard
  omega

theorem supplement_feasible (current threshold reserve : ℝ) (hcurrent : 0 ≤ current)
    (hdesignated : current ≤ threshold) (hreserve : threshold ≤ reserve) :
    0 ≤ threshold-current ∧ threshold-current ≤ reserve := by
  constructor <;> linarith

end EnvyFreeResearch.Full.Chores.Augment
