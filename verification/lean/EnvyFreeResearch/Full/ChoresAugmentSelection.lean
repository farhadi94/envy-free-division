import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! Finite cached selection for whole-piece augmentation. Repeated argmax
reserves the most costly currently available original pieces, with a fixed
list tie rule. The selected pieces and exact remaining list are retained. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open scoped Classical

variable {Piece : Type*} [DecidableEq Piece]

def takeTop (score : Piece → ℝ) : ℕ → List Piece → List Piece × List Piece
  | 0, available => ([],available)
  | k+1, available =>
      match available.argmax score with
      | none => ([],available)
      | some p =>
          let tail := takeTop score k (available.erase p)
          (p::tail.1,tail.2)

theorem take_top_correct (score : Piece → ℝ) (k : ℕ) (available : List Piece)
    (hlen : k ≤ available.length) :
    ∃ selected remaining, takeTop score k available=(selected,remaining) ∧
      selected.length=k ∧ (selected++remaining).Perm available ∧
      selected.Pairwise (fun a b => score b ≤ score a) ∧
      ∀ a ∈ selected, ∀ b ∈ remaining, score b ≤ score a := by
  induction k generalizing available with
  | zero => exact ⟨[],available,rfl,rfl,List.Perm.refl _,List.Pairwise.nil,by simp⟩
  | succ k ih =>
    cases hmax : available.argmax score with
    | none =>
      have hz := List.argmax_eq_none.mp hmax
      simp only [hz,List.length_nil] at hlen
      omega
    | some p =>
      have hp : p ∈ available := List.argmax_mem (f := score) (by simp [hmax])
      have hple : ∀ q ∈ available, score q ≤ score p :=
        fun q hq => List.le_of_mem_argmax (f := score) hq (by simp [hmax])
      have hlen' : k ≤ (available.erase p).length := by
        have h := List.length_erase_add_one hp
        omega
      obtain ⟨selected,remaining,heq,hcount,hperm,horder,hgap⟩ := ih (available.erase p) hlen'
      have hinside : ∀ q ∈ selected++remaining, q ∈ available :=
        fun q hq => List.mem_of_mem_erase (hperm.mem_iff.mp hq)
      refine ⟨p::selected,remaining,?_,by simp [hcount],?_,?_,?_⟩
      · simp only [takeTop,hmax,heq]
      · exact (hperm.cons p).trans (List.perm_cons_erase hp).symm
      · apply List.pairwise_cons.mpr
        exact ⟨fun q hq => hple q (hinside q (List.mem_append_left _ hq)),horder⟩
      · intro a ha b hb
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hple b (hinside b (List.mem_append_right _ hb))
        · exact hgap a ha b hb

theorem take_top_partition (score : Piece → ℝ) (k : ℕ) (available : List Piece)
    (hlen : k ≤ available.length) (hnodup : available.Nodup) :
    ∃ selected remaining, takeTop score k available=(selected,remaining) ∧
      selected.length=k ∧ remaining.length=available.length-k ∧
      (selected++remaining).Perm available ∧ (selected++remaining).Nodup ∧
      selected.Pairwise (fun a b => score b ≤ score a) ∧
      ∀ a ∈ selected, ∀ b ∈ remaining, score b ≤ score a := by
  obtain ⟨selected,remaining,heq,hcount,hperm,horder,hgap⟩ := take_top_correct score k available hlen
  refine ⟨selected,remaining,heq,hcount,?_,hperm,hperm.nodup_iff.mpr hnodup,horder,hgap⟩
  have hl := hperm.length_eq
  simp only [List.length_append,hcount] at hl
  omega

end EnvyFreeResearch.Full.Chores.Augment
