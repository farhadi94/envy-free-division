import EnvyFreeResearch.Full.ChoresAugmentSelection

/-! Forward reservation uses cached costs only. Every reserved piece
costs at least every surviving public original for its reserving agent.
The exact list permutation records all material, including zero-cost pieces. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open scoped Classical

variable {Agent Piece : Type*} [DecidableEq Agent] [DecidableEq Piece]

structure Reservations (Agent Piece : Type*) where
  reserved : Agent → List Piece
  available : List Piece

def reserveAll (cost : Agent → Piece → ℝ) (quota : Agent → ℕ) :
    List Agent → List Piece → Reservations Agent Piece
  | [], available => ⟨fun _ => [],available⟩
  | i::recipients, available =>
      let picked := takeTop (cost i) (quota i) available
      let tail := reserveAll cost quota recipients picked.2
      ⟨Function.update tail.reserved i picked.1,tail.available⟩

theorem reserve_all_correct (cost : Agent → Piece → ℝ) (quota : Agent → ℕ)
    (recipients : List Agent) (available : List Piece)
    (hrec : recipients.Nodup) (hpieces : available.Nodup)
    (hbudget : (recipients.map quota).sum ≤ available.length) :
    let out := reserveAll cost quota recipients available
    (∀ i ∈ recipients, (out.reserved i).length=quota i) ∧
    (∀ i ∉ recipients, out.reserved i=[]) ∧
    (recipients.flatMap out.reserved ++ out.available).Perm available ∧
    out.available.length + (recipients.map quota).sum=available.length ∧
    ∀ i ∈ recipients, ∀ p ∈ out.reserved i, ∀ q ∈ out.available,
      cost i q ≤ cost i p := by
  induction recipients generalizing available with
  | nil => simp [reserveAll]
  | cons i recipients ih =>
    obtain ⟨hin,hrec'⟩ := List.nodup_cons.mp hrec
    have hhead : quota i ≤ available.length := by simpa using (le_trans (Nat.le_add_right _ _) hbudget)
    obtain ⟨picked,remaining,hpick,hcount,hremain,hperm,hnd,horder,hgap⟩ :=
      take_top_partition (cost i) (quota i) available hhead hpieces
    have hbudget' : (recipients.map quota).sum ≤ remaining.length := by
      simp only [List.map_cons,List.sum_cons] at hbudget
      omega
    have hnd' : remaining.Nodup := (List.nodup_append.mp hnd).2.1
    let tail := reserveAll cost quota recipients remaining
    obtain ⟨hlen,houtside,hcover,hlength,hdom⟩ := ih remaining hrec' hnd' hbudget'
    simp only [reserveAll,hpick]
    change (∀ j ∈ i::recipients, (Function.update tail.reserved i picked j).length=quota j) ∧
      (∀ j ∉ i::recipients, Function.update tail.reserved i picked j=[]) ∧
      ((i::recipients).flatMap (Function.update tail.reserved i picked) ++ tail.available).Perm available ∧
      tail.available.length + ((i::recipients).map quota).sum=available.length ∧
      ∀ j ∈ i::recipients, ∀ p ∈ Function.update tail.reserved i picked j,
        ∀ q ∈ tail.available, cost j q ≤ cost j p
    change tail.available.length + (recipients.map quota).sum = remaining.length at hlength
    have hagree (j : Agent) (hj : j ∈ recipients) :
        Function.update tail.reserved i picked j=tail.reserved j := by
      have hne : j ≠ i := by intro h; subst j; exact hin hj
      exact Function.update_of_ne hne _ _
    have hflat : recipients.flatMap (Function.update tail.reserved i picked)=
        recipients.flatMap tail.reserved := List.flatMap_congr hagree
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · simpa using hcount
      · rw [hagree j hj]
        exact hlen j hj
    · intro j hj
      have hne : j ≠ i := by intro h; subst j; exact hj (by simp)
      rw [Function.update_of_ne hne]
      exact houtside j (fun h => hj (List.mem_cons_of_mem _ h))
    · simp only [List.flatMap_cons,Function.update_self,hflat,List.append_assoc]
      exact (hcover.append_left picked).trans hperm
    · simp only [List.map_cons,List.sum_cons]
      have htotal := hperm.length_eq
      simp only [List.length_append,hcount] at htotal
      omega
    · intro j hj p hp q hq
      rcases List.mem_cons.mp hj with rfl | hj
      · have hp' : p ∈ picked := by simpa using hp
        have hq' : q ∈ remaining := hcover.mem_iff.mp (List.mem_append_right _ hq)
        exact hgap p hp' q hq'
      · rw [hagree j hj] at hp
        exact hdom j hj p hp q hq

end EnvyFreeResearch.Full.Chores.Augment
