import EnvyFreeResearch.Full.ChoresFrontierProtection

/-! The atomic scan branch derives its participant set, proper large mask,
nonnegative affine whole-parent values, omitted-observer protection and
all small-observer bounds from the actual maximum-large selection. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open scoped Classical

variable {n : ℕ}

def atomicParticipants (E : Finset (Fin n)) (rank : Fin n → ℕ) (a : Fin n) : Finset (Fin n) :=
  E.filter (fun i => a.val+1 ≤ rank i)

theorem atomic_scan_spec (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hr : ∀ i, 0 < r i) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hatoms : AtomSeparated w r H) (hgaps : GapSeparated w rank r H)
    (owner : Fin n) (howner : rank owner=n) (C : Finset (Fin n))
    (s : Stop n) (hstop : s.Valid rank (eligible w rank r H) C)
    (a : Fin n) (hscan : largestBad w r H (rank s.agent)=some a) :
    let A := atomicParticipants (eligible w rank r H) rank a
    let B := largeMask w r H a
    owner ∈ A ∧ A ⊆ C ∧ s.agent ∉ A ∧ B.Nonempty ∧ s.agent ∉ B ∧
      (∀ i ∈ A, tailCost w i (rank i) ≤ tailCost w i a.val) ∧
      (∀ i, i ∉ A → tailCost w i a.val ≤ tailCost w i (rank i)) ∧
      (∀ i ∈ B, H*r i ≤ w i a) ∧
      ∀ i, i ∉ B → tailCost w i a.val ≤ (n : ℝ)*r i/H := by
  have hHpos : 0 < H := by linarith
  obtain ⟨hstart,hbad,hright⟩ := largestBad_some w r H (rank s.agent) a hscan
  have hownerE := owner_eligible w rank r H owner howner (hr owner).le hHpos
  have hstopE := stop_eligible rank (eligible w rank r H) C s hstop
  have hright' : ∀ j : Fin n, a.val < j.val → Small w r H j := fun j hj => hright j hj
  refine ⟨?_,?_,?_,largeMask_nonempty w r H hatoms a hbad,?_,?_,?_,?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨hownerE,by rw [howner]; exact a.isLt⟩
  · intro i hi
    obtain ⟨hi,hrank⟩ := Finset.mem_filter.mp hi
    exact before_stop_internal rank (eligible w rank r H) C s hstop i hi (by omega)
  · intro h
    have h := (Finset.mem_filter.mp h).2
    omega
  · intro hlarge
    have hbig := ((mem_largeMask w r H a s.agent).mp hlarge).trans
      (atom_le_tail w hw s.agent a (rank s.agent) hstart)
    exact small_not_large (r s.agent) H (tailCost w s.agent (rank s.agent))
      (hr s.agent) hH ((mem_eligible w rank r H s.agent).mp hstopE) hbig
  · intro i hi
    apply tail_antitone w hw i
    exact (Nat.le_succ a.val).trans (Finset.mem_filter.mp hi).2
  · intro i hi
    apply tail_antitone w hw i
    by_cases he : i ∈ eligible w rank r H
    · have hnot : ¬ a.val+1 ≤ rank i := fun h => hi (Finset.mem_filter.mpr ⟨he,h⟩)
      omega
    · exact omitted_rank_le w rank r H hr hHpos hscale hgaps a.val hright' i he
  · intro i hi
    exact (mem_largeMask w r H a i).mp hi
  · intro i hi
    apply tail_small w i a.val (r i) H (hr i).le hHpos
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact hright j hlt i
    · have hja : j=a := Fin.ext heq.symm
      rw [hja]
      exact outside_mask_small w r H hatoms a i hi

theorem atomic_before_frontier (w : Fin n → Fin n → ℝ) (r : Fin n → ℝ) (H : ℝ)
    (t frontier : ℕ) (hpassed : ∀ a : Fin n, frontier ≤ a.val → Small w r H a)
    (a : Fin n) (hscan : largestBad w r H t=some a) : a.val < frontier := by
  have hbad := (largestBad_some w r H t a hscan).2.1
  exact lt_of_not_ge (fun h => hbad (hpassed a h))

end EnvyFreeResearch.Full.Chores.Frontier
