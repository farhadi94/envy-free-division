import EnvyFreeResearch.Full.ChoresIntervalAllocation

/-!
# The actual finite owner chain used by SubCore

An unused parent has no predecessor under the current injective assignment.
Following current assigned parents through their old owners must therefore
exit the selected set, without repeating an owner. The finite path is chosen
from an explicitly bounded list of iterates, using only cached assignments.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set Function

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def ownerStep (selected : Finset Agent) (next : selected → Agent) (i : Agent) : Agent :=
  if h : i ∈ selected then next ⟨i, h⟩ else i

omit [Fintype Agent] in
lemma ownerStep_of_mem (selected : Finset Agent) (next : selected → Agent)
    (i : Agent) (hi : i ∈ selected) : ownerStep selected next i = next ⟨i, hi⟩ := by
  simp only [ownerStep, dite_eq_left hi]

omit [Fintype Agent] in
lemma ownerStep_injective_on (selected : Finset Agent) (next : selected → Agent)
    (hinj : Injective next) {i j : Agent} (hi : i ∈ selected) (hj : j ∈ selected)
    (heq : ownerStep selected next i = ownerStep selected next j) : i = j := by
  rw [ownerStep_of_mem selected next i hi, ownerStep_of_mem selected next j hj] at heq
  exact congrArg Subtype.val (hinj heq)

/-- Finite injectivity forces the path from an unused parent to leave the
selected owners. This proves termination rather than assuming a free endpoint. -/
theorem owner_chain_exits (selected : Finset Agent) (next : selected → Agent)
    (hinj : Injective next) (start : Agent) (hstart : ∀ i, next i ≠ start) :
    ∃ k : ℕ, (ownerStep selected next)^[k] start ∉ selected := by
  classical
  by_contra h
  have hall : ∀ k : ℕ, (ownerStep selected next)^[k] start ∈ selected := by
    simpa only [not_exists, not_not] using h
  let reachable : Set Agent := {i | ∃ k : ℕ, (ownerStep selected next)^[k] start = i}
  have hreach : ∀ i : reachable, i.val ∈ selected := by
    rintro ⟨i, k, rfl⟩
    exact hall k
  let step : reachable → reachable := fun i => ⟨ownerStep selected next i.val, by
    obtain ⟨k, hk⟩ := i.property
    exact ⟨k + 1, by rw [iterate_succ_apply', hk]⟩⟩
  have hstep : Injective step := by
    intro i j hij
    apply Subtype.ext
    exact ownerStep_injective_on selected next hinj (hreach i) (hreach j) (congrArg Subtype.val hij)
  obtain ⟨i, hi⟩ := (Finite.surjective_of_injective hstep) (⟨start, 0, rfl⟩ : reachable)
  have heq : ownerStep selected next i.val = start := congrArg Subtype.val hi
  rw [ownerStep_of_mem selected next i.val (hreach i)] at heq
  exact hstart ⟨i.val, hreach i⟩ heq

omit [Fintype Agent] in
lemma owner_chain_no_repeat (selected : Finset Agent) (next : selected → Agent)
    (hinj : Injective next) (start : Agent) (hstart : ∀ i, next i ≠ start)
    (h : ℕ) (hbefore : ∀ r < h, (ownerStep selected next)^[r] start ∈ selected) :
    ∀ i j : ℕ, i < j → j ≤ h →
      (ownerStep selected next)^[i] start ≠ (ownerStep selected next)^[j] start := by
  intro i
  induction i with
  | zero =>
    intro j hij hjh heq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hj : (ownerStep selected next)^[j] start ∈ selected := hbefore j (by omega)
    rw [iterate_zero_apply, iterate_succ_apply', ownerStep_of_mem selected next _ hj] at heq
    exact hstart ⟨_, hj⟩ heq.symm
  | succ i ih =>
    intro j hij hjh heq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [iterate_succ_apply', iterate_succ_apply'] at heq
    have hi : (ownerStep selected next)^[i] start ∈ selected := hbefore i (by omega)
    have hj : (ownerStep selected next)^[j] start ∈ selected := hbefore j (by omega)
    exact ih j (by omega) (by omega) (ownerStep_injective_on selected next hinj hi hj heq)

/-- A bounded, nonrepeating owner chain can be searched without any oracle
call. Its last owner is outside the selected set; every earlier owner is in it. -/
theorem owner_chain_bounded (selected : Finset Agent) (next : selected → Agent)
    (hinj : Injective next) (start : Agent) (hmem : start ∈ selected)
    (hstart : ∀ i, next i ≠ start) :
    ∃ h : ℕ, 0 < h ∧ h ≤ selected.card ∧
      (∀ r < h, (ownerStep selected next)^[r] start ∈ selected) ∧
      (ownerStep selected next)^[h] start ∉ selected ∧
      Injective (fun r : Fin (h + 1) => (ownerStep selected next)^[r.val] start) := by
  classical
  have hex := owner_chain_exits selected next hinj start hstart
  let h := Nat.find hex
  have hout : (ownerStep selected next)^[h] start ∉ selected := Nat.find_spec hex
  have hbefore : ∀ r < h, (ownerStep selected next)^[r] start ∈ selected := by
    intro r hr
    exact not_not.mp (Nat.find_min hex hr)
  have hpos : 0 < h := by
    by_contra hn
    have hz : h = 0 := by omega
    rw [hz, iterate_zero_apply] at hout
    exact hout hmem
  have hdistinct : Injective (fun r : Fin (h + 1) => (ownerStep selected next)^[r.val] start) := by
    intro i j heq
    apply Fin.ext
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact owner_chain_no_repeat selected next hinj start hstart h hbefore i.val j.val hij (by omega) heq
    · exact owner_chain_no_repeat selected next hinj start hstart h hbefore j.val i.val hji (by omega) heq.symm
  have hcard : h ≤ selected.card := by
    let f : Fin h → selected := fun r => ⟨(ownerStep selected next)^[r.val] start, hbefore r.val r.isLt⟩
    have hf : Injective f := by
      intro i j hij
      have hv := congrArg Subtype.val hij
      have heq : i.castSucc = j.castSucc := hdistinct hv
      have hv' : i.val = j.val := congrArg (fun r : Fin (h + 1) => r.val) heq
      exact Fin.ext hv'
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf
  exact ⟨h, hpos, hcard, hbefore, hout, hdistinct⟩

end EnvyFreeResearch.Full.Chores.SubCore
