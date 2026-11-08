import EnvyFreeResearch.Full.UpperRoundingSlots

/-!
# Whole-cell rounding of a fractional assignment

Sorted packing, fractional capacities, Hall's theorem, and repeated deletion
produce disjoint whole-cell ownership with an owner deficit at most one cell.
-/

noncomputable section

open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperRounding

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

def target (a x : Agent → Cell → ℝ) (j : Agent) : ℝ := ∑ e, a j e * x j e

def load (a : Agent → Cell → ℝ) (owned : Agent → Finset Cell) (j : Agent) : ℝ :=
  ∑ e ∈ owned j, a j e


/-- The complementary sorted-slot estimate: discard the first match and
charge each later match to the preceding full fractional slot. -/
theorem sorted_matched_load_upper {n : ℕ} (a : Cell → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta) (ha : ∀ e, 0 ≤ a e) (habound : ∀ e, a e ≤ eta)
    (b : Fin (n + 1) → Cell → ℝ) (hb : ∀ r e, 0 ≤ b r e)
    (hfull : ∀ r : Fin n, ∑ e, b r.castSucc e = 1)
    (hadj : ∀ (r : Fin n) e e', 0 < b r.castSucc e → 0 < b r.succ e' → a e' ≤ a e)
    (m : Fin n → Cell) (hm : ∀ r, 0 < b r.castSucc (m r)) :
    (∑ r, a (m r)) ≤ eta + ∑ r, ∑ e, a e * b r e := by
  let v (r : Fin (n + 1)) : ℝ := ∑ e, a e * b r e
  have hv (r : Fin (n + 1)) : 0 ≤ v r :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (ha e) (hb r e))
  cases n with
  | zero =>
    simp only [Fin.sum_univ_zero]
    exact add_nonneg heta (Finset.sum_nonneg (fun r _ => hv r))
  | succ n =>
    have hprev (r : Fin n) : a (m r.succ) ≤ v r.castSucc.castSucc := by
      calc
        a (m r.succ) = ∑ e, a (m r.succ) * b r.castSucc.castSucc e := by
          rw [← Finset.mul_sum, hfull r.castSucc, mul_one]
        _ ≤ ∑ e, a e * b r.castSucc.castSucc e := by
          apply Finset.sum_le_sum
          intro e _
          by_cases he : 0 < b r.castSucc.castSucc e
          · apply mul_le_mul_of_nonneg_right _ (hb _ e)
            exact hadj r.castSucc e (m r.succ) he (by simpa using hm r.succ)
          · have hz : b r.castSucc.castSucc e = 0 := le_antisymm (le_of_not_gt he) (hb _ e)
            simp [hz]
        _ = v r.castSucc.castSucc := rfl
    have hsum := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin n))) => hprev r)
    have hfirst := habound (m 0)
    change (∑ r, a (m r)) ≤ eta + ∑ r, v r
    rw [Fin.sum_univ_succ (fun r => a (m r))]
    rw [Fin.sum_univ_castSucc (fun r => v r), Fin.sum_univ_castSucc]
    have hlast := hv (Fin.last (n + 1))
    have hnextlast := hv (Fin.last n).castSucc
    linarith

namespace SlotPacking

variable {a x : Agent → Cell → ℝ} (P : SlotPacking a x)

def fullMass (s : (j : Agent) × Fin (P.count j)) (e : Cell) : ℝ :=
  P.mass s.1 s.2.castSucc e

theorem fullMass_capacity (hcell : ∀ e, ∑ j, x j e ≤ 1) (e : Cell) :
    ∑ s, P.fullMass s e ≤ 1 := by
  rw [Fintype.sum_sigma]
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hcell e)
  change ∑ r : Fin (P.count j), P.mass j r.castSucc e ≤ x j e
  have h := P.column j e
  rw [Fin.sum_univ_castSucc] at h
  have hlast := P.nonneg j (Fin.last (P.count j)) e
  linarith

theorem matching (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    ∃ m : ((j : Agent) × Fin (P.count j)) → Cell,
      Function.Injective m ∧ ∀ s, 0 < P.fullMass s (m s) :=
  matching_of_fractional P.fullMass (fun s e => P.nonneg s.1 s.2.castSucc e)
    (fun s => P.full s.1 s.2) (P.fullMass_capacity hcell)

def value (j : Agent) (r : Fin (P.count j + 1)) : ℝ := ∑ e, a j e * P.mass j r e

omit [Fintype Agent] in
theorem value_nonneg (ha : ∀ j e, 0 ≤ a j e) (j : Agent) (r : Fin (P.count j + 1)) :
    0 ≤ P.value j r := Finset.sum_nonneg (fun e _ => mul_nonneg (ha j e) (P.nonneg j r e))

omit [Fintype Agent] in
theorem value_le (eta : ℝ) (heta : 0 ≤ eta) (ha : ∀ j e, a j e ≤ eta)
    (j : Agent) (r : Fin (P.count j + 1)) : P.value j r ≤ eta := by
  calc
    P.value j r ≤ ∑ e, eta * P.mass j r e :=
      Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (ha j e) (P.nonneg j r e))
    _ = eta * ∑ e, P.mass j r e := (Finset.mul_sum ..).symm
    _ ≤ eta * 1 := mul_le_mul_of_nonneg_left (P.row_le j r) heta
    _ = eta := mul_one _

omit [Fintype Agent] in
theorem sum_value (j : Agent) : ∑ r, P.value j r = target a x j := by
  unfold value target
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum, P.column]

omit [Fintype Agent] in
/-- A matched value dominates the next slot's fractional value, including
its final partial slot. -/
theorem next_value_le_match (ha : ∀ j e, 0 ≤ a j e)
    (m : ((j : Agent) × Fin (P.count j)) → Cell)
    (hm : ∀ s, 0 < P.fullMass s (m s)) (j : Agent) (r : Fin (P.count j)) :
    P.value j r.succ ≤ a j (m ⟨j, r⟩) := by
  calc
    P.value j r.succ ≤ ∑ e, a j (m ⟨j, r⟩) * P.mass j r.succ e := by
      apply Finset.sum_le_sum
      intro e _
      by_cases he : 0 < P.mass j r.succ e
      · exact mul_le_mul_of_nonneg_right
          (P.adjacent j r _ e (hm ⟨j, r⟩) he) (P.nonneg j r.succ e)
      · have hz : P.mass j r.succ e = 0 := le_antisymm (le_of_not_gt he) (P.nonneg j r.succ e)
        simp [hz]
    _ = a j (m ⟨j, r⟩) * ∑ e, P.mass j r.succ e := (Finset.mul_sum ..).symm
    _ ≤ a j (m ⟨j, r⟩) * 1 := mul_le_mul_of_nonneg_left (P.row_le j r.succ) (ha j _)
    _ = a j (m ⟨j, r⟩) := mul_one _

omit [Fintype Agent] in
/-- The first fractional slot costs at most one cell, and each remaining
fractional slot is charged to its preceding matched value. -/
theorem matched_load_lower (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (m : ((j : Agent) × Fin (P.count j)) → Cell)
    (hm : ∀ s, 0 < P.fullMass s (m s)) (j : Agent) :
    target a x j - eta ≤ ∑ r : Fin (P.count j), a j (m ⟨j, r⟩) := by
  have hfirst := P.value_le eta heta habound j 0
  have hrest := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin (P.count j)))) =>
    P.next_value_le_match ha m hm j r)
  have htarget := P.sum_value j
  rw [Fin.sum_univ_succ] at htarget
  linarith


omit [Fintype Agent] in
/-- Both untrimmed load bounds of the manuscript follow from the packing. -/
theorem matched_load_bounds (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (m : ((j : Agent) × Fin (P.count j)) → Cell)
    (hm : ∀ s, 0 < P.fullMass s (m s)) (j : Agent) :
    target a x j - eta ≤ ∑ r : Fin (P.count j), a j (m ⟨j, r⟩) ∧
      (∑ r : Fin (P.count j), a j (m ⟨j, r⟩)) ≤ target a x j + eta := by
  refine ⟨P.matched_load_lower eta heta ha habound m hm j, ?_⟩
  have h := sorted_matched_load_upper (a j) eta heta (ha j) (habound j)
    (P.mass j) (P.nonneg j) (P.full j) (P.adjacent j) (fun r => m ⟨j, r⟩)
    (fun r => hm ⟨j, r⟩)
  change (∑ r, a j (m ⟨j, r⟩)) ≤ eta + ∑ r, P.value j r at h
  rw [P.sum_value] at h
  linarith

end SlotPacking

/-- Every finite feasible fractional assignment admits disjoint whole-cell
ownership below each fractional target and within one maximum cell value.
The proof constructs sorted slots and invokes Hall using their actual masses. -/
theorem exists_rounding (a x : Agent → Cell → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (hx : ∀ j e, 0 ≤ x j e) (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    ∃ owned : Agent → Finset Cell,
      (∀ i j, i ≠ j → Disjoint (owned i) (owned j)) ∧
      ∀ j, target a x j - eta ≤ load a owned j ∧ load a owned j ≤ target a x j := by
  classical
  let P := makePacking a x hx
  obtain ⟨m, hinj, hm⟩ := P.matching hcell
  let initial (j : Agent) : Finset Cell := Finset.univ.image (fun r => m ⟨j, r⟩)
  have hinitial (j : Agent) : ∑ e ∈ initial j, a j e = ∑ r : Fin (P.count j), a j (m ⟨j, r⟩) := by
    apply Finset.sum_image
    intro r _ s _ hrs
    have h := hinj hrs
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hdisjoint (i j : Agent) (hij : i ≠ j) : Disjoint (initial i) (initial j) := by
    apply Finset.disjoint_left.mpr
    intro e hi hj
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hi
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hj
    exact hij (congrArg Sigma.fst (hinj (hr.trans hs.symm)))
  have htrim (j : Agent) : ∃ T ⊆ initial j,
      target a x j - eta ≤ ∑ e ∈ T, a j e ∧ ∑ e ∈ T, a j e ≤ target a x j := by
    apply trim_load (a j) eta (target a x j) (habound j)
      (Finset.sum_nonneg (fun e _ => mul_nonneg (ha j e) (hx j e))) (initial j)
    rw [hinitial]
    exact P.matched_load_lower eta heta ha habound m hm j
  choose owned hsubset hbounds using htrim
  refine ⟨owned, ?_, hbounds⟩
  intro i j hij
  exact (hdisjoint i j hij).mono (hsubset i) (hsubset j)

/-- The deficit formulation needed by reserve Repair. -/
theorem exists_rounding_deficit (a x : Agent → Cell → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (hx : ∀ j e, 0 ≤ x j e) (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    ∃ owned : Agent → Finset Cell,
      (∀ i j, i ≠ j → Disjoint (owned i) (owned j)) ∧
      ∀ j, 0 ≤ target a x j - load a owned j ∧
        target a x j - load a owned j ≤ min (target a x j) eta := by
  obtain ⟨owned, hdisjoint, hbounds⟩ := exists_rounding a x eta heta ha habound hx hcell
  refine ⟨owned, hdisjoint, fun j => ⟨sub_nonneg.mpr (hbounds j).2, le_min ?_ ?_⟩⟩
  · have hnonneg : 0 ≤ load a owned j := Finset.sum_nonneg (fun e _ => ha j e)
    linarith
  · linarith [(hbounds j).1]

end EnvyFreeResearch.Full.UpperRounding
