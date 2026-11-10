import EnvyFreeResearch.Full.UpperRounding

/-! The sorted-slot rounding can preserve the support of every real color.
This strengthening is necessary when discrepancy equations have been dropped:
a zero coordinate must never acquire a cell in a later rounding step. -/
noncomputable section
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.RefinedUpperSupportedRounding
open UpperRounding
variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]

theorem exists_supported_rounding (a x : Agent → Cell → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta) (ha : ∀ j e, 0 ≤ a j e) (habound : ∀ j e, a j e ≤ eta)
    (hx : ∀ j e, 0 ≤ x j e) (hcell : ∀ e, ∑ j, x j e ≤ 1) :
    ∃ owned : Agent → Finset Cell,
      (∀ i j, i ≠ j → Disjoint (owned i) (owned j)) ∧
      (∀ j, target a x j - eta ≤ load a owned j ∧ load a owned j ≤ target a x j) ∧
      (∀ j e, e ∈ owned j → 0 < x j e) := by
  let P := makePacking a x hx
  obtain ⟨m, hinj, hm⟩ := P.matching hcell
  let initial (j : Agent) : Finset Cell := Finset.univ.image (fun r => m ⟨j, r⟩)
  have hinitial (j : Agent) : ∑ e ∈ initial j, a j e = ∑ r : Fin (P.count j), a j (m ⟨j,r⟩) := by
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
  refine ⟨owned, fun i j hij => (hdisjoint i j hij).mono (hsubset i) (hsubset j), hbounds, ?_⟩
  intro j e he
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp (hsubset j he)
  have hp : 0 < P.mass j r.castSucc e := by
    simpa only [SlotPacking.fullMass, hr] using hm ⟨j,r⟩
  have hle : P.mass j r.castSucc e ≤ ∑ q, P.mass j q e :=
    Finset.single_le_sum (fun q _ => P.nonneg j q e) (Finset.mem_univ _)
  rw [P.column] at hle
  exact hp.trans_le hle

end EnvyFreeResearch.Full.RefinedUpperSupportedRounding
