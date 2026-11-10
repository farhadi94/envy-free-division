import EnvyFreeResearch.Full.RefinedUpperPeelingPartialControl

/-! Explicit endpoint charges of a concrete peeling transcript. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open scoped Classical BigOperators
variable {Cell Index : Type*} [DecidableEq Index]

/-- The charged samples are precisely endpoints of chosen cells. -/
def charges (endpoints : Cell → Finset Index) : List (Cell × Cell) → Finset Index
  | [] => ∅
  | p::ps => endpoints p.1 ∪ endpoints p.2 ∪ charges endpoints ps

lemma mem_charges (endpoints : Cell → Finset Index) (pairs : List (Cell × Cell)) (t : Index) :
    t ∈ charges endpoints pairs ↔ ∃ p ∈ pairs, t ∈ endpoints p.1 ∨ t ∈ endpoints p.2 := by
  induction pairs with
  | nil => simp [charges]
  | cons p ps ih => simp only [charges,Finset.mem_union,ih,List.mem_cons]; aesop

lemma charges_card_le (endpoints : Cell → Finset Index) (pairs : List (Cell × Cell))
    (hcard : ∀ c, (endpoints c).card ≤ 2) :
    (charges endpoints pairs).card ≤ 4*pairs.length := by
  induction pairs with
  | nil => simp [charges]
  | cons p ps ih =>
    have h1 := Finset.card_union_le (endpoints p.1) (endpoints p.2)
    have h2 := Finset.card_union_le (endpoints p.1 ∪ endpoints p.2) (charges endpoints ps)
    have ha := hcard p.1
    have hb := hcard p.2
    simp only [charges,List.length_cons]
    omega

lemma uncharged_keeps_pairs (endpoints : Cell → Finset Index) (pairs : List (Cell × Cell))
    (t : Index) (ht : t ∉ charges endpoints pairs) :
    ∀ p ∈ pairs, decide (t ∉ endpoints p.1) = true ∧ decide (t ∉ endpoints p.2) = true := by
  intro p hp
  constructor
  · simp only [decide_eq_true_eq]
    intro h
    exact ht ((mem_charges endpoints pairs t).mpr ⟨p,hp,Or.inl h⟩)
  · simp only [decide_eq_true_eq]
    intro h
    exact ht ((mem_charges endpoints pairs t).mpr ⟨p,hp,Or.inr h⟩)

lemma charges_append (endpoints : Cell → Finset Index) (ps qs : List (Cell × Cell)) :
    charges endpoints (ps++qs) = charges endpoints ps ∪ charges endpoints qs := by
  ext t
  simp only [mem_charges,Finset.mem_union,List.mem_append]
  aesop

/-- Endpoint charging has exactly the claimed linear budget: at most four
sample labels per selected slot and four per final row-pair witness. -/
theorem total_charges_card (endpoints : Cell → Finset Index)
    (selected finalWitnesses : List (Cell × Cell)) (hcard : ∀ c, (endpoints c).card ≤ 2) :
    (charges endpoints (selected++finalWitnesses)).card ≤
      4*selected.length+4*finalWitnesses.length := by
  have h := charges_card_le endpoints (selected++finalWitnesses) hcard
  simpa [List.length_append,Nat.mul_add] using h

end EnvyFreeResearch.Full.RefinedUpperPeeling
