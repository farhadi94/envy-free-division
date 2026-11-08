import EnvyFreeResearch.Full.UpperShrinkCarveExecution

/-! Fraction feasibility and the actual number of queried parents. The
bound is on the concrete floating selector's list of split cells. -/
noncomputable section
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve

def Piece.Valid (p : Piece k) : Prop :=
  (∀ c, 0 ≤ p.fraction c ∧ p.fraction c ≤ 1) ∧ ∑ c, p.fraction c = 1

def Mesh.FractionsValid (mesh : Mesh n k) : Prop := ∀ p ∈ mesh.pieces, p.Valid

theorem splitCount_ofFn (p : Fin r → Piece k) :
    splitCount (List.ofFn p) = ∑ i, if split (p i) then 1 else 0 := by
  induction r with
  | zero => simp [splitCount]
  | succ r ih =>
    rw [List.ofFn_succ,Fin.sum_univ_succ]
    change (List.filter (fun p => decide (split p)) (p 0::List.ofFn (fun i => p i.succ))).length = _
    by_cases hs : split (p 0)
    · simp only [List.filter_cons,hs,decide_true,ite_true,List.length_cons]
      change splitCount (List.ofFn (fun i => p i.succ))+1 = _
      rw [ih]
      omega
    · simp only [List.filter_cons,hs,decide_false,ite_false,zero_add]
      exact ih _

theorem floated_valid_count (active : Fin k → Fin n) (normal : Fin k → ℝ) (mesh : Mesh n k)
    (hvalid : mesh.FractionsValid) :
    (floated active normal mesh).FractionsValid ∧ splitCount (floated active normal mesh).pieces ≤ k^2 := by
  let x : UpperFloating.PaymentCoord (Fin k) (Fin mesh.pieces.length) → ℝ :=
    fun c => (mesh.pieces.get c.1).fraction c.2
  have hs := UpperFloating.select_spec (weights active normal mesh) x
    (fun c => (hvalid _ (List.get_mem _ c.1)).1 c.2)
    (fun e => (hvalid _ (List.get_mem _ e)).2)
  constructor
  · intro p hp
    obtain ⟨e,he⟩ := List.mem_ofFn.mp hp
    subst p
    exact ⟨fun c => hs.1 (e,c),hs.2.1 e⟩
  · change splitCount (List.ofFn (fun e : Fin mesh.pieces.length =>
        (⟨(mesh.pieces.get e).cells,fun c => UpperFloating.select (weights active normal mesh) x (e,c)⟩ : Piece k))) ≤ k^2
    rw [splitCount_ofFn]
    have hsame : (∑ i : Fin mesh.pieces.length, if split
        (⟨(mesh.pieces.get i).cells,fun c => UpperFloating.select (weights active normal mesh) x (i,c)⟩ : Piece k)
        then 1 else 0) = (UpperFloating.splitCells (UpperFloating.select (weights active normal mesh) x)).card := by
      rw [UpperFloating.splitCells_eq_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : ∃ c, 0 < UpperFloating.select (weights active normal mesh) x (i,c) ∧
          UpperFloating.select (weights active normal mesh) x (i,c) < 1
      · simp [split,h]
      · simp [split,h]
    rw [hsame]
    simpa only [Fintype.card_fin] using hs.2.2.2.2

theorem children_valid (piece : Piece k) (hp : piece.Valid) (state : UpperCorrectionExecution.State n) :
    ∀ child ∈ children piece state, child.Valid := by
  intro child hc
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hc
  exact hp

theorem refinement_valid (policy : UpperCircularStage.Policy n) (active : Fin k → Fin n)
    (pieces : List (Piece k)) (history : UpperCircularStage.History n)
    (hp : ∀ p ∈ pieces, p.Valid) : (refinePiecesExecute policy active pieces history).FractionsValid := by
  induction pieces generalizing history with
  | nil => intro p h; cases h
  | cons p rest ih =>
    have hpv := hp p (by simp)
    have hrest : ∀ q ∈ rest,q.Valid := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    by_cases hs : split p
    · intro q hq
      simp only [refinePiecesExecute,hs,ite_true,List.mem_append] at hq
      rcases hq with hq | hq
      · exact children_valid p hpv _ q hq
      · exact ih _ hrest q hq
    · intro q hq
      simp only [refinePiecesExecute,hs,ite_false,List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hpv
      · exact ih _ hrest q hq

end EnvyFreeResearch.Full.UpperShrinkCarve
