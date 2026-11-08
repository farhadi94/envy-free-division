import EnvyFreeResearch.Full.UpperShrinkCarvePhysical
import EnvyFreeResearch.Full.UpperShrinkCarveFractions
import EnvyFreeResearch.Full.UpperShrinkCarveRounding

/-! Every actual fractional child passes all observer medians. Integral
parents are not cut, and the floating selector never unfreezes them. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

def SplitBound (μ : Fin n → Measure ℝ) (active : Fin k → Fin n) (bound : Fin k → ℝ)
    (pieces : List (Piece k)) : Prop :=
  ∀ p ∈ pieces, split p → ∀ i, (μ (active i)).real (domain p.cells) ≤ bound i

theorem floated_split_bound (μ : Fin n → Measure ℝ) (active : Fin k → Fin n)
    (normal bound : Fin k → ℝ) (mesh : Mesh n k) (hv : mesh.FractionsValid)
    (hb : SplitBound μ active bound mesh.pieces) :
    SplitBound μ active bound (floated active normal mesh).pieces := by
  let x : UpperFloating.PaymentCoord (Fin k) (Fin mesh.pieces.length) → ℝ :=
    fun c => (mesh.pieces.get c.1).fraction c.2
  have hs := UpperFloating.select_spec (weights active normal mesh) x
    (fun c => (hv _ (List.get_mem _ c.1)).1 c.2)
    (fun e => (hv _ (List.get_mem _ e)).2)
  intro p hp hsplit i
  obtain ⟨e,he⟩ := List.mem_ofFn.mp hp
  subst p
  have hparent : split (mesh.pieces.get e) := by
    rcases hsplit with ⟨c,hc0,hc1⟩
    by_contra hn
    have hnot : ¬ (0 < x (e,c) ∧ x (e,c) < 1) := fun h => hn ⟨c,h⟩
    have hbox := (hv _ (List.get_mem _ e)).1 c
    have hext : x (e,c) = 0 ∨ x (e,c) = 1 := by
      change 0 ≤ x (e,c) ∧ x (e,c) ≤ 1 at hbox
      rcases le_or_gt (x (e,c)) 0 with h | h
      · exact Or.inl (le_antisymm h hbox.1)
      · exact Or.inr (le_antisymm hbox.2 (le_of_not_gt (fun ht => hnot ⟨h,ht⟩)))
    have heq := hs.2.2.2.1 (e,c) hext
    change 0 < UpperFloating.select (weights active normal mesh) x (e,c) at hc0
    change UpperFloating.select (weights active normal mesh) x (e,c) < 1 at hc1
    rw [heq] at hc0 hc1
    rcases hext with h | h <;> linarith
  exact hb _ (List.get_mem _ e) hparent i

theorem refinement_split_halving (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (active : Fin k → Fin n) (bound : Fin k → ℝ)
    (pieces : List (Piece k)) (history : History n)
    (hw : ∀ p ∈ pieces, WellFormed μ (⟨p.cells,history⟩ : State n))
    (hb : SplitBound μ active bound pieces) :
    SplitBound μ active (fun i => bound i/2) (refinePiecesExecute policy active pieces history).pieces := by
  induction pieces generalizing history with
  | nil => intro p h; cases h
  | cons p rest ih =>
    have hpw := hw p (by simp)
    have hrest : ∀ q ∈ rest, WellFormed μ (⟨q.cells,history⟩ : State n) :=
      fun q hq => hw q (by simp [hq])
    have hbr : SplitBound μ active bound rest := fun q hq => hb q (by simp [hq])
    by_cases hs : split p
    · let out := medianChainExecute policy (List.ofFn active) (⟨p.cells,history⟩ : State n)
      have how : WellFormed μ out := medianChain_wellFormed μ policy hp _ _ hpw
      obtain ⟨trace,_,hh⟩ := medianChain_executes policy (List.ofFn active) (⟨p.cells,history⟩ : State n)
      have he : history ⊆ out.history := by rw [hh]; exact List.subset_append_left _ _
      have hrest' : ∀ q ∈ rest, WellFormed μ (⟨q.cells,out.history⟩ : State n) :=
        fun q hq => wellFormed_history_extend μ _ history out.history (hrest q hq) how.2.2.1 he
      intro q hq hqs i
      simp only [refinePiecesExecute,hs,ite_true,List.mem_append] at hq
      rcases hq with hq | hq
      · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
        have hhalf := medianChain_components_half μ policy hp (List.ofFn active)
          (⟨p.cells,history⟩ : State n) hpw (active i) (List.mem_ofFn.mpr ⟨i,rfl⟩) c hc
        change (μ (active i)).real (domain [c]) ≤ _
        simp only [domain,union_empty]
        exact hhalf.trans (div_le_div_of_nonneg_right (hb p (by simp) hs i) (by norm_num))
      · exact ih out.history hrest' hbr q hq hqs i
    · intro q hq hqs i
      simp only [refinePiecesExecute,hs,ite_false,List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact (hs hqs).elim
      · exact ih history hrest hbr q hq hqs i

end EnvyFreeResearch.Full.UpperShrinkCarve
