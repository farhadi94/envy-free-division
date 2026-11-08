import EnvyFreeResearch.Full.UpperShrinkCarvePhysical

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperEndpointCache

theorem disjoint_pieceDomain (S : Set ℝ) (pieces : List (Piece k))
    (h : ∀ p ∈ pieces, Disjoint S (domain p.cells)) : Disjoint S (pieceDomain pieces) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨p,hp,hy⟩ := mem_pieceDomain.mp hy
  exact Set.disjoint_left.mp (h p hp) hx hy

variable {n k : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (policy : Policy n)
  (hp : Admissible (Chores.measureProfile μ) policy) (active : Fin k → Fin n)

include hp in
theorem refinePieces_physical (pieces : List (Piece k)) (history : History n)
    (ht : Truthful μ history)
    (hw : ∀ p ∈ pieces, WellFormed μ (⟨p.cells,history⟩ : State n))
    (hd : pieces.Pairwise (fun p q => Disjoint (domain p.cells) (domain q.cells))) :
    (refinePiecesExecute policy active pieces history).Physical μ (pieceDomain pieces) := by
  induction pieces generalizing history with
  | nil =>
    change (⟨[],history⟩ : Mesh n k).Physical μ (pieceDomain [])
    exact ⟨ht,by simp,by simp,rfl⟩
  | cons p rest ih =>
    have hhead := hw p (by simp)
    have hrest : ∀ q ∈ rest, WellFormed μ (⟨q.cells,history⟩ : State n) :=
      fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have hdparts := List.pairwise_cons.mp hd
    have hdis := disjoint_pieceDomain (domain p.cells) rest hdparts.1
    by_cases hs : split p
    · let mid := medianChainExecute policy (List.ofFn active) (⟨p.cells,history⟩ : State n)
      have hmid := medianChain_wellFormed μ policy hp (List.ofFn active) _ hhead
      obtain ⟨tr,_,htr⟩ := medianChain_executes policy (List.ofFn active) (⟨p.cells,history⟩ : State n)
      have hpre : history ⊆ mid.history := by rw [htr]; exact List.subset_append_left _ _
      have htail := ih mid.history hmid.2.2.1
        (fun q hq => wellFormed_history_extend μ _ history mid.history (hrest q hq) hmid.2.2.1 hpre)
        hdparts.2
      let tail := refinePiecesExecute policy active rest mid.history
      obtain ⟨tr',_,htr'⟩ := refinePieces_executes policy active rest mid.history
      have hpost : mid.history ⊆ tail.history := by rw [htr']; exact List.subset_append_left _ _
      have hmidDomain : domain mid.cells = domain p.cells := medianChain_domain policy _ _
      have hcross : ∀ a ∈ children p mid, ∀ b ∈ tail.pieces,
          Disjoint (domain a.cells) (domain b.cells) := by
        intro a ha b hb
        have hsa := piece_subset_domain (children p mid) a ha
        rw [children_domain,hmidDomain] at hsa
        have hsb := piece_subset_domain tail.pieces b hb
        rw [htail.cover] at hsb
        exact hdis.mono hsa hsb
      simp only [refinePiecesExecute, if_pos hs]
      refine ⟨htail.truthful,?_,?_,?_⟩
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact children_wellFormed μ p mid hmid tail.history htail.truthful hpost q hq
        · exact htail.pieces q hq
      · exact List.pairwise_append.mpr ⟨children_disjoint p mid hmid.2.1,htail.disjoint,hcross⟩
      · change pieceDomain (children p mid ++ tail.pieces) = _
        rw [pieceDomain_append,children_domain,hmidDomain,htail.cover,pieceDomain_cons]
    · have htail := ih history ht hrest hdparts.2
      obtain ⟨tr,_,htr⟩ := refinePieces_executes policy active rest history
      have hpost : history ⊆ (refinePiecesExecute policy active rest history).history := by
        rw [htr]
        exact List.subset_append_left _ _
      simp only [refinePiecesExecute, if_neg hs]
      refine ⟨htail.truthful,?_,?_,?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact wellFormed_history_extend μ _ _ _ hhead htail.truthful hpost
        · exact htail.pieces q hq
      · apply List.pairwise_cons.mpr
        refine ⟨?_,htail.disjoint⟩
        intro q hq
        have hsub := piece_subset_domain _ q hq
        rw [htail.cover] at hsub
        exact hdis.mono_right hsub
      · rw [pieceDomain_cons,htail.cover,pieceDomain_cons]

end EnvyFreeResearch.Full.UpperShrinkCarve
