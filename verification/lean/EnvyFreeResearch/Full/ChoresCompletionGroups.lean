import EnvyFreeResearch.Full.ChoresCompletionAllocation
import EnvyFreeResearch.Full.ChoresCompletionBudget

/-! Combining the two completed groups uses physical containment and the
large whole pieces protected by near-equal splitting. No connectedness or
strictly-positive-density assumption is needed. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram

variable {n : ℕ} {B D : Type*}

def sumAllocation (left : Allocation n B) (right : Allocation n D) : Allocation n (Sum B D) :=
  ⟨Sum.elim left.pieces right.pieces⟩

theorem sum_allocation_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agentB : B → Fin n) (agentD : D → Fin n) (R X : Set ℝ) (hRX : Disjoint R X)
    (left : Allocation n B) (right : Allocation n D)
    (hl : left.Sound cost agentB R) (hr : right.Sound cost agentD X)
    (hprotectB : ∀ i j, (cost (agentB i)).real R ≤ (cost (agentB i)).real (material (right.pieces j)))
    (hprotectD : ∀ j i, (cost (agentD j)).real X ≤ (cost (agentD j)).real (material (left.pieces i))) :
    (sumAllocation left right).Sound cost (Sum.elim agentB agentD) (R ∪ X) := by
  constructor
  · intro i
    cases i with
    | inl i => exact hl.cache i
    | inr j => exact hr.cache j
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hl.disjoint (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hRX.mono (hl.subset cost _ R left i) (hr.subset cost _ X right j)
    | inr i =>
      cases j with
      | inl j => exact hRX.symm.mono (hr.subset cost _ X right i) (hl.subset cost _ R left j)
      | inr j => exact hr.disjoint (fun h => hij (congrArg Sum.inr h))
  · ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      cases i with
      | inl i => exact Or.inl ((hl.subset cost _ R left i) hi)
      | inr i => exact Or.inr ((hr.subset cost _ X right i) hi)
    · rintro (hx | hx)
      · rw [← hl.cover] at hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨Sum.inl i,hi⟩
      · rw [← hr.cover] at hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨Sum.inr i,hi⟩
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hl.envy_free i j
      | inr j => exact (measureReal_mono (hl.subset cost _ R left i)).trans (hprotectB i j)
    | inr i =>
      cases j with
      | inl j => exact (measureReal_mono (hr.subset cost _ X right i)).trans (hprotectD i j)
      | inr j => exact hr.envy_free i j

theorem separation_protects (small large denominator scale : ℝ)
    (hs : 0 ≤ small) (hd : 0 < denominator) (hscale : denominator ≤ scale)
    (hseparation : scale*small ≤ large) : small ≤ large/denominator := by
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem completion_scale (b c : ℕ) : 2*countPieces c ≤ (2 : ℕ)^(b+c+2) := by
  have h : 2*countPieces c=(2 : ℕ)^(c+2) := by simp [countPieces,pow_succ]; ring
  rw [h]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem split_protection (b c : ℕ) (small large : ℝ) (hs : 0 ≤ small)
    (hsep : (2 : ℝ)^(b+c+2)*small ≤ large) :
    small ≤ large/(2*(countPieces c : ℝ)) := by
  apply separation_protects small large _ ((2 : ℝ)^(b+c+2)) hs
  · exact mul_pos (by norm_num) (Nat.cast_pos.mpr (countPieces_pos c))
  · exact_mod_cast completion_scale b c
  · exact hsep

end EnvyFreeResearch.Full.Chores.Completion
