import EnvyFreeResearch.Full.MixedBatch

/-! Finite amplification of the concrete capture batches. The hard profile
is selected using its tape law before an execution tape is drawn. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedAmplification
open Set MeasureTheory IntervalOracle OracleProtocol MixedFrontier MixedExecution MixedBatch
open MixedPhysicalFailure IntervalAllocation
open scoped Classical

variable {Agent Ω : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {α : ℝ}

def captureRate (Agent : Type*) [Fintype Agent] (fuel : ℕ) : ℝ :=
  1 / (2 * (2 * Fintype.card Agent : ℝ) ^ fuel)

omit [MeasurableSpace Agent] [MeasurableSingletonClass Agent] in
theorem captureRate_pos (fuel : ℕ) : 0 < captureRate Agent fuel := by
  have hn : (0 : ℝ) < Fintype.card Agent := by exact_mod_cast Fintype.card_pos
  unfold captureRate
  positivity

omit [MeasurableSpace Agent] [MeasurableSingletonClass Agent] in
theorem captureRate_le_one (fuel : ℕ) : captureRate Agent fuel ≤ 1 := by
  have hn : (1 : ℝ) ≤ Fintype.card Agent := by exact_mod_cast Fintype.card_pos
  have hp : (1 : ℝ) ≤ (2 * Fintype.card Agent : ℝ) ^ fuel :=
    one_le_pow₀ (by linarith)
  unfold captureRate
  apply (div_le_one (by positivity : (0 : ℝ) < 2 * (2 * Fintype.card Agent : ℝ) ^ fuel)).mpr
  linarith

/-- Old captured tapes remain protected, and a batch captures a fixed
fraction of the remaining tape measure. -/
theorem extend_capture
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base) (S : State Agent α)
    (H : Set Ω) (fuel : ℕ) (hα : 0 < α) (hH : MeasurableSet H)
    (hp : ∀ ω ∈ H, Protected next S ω fuel) :
    ∃ T : State Agent α, ∃ J : Set Ω, Extends S T ∧ MeasurableSet J ∧ H ⊆ J ∧
      μ.real Jᶜ ≤ (1 - captureRate Agent fuel) * μ.real Hᶜ ∧
      ∀ ω ∈ J, Protected next T ω fuel := by
  obtain ⟨T, G, hst, hG, hGc, hgain, hpg⟩ :=
    exists_batch (μ := μ) next base views S Hᶜ fuel hα hH.compl
  have hd : Disjoint H G := by
    apply Set.disjoint_left.mpr
    intro ω hω hg
    exact hGc hg hω
  refine ⟨T, H ∪ G, hst, hH.union hG, subset_union_left, ?_, ?_⟩
  · rw [measureReal_compl (hH.union hG), measureReal_union hd hG]
    have hc := measureReal_compl (μ := μ) hH
    have hg : μ.real Hᶜ * captureRate Agent fuel ≤ μ.real G := by
      simpa only [captureRate, one_div, div_eq_mul_inv, one_mul] using hgain
    nlinarith
  · intro ω hω
    rcases hω with hω | hω
    · exact protected_of_extends next hst ω fuel (hp ω hω)
    · exact hpg ω hω

/-- Every finite number of capture rounds produces a single concrete state. -/
theorem capture_rounds
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base) (S : State Agent α)
    (fuel rounds : ℕ) (hα : 0 < α) :
    ∃ T : State Agent α, ∃ H : Set Ω, Extends S T ∧ MeasurableSet H ∧
      μ.real Hᶜ ≤ (1 - captureRate Agent fuel) ^ rounds ∧
      ∀ ω ∈ H, Protected next T ω fuel := by
  induction rounds with
  | zero =>
    refine ⟨S, ∅, Extends.refl S, MeasurableSet.empty, by simp, ?_⟩
    intro ω hω
    exact False.elim hω
  | succ rounds ih =>
    obtain ⟨T, H, hst, hH, hrem, hp⟩ := ih
    obtain ⟨U, J, htu, hJ, hHJ, hstep, hpu⟩ :=
      extend_capture (μ := μ) next base views T H fuel hα hH hp
    refine ⟨U, J, hst.trans htu, hJ, ?_, hpu⟩
    calc
      μ.real Jᶜ ≤ (1 - captureRate Agent fuel) * μ.real Hᶜ := hstep
      _ ≤ (1 - captureRate Agent fuel) * (1 - captureRate Agent fuel) ^ rounds :=
        mul_le_mul_of_nonneg_left hrem (sub_nonneg.mpr (captureRate_le_one (Agent := Agent) fuel))
      _ = (1 - captureRate Agent fuel) ^ (rounds + 1) := by rw [pow_succ]; ring

/-- A fixed physical input protects all but δ of the tape space. -/
theorem exists_almost_all_protected
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base) (S : State Agent α)
    (fuel : ℕ) (δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ T : State Agent α, ∃ H : Set Ω, Extends S T ∧ MeasurableSet H ∧
      μ.real Hᶜ < δ ∧ ∀ ω ∈ H, Protected next T ω fuel := by
  have hr : 1 - captureRate Agent fuel < 1 := by linarith [captureRate_pos (Agent := Agent) fuel]
  obtain ⟨rounds, hrounds⟩ := exists_pow_lt_of_lt_one hδ hr
  obtain ⟨T, H, hst, hH, hrem, hp⟩ := capture_rounds (μ := μ) next base views S fuel rounds hα
  exact ⟨T, H, hst, hH, hrem.trans_lt hrounds, hp⟩

def capSuccess (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (fuel : ℕ) (ε : ℝ) : Set Ω :=
  {ω | ∃ A, (run next (oracle (profile S)) ω fuel []).stop = .returned A ∧ ApproximateEF S A ε}

/-- The finite-horizon hard-input theorem follows from the actual constructed
profiles and physical output obstruction, not from a supplied adversary field. -/
theorem exists_hard_cap
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base) (fuel : ℕ) (ε δ : ℝ)
    (hn : 3 ≤ Fintype.card Agent) (hα : 0 < α) (hε : ε < α) (hδ : 0 < δ) :
    ∃ T : State Agent α, μ.real (capSuccess next T fuel ε) < δ := by
  obtain ⟨T, H, hst, hH, hrem, hp⟩ := exists_almost_all_protected (μ := μ)
    next base views (initial Agent α) fuel δ hα hδ
  have hsub : capSuccess next T fuel ε ⊆ Hᶜ := by
    intro ω hs hω
    obtain ⟨A, hret, hef⟩ := hs
    exact protected_failure next T ω fuel ε hn hα.le hε (hp ω hω) A hret hef
  exact ⟨T, (measureReal_mono hsub (by finiteness)).trans_lt hrem⟩

end EnvyFreeResearch.Full.MixedAmplification
