import EnvyFreeResearch.Full.ChoresTwoAgent
import EnvyFreeResearch.Full.AdaptiveOracle

/-!
# The complete two-agent chore protocol for all adaptive legal Cut replies

This version allows the reply policy to depend on the entire answered history.
The four-query protocol is the same fixed function used in ChoresTwoAgent.
Its trace, literal material partition, exact envy-freeness and one-Cut count
are derived for every history-dependent legal policy.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores
open Set MeasureTheory OracleProtocol IntervalOracle

/-- Exact adaptive execution, with the actual history passed to every query. -/
theorem twoAgentAdaptive_trace (O : AdaptiveOracle.Policy (Query (Fin 2)) ℝ)
    (total x leftCost rightCost : ℝ)
    (htotal : O [] (.eval 0 0 1) = some total)
    (hcut : O [(.eval 0 0 1, total)] (.cut 0 0 1 (total / 2)) = some x)
    (hleft : O [(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x)] (.eval 1 0 x) = some leftCost)
    (hright : O [(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x), (.eval 1 0 x, leftCost)] (.eval 1 x 1) = some rightCost) :
    AdaptiveOracle.run twoAgentProtocol O () 4 [] =
      ⟨[(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x),
        (.eval 1 0 x, leftCost), (.eval 1 x 1, rightCost)],
        .returned (choiceAllocation x leftCost rightCost)⟩ := by
  simp [twoAgentProtocol, htotal, hcut, hleft, hright]


/-- Fully adaptive end-to-end two-agent correctness and physical query counts. -/
theorem complete_twoAgent_adaptive_protocol (cost : Fin 2 → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (O : AdaptiveOracle.Policy (Query (Fin 2)) ℝ)
    (hO : AdaptiveOracle.IsLegalPolicy (measureProfile cost) O) :
    ∃ x ∈ Icc (0 : ℝ) 1,
      let A := twoAgentAllocation cost 0 x 1
      let execution := AdaptiveOracle.run twoAgentProtocol O () 4 []
      execution.stop = .returned A ∧ execution.answered.length = 4 ∧
        (execution.answered.filter (fun qr => isCutQuery qr.1)).length = 1 ∧
        Disjoint (A 0) (A 1) ∧ A 0 ∪ A 1 = Icc 0 1 ∧
        ∀ i j, (cost i).real (A i) ≤ (cost i).real (A j) := by
  obtain ⟨total, htotal⟩ := (hO []).complete (.eval 0 0 1) (by norm_num [Legal])
  have htotalval : total = (cost 0).real (Icc 0 1) := by
    have h := ((hO []).sound _ _ htotal).2
    simpa [ValidReply, measureProfile, prefixCost_self, prefixCost, measureReal_def] using h
  have hnonneg : (0 : ℝ) ≤ (cost 0).real (Icc 0 1) := measureReal_nonneg
  have hlegalCut : Legal (measureProfile cost) (.cut 0 0 1 (total / 2)) := by
    simp only [Legal, measureProfile, ExtremalRoots.LegalTarget]
    rw [prefixCost_self]
    change 0 ≤ (0 : ℝ) ∧ 0 ≤ (1 : ℝ) ∧ 1 ≤ (1 : ℝ) ∧
      min 0 ((cost 0).real (Icc 0 1) - 0) ≤ total / 2 ∧
        total / 2 ≤ max 0 ((cost 0).real (Icc 0 1) - 0)
    rw [sub_zero, min_eq_left hnonneg, max_eq_right hnonneg, htotalval]
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor <;> linarith
  obtain ⟨x, hcut⟩ := (hO [(.eval 0 0 1, total)]).complete _ hlegalCut
  have hcutval : x ∈ Icc (0 : ℝ) 1 ∧
      (cost 0).real (Icc 0 x) = (cost 0).real (Icc 0 1) / 2 := by
    have h := ((hO [(.eval 0 0 1, total)]).sound _ _ hcut).2
    simpa [ValidReply, measureProfile, prefixCost_self, htotalval, prefixCost,
      measureReal_def] using h
  obtain ⟨leftCost, hleft⟩ := (hO [(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x)]).complete (.eval 1 0 x)
    ⟨le_rfl, hcutval.1.1, hcutval.1.2⟩
  obtain ⟨rightCost, hright⟩ := (hO [(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x), (.eval 1 0 x, leftCost)]).complete (.eval 1 x 1)
    ⟨hcutval.1.1, hcutval.1.2, le_rfl⟩
  have hleftval : leftCost = (cost 1).real (Icc 0 x) := by
    have h := ((hO [(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x)]).sound _ _ hleft).2
    simpa [ValidReply, measureProfile, prefixCost_self, prefixCost, measureReal_def] using h
  have hrightval : rightCost = (cost 1).real (Ioc x 1) := by
    have h := ((hO [(.eval 0 0 1, total), (.cut 0 0 1 (total / 2), x), (.eval 1 0 x, leftCost)]).sound _ _ hright).2
    change rightCost = prefixCost (cost 1) 0 1 - prefixCost (cost 1) 0 x at h
    rw [prefix_difference_eq_interval (cost 1) hcutval.1.1 hcutval.1.2] at h
    exact h
  have htrace := twoAgentAdaptive_trace O total x leftCost rightCost htotal hcut hleft hright
  have hallocation : choiceAllocation x leftCost rightCost = twoAgentAllocation cost 0 x 1 := by
    rw [hleftval, hrightval]
    rfl
  rw [hallocation] at htrace
  refine ⟨x, hcutval.1, ?_⟩
  dsimp only
  rw [htrace]
  simpa [isCutQuery] using twoAgent_every_half_root cost hcutval.1 hcutval.2


end EnvyFreeResearch.Full.Chores
