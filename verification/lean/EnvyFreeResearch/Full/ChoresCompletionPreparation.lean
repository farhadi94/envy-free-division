import EnvyFreeResearch.Full.ChoresCompletionGroups
import EnvyFreeResearch.Full.ChoresCompletionAgents

/-! Actual two-group preparation, with both tentative partial allocations
and their exact ordered-cache complements. Its bound counts original
ordinary queries and all physical Cut calls. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n b c : ℕ}

structure Prepared (n b c : ℕ) where
  forB : SplitOutput n b
  forD : SplitOutput n c

def prepare (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (cacheX cacheR : List (Parent n)) : Program (Query (Fin n)) ℝ (Prepared n b c) :=
  (splitAugment (observerSet agentB) (extendAgent agentD hc) c cacheX).bind (fun forD =>
    (splitAugment (observerSet agentD) (extendAgent agentB hb) b cacheR).bind
      (fun forB => .returned ⟨forB,forD⟩))

structure Prepared.Correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (X R : Set ℝ) (out : Prepared n b c) : Prop where
  forB : out.forB.allocation.Correct cost (extendAgent agentB hb) R out.forB.original
  forD : out.forD.allocation.Correct cost (extendAgent agentD hc) X out.forD.original
  protectsB : ∀ i j, (cost (agentB i)).real R ≤
    (cost (agentB i)).real (material (out.forD.allocation.allocated j))
  protectsD : ∀ j i, (cost (agentD j)).real X ≤
    (cost (agentD j)).real (material (out.forB.allocation.allocated i))

theorem prepare_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (X R : Set ℝ) (cacheX cacheR : List (Parent n))
    (hX : CacheValid (measureProfile cost) X cacheX) (hR : CacheValid (measureProfile cost) R cacheR)
    (hsepB : ∀ i, (2 : ℝ)^(b+c+2)*(cost (agentB i)).real R ≤ (cost (agentB i)).real X)
    (hsepD : ∀ j, (2 : ℝ)^(b+c+2)*(cost (agentD j)).real X ≤ (cost (agentD j)).real R)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (prepare agentB agentD hb hc cacheX cacheR) prior out trace ∧
      trace.length ≤ (19*2^(b+c))*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 19*2^(b+c) ∧
      out.Correct cost agentB agentD hb hc X R := by
  obtain ⟨forD,t1,hexec1,hQ1,hC1,hD,hlargeD⟩ :=
    split_augment_correct cost oracle hpolicy (observerSet agentB) (extendAgent agentD hc) c X cacheX hX prior
  obtain ⟨forB,t2,hexec2,hQ2,hC2,hB,hlargeB⟩ :=
    split_augment_correct cost oracle hpolicy (observerSet agentD) (extendAgent agentB hb) b R cacheR hR (prior++t1)
  have hbudget : splitBudget (observerSet agentB).card c+splitBudget (observerSet agentD).card b ≤ 19*2^(b+c) :=
    (Nat.add_le_add (split_budget_mono _ b c (observer_card agentB))
      (split_budget_mono _ c b (observer_card agentD))).trans (two_group_budget b c hb hc)
  refine ⟨⟨forB,forD⟩,t1++t2,?_,?_,?_,⟨hB,hD,?_,?_⟩⟩
  · have htail := hexec2.bind (fun forB => Program.returned (⟨forB,forD⟩ : Prepared n b c)) (Executes.returned _ _)
    simpa only [prepare,List.append_nil] using hexec1.bind
      (fun forD => (splitAugment (observerSet agentD) (extendAgent agentB hb) b cacheR).bind
        (fun forB => Program.returned (⟨forB,forD⟩ : Prepared n b c))) htail
  · rw [List.length_append]
    exact (Nat.add_le_add hQ1 hQ2).trans (by simpa only [Nat.add_mul] using Nat.mul_le_mul_right n hbudget)
  · rw [List.countP_append]
    exact (Nat.add_le_add hC1 hC2).trans hbudget
  · intro i j
    exact (split_protection b c _ _ measureReal_nonneg (hsepB i)).trans
      (hlargeD (agentB i) (observer_mem agentB i) j)
  · intro j i
    have hsep : (2 : ℝ)^(c+b+2)*(cost (agentD j)).real X ≤ (cost (agentD j)).real R := by
      simpa only [Nat.add_comm c b] using hsepD j
    exact (split_protection c b _ _ measureReal_nonneg hsep).trans
      (hlargeB (agentD j) (observer_mem agentD j) i)

end EnvyFreeResearch.Full.Chores.Completion
