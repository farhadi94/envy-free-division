import EnvyFreeResearch.Full.ChoresCompletionFinish

/-! The actual two-group ordinary-query program, including both recursive
calls at their full enclosing histories. The recursive specifications are
explicit induction hypotheses, not a claim that the outer recursion has
already been implemented. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram

variable {n b c : ℕ}

def completeProgram (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (cacheX cacheR : List (Parent n))
    (childB : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin b)))
    (childD : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin c))) :
    Program (Query (Fin n)) ℝ (Allocation n (Sum (Fin b) (Fin c))) :=
  (prepare agentB agentD hb hc cacheX cacheR).bind (fun prepared =>
    (childD prepared.forD.allocation.remainder).bind (fun outD =>
      (childB prepared.forB.allocation.remainder).bind
        (fun outB => .returned (finishPrepared prepared outB outD))))

theorem complete_program_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (X R : Set ℝ) (hXR : Disjoint X R) (cacheX cacheR : List (Parent n))
    (hX : CacheValid (measureProfile cost) X cacheX) (hR : CacheValid (measureProfile cost) R cacheR)
    (hsepB : ∀ i, (2 : ℝ)^(b+c+2)*(cost (agentB i)).real R ≤ (cost (agentB i)).real X)
    (hsepD : ∀ j, (2 : ℝ)^(b+c+2)*(cost (agentD j)).real X ≤ (cost (agentD j)).real R)
    (childB : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin b)))
    (childD : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin c)))
    (QB QD CB CD : ℕ)
    (hchildB : ∀ cache, CacheValid (measureProfile cost) (material cache) cache →
      ∀ prior, ∃ out trace, Executes oracle (childB cache) prior out trace ∧ trace.length ≤ QB ∧
        trace.countP (fun qr => isCutQuery qr.1) ≤ CB ∧ out.Sound cost agentB (material cache))
    (hchildD : ∀ cache, CacheValid (measureProfile cost) (material cache) cache →
      ∀ prior, ∃ out trace, Executes oracle (childD cache) prior out trace ∧ trace.length ≤ QD ∧
        trace.countP (fun qr => isCutQuery qr.1) ≤ CD ∧ out.Sound cost agentD (material cache))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (completeProgram agentB agentD hb hc cacheX cacheR childB childD)
        prior out trace ∧
      trace.length ≤ (19*2^(b+c))*n+QD+QB ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ 19*2^(b+c)+CD+CB ∧
      out.Sound cost (Sum.elim agentB agentD) (X ∪ R) := by
  obtain ⟨prepared,t1,hexec1,hQ1,hC1,hcorrect⟩ :=
    prepare_correct cost oracle hpolicy agentB agentD hb hc X R cacheX cacheR hX hR hsepB hsepD prior
  obtain ⟨outD,t2,hexec2,hQ2,hC2,hD⟩ :=
    hchildD prepared.forD.allocation.remainder hcorrect.forD.remainder_cache (prior++t1)
  obtain ⟨outB,t3,hexec3,hQ3,hC3,hB⟩ :=
    hchildB prepared.forB.allocation.remainder hcorrect.forB.remainder_cache ((prior++t1)++t2)
  refine ⟨finishPrepared prepared outB outD,t1++(t2++t3),?_,?_,?_,
    finish_prepared_sound cost agentB agentD hb hc X R hXR prepared hcorrect outB outD hB hD⟩
  · have hlast := hexec3.bind (fun outB => Program.returned (finishPrepared prepared outB outD))
      (Executes.returned _ _)
    have hmiddle := hexec2.bind
      (fun outD => (childB prepared.forB.allocation.remainder).bind
        (fun outB => Program.returned (finishPrepared prepared outB outD))) hlast
    simpa only [completeProgram,List.append_nil] using hexec1.bind
      (fun prepared => (childD prepared.forD.allocation.remainder).bind (fun outD =>
        (childB prepared.forB.allocation.remainder).bind
          (fun outB => Program.returned (finishPrepared prepared outB outD)))) hmiddle
  · simp only [List.length_append]
    omega
  · simp only [List.countP_append]
    omega

end EnvyFreeResearch.Full.Chores.Completion
