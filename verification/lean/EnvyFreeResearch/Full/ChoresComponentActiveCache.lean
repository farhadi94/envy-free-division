import EnvyFreeResearch.Full.ChoresComponentActiveCore

/-! Ambient all-observer cache alignment for the active k-agent Core.
At most 3k output endpoints are recorded, costing at most 3nk Evals. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ActiveCore
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion

variable {n k : ℕ}

def AlignedOutcome (cache : List (Parent n)) : IntervalCore.Outcome k → Prop
  | .zero _ => True
  | .prefixes parent s => ∀ p, Aligned cache (parent p).left ∧
      Aligned cache (s.endpoint p).point ∧ Aligned cache (parent p).right

theorem aligned_of_endpoints (cache : List (Parent n)) (out : IntervalCore.Outcome k)
    (h : ∀ x ∈ coreEndpoints out, Aligned cache x) : AlignedOutcome cache out := by
  cases out with
  | zero z => trivial
  | prefixes parent s =>
    intro p
    refine ⟨h _ ?_, h _ ?_, h _ ?_⟩ <;> simp [coreEndpoints]

def cachedProgram (agent : Fin k ↪ Fin n) (c : Fin k) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (IntervalCore.Outcome k × List (Parent n)) :=
  (domainProgram agent c cache).bind (fun pair =>
    (alignManyProgram (coreEndpoints pair.1) pair.2).bind (fun fresh => .returned (pair.1, fresh)))

def cachedBudget (n k : ℕ) : ℕ := domainBudget n k + 3 * n * k

theorem cached_program_correct (hk : 2 ≤ k) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (agent : Fin k ↪ Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (c : Fin k)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : IntervalCore.Outcome k, ∃ fresh : List (Parent n),
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (cachedProgram agent c cache) prior (out, fresh) trace ∧
      trace.length ≤ cachedBudget n k ∧
      virtualCuts trace ≤ k - 1 + IntervalCore.trimBudget k ∧
      DomainCorrect (fun i => cost (agent i)) U c out ∧
      CacheValid (measureProfile cost) U fresh ∧ AlignedOutcome fresh out := by
  obtain ⟨out, first, t₁, hexec₁, hlen₁, hcuts₁, hcorrect, hfirst⟩ :=
    domain_program_correct hk cost oracle hpolicy agent U cache hc c prior
  obtain ⟨fresh, t₂, hexec₂, hlen₂, hcuts₂, hfresh, halign, _, _⟩ :=
    align_many_correct (measureProfile cost) oracle hpolicy U (coreEndpoints out) first hfirst (prior ++ t₁)
  have htail : Executes oracle
      ((alignManyProgram (coreEndpoints out) first).bind (fun fresh => Program.returned (out, fresh)))
      (prior ++ t₁) (out, fresh) t₂ := by
    simpa only [List.append_nil] using hexec₂.bind (fun fresh => Program.returned (out, fresh))
      (Executes.returned _ _)
  refine ⟨out, fresh, t₁ ++ t₂, hexec₁.bind _ htail, ?_, ?_, hcorrect, hfresh,
    aligned_of_endpoints fresh out halign⟩
  · rw [List.length_append]
    calc
      t₁.length + t₂.length ≤ domainBudget n k + n * (coreEndpoints out).length := Nat.add_le_add hlen₁ hlen₂
      _ ≤ domainBudget n k + n * (3 * k) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left n (core_endpoint_count out)) _
      _ = cachedBudget n k := by unfold cachedBudget; ring
  · change (t₁ ++ t₂).countP (fun qr => isCutQuery qr.1) ≤ _
    rw [List.countP_append]
    change virtualCuts t₁ + virtualCuts t₂ ≤ _
    simpa only [hcuts₂, add_zero] using hcuts₁

end EnvyFreeResearch.Full.Chores.ActiveCore
