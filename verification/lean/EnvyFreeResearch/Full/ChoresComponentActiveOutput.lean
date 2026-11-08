import EnvyFreeResearch.Full.ChoresComponentActiveParts

/-! The active Core exposes root's recursive allocation interface on the
literal allocated domain, plus a truthful original-observer residue cache.
Both cutter progress bounds retain the active population size k. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ActiveCore
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n k : ℕ}

def allocation (cache : List (Parent n)) (out : IntervalCore.Outcome k) : Completion.Allocation n (Fin k) :=
  ⟨allocationCache cache out⟩

theorem allocated_domain (cost : Fin k → Measure ℝ) (U : Set ℝ) (c : Fin k)
    (out : IntervalCore.Outcome k) (h : DomainCorrect cost U c out) :
    (⋃ i, domainAllocation U c out i) = U \ domainResidue U out := by
  ext x
  constructor
  · intro hx
    refine ⟨h.2.2.1 ▸ Or.inl hx, ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact fun hr => disjoint_left.mp (h.2.1 i) hi hr
  · rintro ⟨hx, hr⟩
    rw [← h.2.2.1] at hx
    exact hx.resolve_right hr

theorem allocation_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k ↪ Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (c : Fin k) (out : IntervalCore.Outcome k)
    (halign : AlignedOutcome cache out) (hcorrect : DomainCorrect (fun i => cost (agent i)) U c out) :
    (allocation cache out).Sound cost agent (U \ domainResidue U out) := by
  have hm (i : Fin k) : material ((allocation cache out).pieces i) = domainAllocation U c out i :=
    (allocation_cache_correct _ U cache hc c out halign i).2.2
  constructor
  · intro i
    have hi := allocation_cache_correct _ U cache hc c out halign i
    exact ⟨hi.1, hi.2.1, rfl⟩
  · intro i j hij
    rw [hm i, hm j]
    exact hcorrect.1 hij
  · simp only [hm]
    exact allocated_domain _ U c out hcorrect
  · intro i j
    rw [hm i, hm j]
    exact hcorrect.2.2.2.1 i j

structure Output (n k : ℕ) where
  outcome : IntervalCore.Outcome k
  pieces : Completion.Allocation n (Fin k)
  residue : List (Parent n)
  cache : List (Parent n)

def program (agent : Fin k ↪ Fin n) (c : Fin k) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (Output n k) :=
  (cachedProgram agent c cache).bind (fun (out, fresh) =>
    .returned ⟨out, allocation fresh out, residueCache fresh out, fresh⟩)

theorem program_correct (hk : 2 ≤ k) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (agent : Fin k ↪ Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (c : Fin k)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Output n k, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (program agent c cache) prior out trace ∧
      trace.length ≤ cachedBudget n k ∧
      virtualCuts trace ≤ k - 1 + IntervalCore.trimBudget k ∧
      out.pieces.Sound cost agent (U \ material out.residue) ∧
      CacheValid (measureProfile cost) (material out.residue) out.residue ∧
      (∀ i, Disjoint (material (out.pieces.pieces i)) (material out.residue)) ∧
      (⋃ i, material (out.pieces.pieces i)) ∪ material out.residue = U ∧
      (cost (agent c)).real (material out.residue) ≤
        ((k - 1 : ℕ) : ℝ) / k * (cost (agent c)).real U ∧
      (∃ j, (cost (agent c)).real (material out.residue) / (k - 1 : ℕ) ≤
        (cost (agent c)).real (material (out.pieces.pieces j)) -
          (cost (agent c)).real (material (out.pieces.pieces c))) ∧
      CacheValid (measureProfile cost) U out.cache ∧ AlignedOutcome out.cache out.outcome := by
  obtain ⟨result, fresh, trace, hexec, hlen, hcuts, hcorrect, hfresh, halign⟩ :=
    cached_program_correct hk cost oracle hpolicy agent U cache hc c prior
  let out : Output n k := ⟨result, allocation fresh result, residueCache fresh result, fresh⟩
  have hres := residue_cache_correct (measureProfile cost) U fresh hfresh result halign
  have halloc := allocation_cache_correct (measureProfile cost) U fresh hfresh c result halign
  have hs := allocation_sound cost agent U fresh hfresh c result halign hcorrect
  refine ⟨out, trace, ?_, hlen, hcuts, ?_, ⟨hres.1, hres.2.1, rfl⟩, ?_, ?_, ?_, ?_, hfresh, halign⟩
  · simpa only [program, List.append_nil] using hexec.bind
      (fun (result, fresh) => Program.returned
        (⟨result, allocation fresh result, residueCache fresh result, fresh⟩ : Output n k))
      (Executes.returned _ (prior ++ trace))
  · simpa only [out, hres.2.2] using hs
  · intro i
    change Disjoint (material (allocationCache fresh result i)) (material (residueCache fresh result))
    rw [(halloc i).2.2, hres.2.2]
    exact hcorrect.2.1 i
  · change (⋃ i, material (allocationCache fresh result i)) ∪ material (residueCache fresh result) = U
    simp only [fun i => (halloc i).2.2, hres.2.2]
    exact hcorrect.2.2.1
  · simpa only [out, hres.2.2] using hcorrect.2.2.2.2.1
  · change ∃ j, (cost (agent c)).real (material (residueCache fresh result)) / (k - 1 : ℕ) ≤
      (cost (agent c)).real (material (allocationCache fresh result j)) -
        (cost (agent c)).real (material (allocationCache fresh result c))
    simpa only [fun i => (halloc i).2.2, hres.2.2] using hcorrect.2.2.2.2.2

def singletonAllocation (cache : List (Parent n)) : Completion.Allocation n (Fin 1) := ⟨fun _ => cache⟩

theorem singleton_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin 1 → Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) :
    (singletonAllocation cache).Sound cost agent U := by
  constructor
  · intro i
    exact ⟨hc.1, hc.2.1, rfl⟩
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · simpa only [singletonAllocation, iUnion_const] using hc.2.2
  · intro i j
    exact le_rfl

end EnvyFreeResearch.Full.Chores.ActiveCore
