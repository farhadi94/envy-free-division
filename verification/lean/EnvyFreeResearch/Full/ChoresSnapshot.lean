import EnvyFreeResearch.Full.ChoresPackageInitial

/-! A complete physical chore snapshot: Core, every original equalizer,
and the initial package ledger. The actual sequential program reads only
cached costs and ordinary oracle replies. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Snapshot
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Equalizers PackageGeometry ChoreComposition
open scoped Classical

structure Output (n : ℕ) where
  outcome : IntervalCore.Outcome n
  cache : List (Parent n)
  equalizers : Table n

def Output.parents {n : ℕ} (out : Output n) : Fin n → List (Parent n) :=
  allocationCache out.cache out.outcome

def Output.residue {n : ℕ} (out : Output n) : List (Parent n) := residueCache out.cache out.outcome

def program {n : ℕ} (c : Fin n) (cache : List (Parent n)) : Program (Query (Fin n)) ℝ (Output n) :=
  (cachedDomainCoreProgram c cache).bind (fun core =>
    (recordTable (allocationCache core.2 core.1)).bind (fun equalizers =>
      .returned ⟨core.1,core.2,equalizers⟩))

def queryBudget (n : ℕ) : ℕ := cachedDomainCoreBudget n+n^3
def cutBudget (n : ℕ) : ℕ := n-1+IntervalCore.trimBudget n+n^2

theorem program_correct {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Output n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (program c cache) prior out trace ∧
      trace.length ≤ queryBudget n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ cutBudget n ∧
      DomainCorrect cost U c out.outcome ∧
      (∀ p, CacheValid (measureProfile cost) (domainAllocation U c out.outcome p) (out.parents p)) ∧
      CacheValid (measureProfile cost) (domainResidue U out.outcome) out.residue ∧
      (∀ p i, Equalizers.Correct cost (domainAllocation U c out.outcome p)
        (baselines out.parents) i (out.equalizers (p,i))) ∧
      (∀ p, (out.equalizers (p,p)).parts.prefixParts = out.parents p ∧
        (out.equalizers (p,p)).parts.suffixParts = []) ∧
      (Package.seed (initialFrame () out.parents out.equalizers)).Valid := by
  obtain ⟨out,fresh,t₁,hcore,hlen₁,hcuts₁,hcorrect,hparents,hresidue⟩ :=
    recorded_core_correct hn cost oracle hpolicy U cache hc c prior
  have hEF := hcorrect.2.2.2.1
  obtain ⟨table,t₂,htable,hlen₂,hcuts₂,hequalizers,hown⟩ :=
    record_table_correct cost oracle hpolicy (domainAllocation U c out)
      (allocationCache fresh out) hparents hEF (prior++t₁)
  have hinitial := recorded_initial_package cost () (domainAllocation U c out)
    (allocationCache fresh out) hparents hEF table hequalizers (fun p => (hown p).1)
  refine ⟨⟨out,fresh,table⟩,t₁++t₂,?_,?_,?_,hcorrect,hparents,hresidue,
    hequalizers,hown,hinitial.1⟩
  · have htable' := htable.bind (fun table => Program.returned (⟨out,fresh,table⟩ : Output n))
      (Executes.returned _ ((prior++t₁)++t₂))
    have h := hcore.bind (fun core => (recordTable (allocationCache core.2 core.1)).bind
      (fun equalizers => Program.returned (⟨core.1,core.2,equalizers⟩ : Output n)))
      (by simpa only [List.append_nil] using htable')
    exact h
  · simpa only [List.length_append,queryBudget] using Nat.add_le_add hlen₁ hlen₂
  · simpa only [List.countP_append,virtualCuts,cutBudget] using Nat.add_le_add hcuts₁ hcuts₂

end EnvyFreeResearch.Full.Chores.Snapshot
