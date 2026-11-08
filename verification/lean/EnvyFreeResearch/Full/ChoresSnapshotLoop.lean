import EnvyFreeResearch.Full.ChoresSnapshot

/-! Sequential generation of the original snapshots. Every next Core runs
on the actual remaining component cache. The full physical trace includes
all equalizer records, and the proof retains each snapshot's precise input
domain and unchanged original baseline table. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Snapshot
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Equalizers PackageGeometry ChoreComposition

variable {n : ℕ}

structure Sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (U : Set ℝ) (c : Fin n) (out : Output n) : Prop where
  core : DomainCorrect cost U c out.outcome
  parent_cache : ∀ p, CacheValid (measureProfile cost) (domainAllocation U c out.outcome p) (out.parents p)
  residue_cache : CacheValid (measureProfile cost) (domainResidue U out.outcome) out.residue
  equalizers : ∀ p i, Equalizers.Correct cost (domainAllocation U c out.outcome p)
    (baselines out.parents) i (out.equalizers (p,i))
  own_equalizers : ∀ p, (out.equalizers (p,p)).parts.prefixParts = out.parents p ∧
    (out.equalizers (p,p)).parts.suffixParts = []
  package_valid : (Package.seed (initialFrame () out.parents out.equalizers)).Valid

theorem sound_program_correct (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (program c cache) prior out trace ∧
      trace.length ≤ queryBudget n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ cutBudget n ∧
      Sound cost U c out := by
  obtain ⟨out,trace,hexec,hlen,hcuts,hcore,hparents,hresidue,heq,hown,hvalid⟩ :=
    program_correct hn cost oracle hpolicy U cache hc c prior
  exact ⟨out,trace,hexec,hlen,hcuts,⟨hcore,hparents,hresidue,heq,hown,hvalid⟩⟩

structure Batch (n : ℕ) where
  snapshots : List (Output n)
  residue : List (Parent n)

def generate (c : Fin n) : ℕ → List (Parent n) → Program (Query (Fin n)) ℝ (Batch n)
  | 0, cache => .returned ⟨[],cache⟩
  | k+1, cache => (program c cache).bind (fun first =>
      (generate c k first.residue).bind (fun tail =>
        .returned ⟨first::tail.snapshots,tail.residue⟩))

inductive Chain (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)] (c : Fin n) :
    Set ℝ → List (Output n) → List (Parent n) → Prop
  | nil (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache) :
      Chain cost c U [] cache
  | cons {U : Set ℝ} {first : Output n} {rest : List (Output n)} {cache : List (Parent n)}
      (hfirst : Sound cost U c first)
      (hrest : Chain cost c (domainResidue U first.outcome) rest cache) :
      Chain cost c U (first::rest) cache

/-- This is the complete bounded physical snapshot-generation loop. A
zero-residue Core is harmless: subsequent snapshots contain only empty
material, and every request is still included in the uniform bound. -/
theorem generate_correct (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) (k : ℕ) (prior : History (Query (Fin n)) ℝ) :
    ∃ batch trace, Executes oracle (generate c k cache) prior batch trace ∧
      batch.snapshots.length = k ∧ trace.length ≤ k*queryBudget n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ k*cutBudget n ∧
      Chain cost c U batch.snapshots batch.residue := by
  induction k generalizing U cache prior with
  | zero => exact ⟨⟨[],cache⟩,[],Executes.returned _ _,rfl,by simp,by simp,Chain.nil U cache hc⟩
  | succ k ih =>
    obtain ⟨first,t₁,hfirst,hlen₁,hcuts₁,hsound⟩ :=
      sound_program_correct hn cost oracle hpolicy U cache hc c prior
    obtain ⟨tail,t₂,htail,hnodes,hlen₂,hcuts₂,hchain⟩ :=
      ih (domainResidue U first.outcome) first.residue hsound.residue_cache (prior++t₁)
    refine ⟨⟨first::tail.snapshots,tail.residue⟩,t₁++t₂,?_,?_,?_,?_,Chain.cons hsound hchain⟩
    · have ht := htail.bind (fun tail => Program.returned
        (⟨first::tail.snapshots,tail.residue⟩ : Batch n))
        (Executes.returned _ ((prior++t₁)++t₂))
      exact hfirst.bind (fun first => (generate c k first.residue).bind
        (fun tail => Program.returned (⟨first::tail.snapshots,tail.residue⟩ : Batch n)))
        (by simpa only [List.append_nil] using ht)
    · simp only [List.length_cons,hnodes]
    · simp only [List.length_append]
      calc
        t₁.length+t₂.length ≤ queryBudget n+k*queryBudget n := Nat.add_le_add hlen₁ hlen₂
        _ = (k+1)*queryBudget n := by ring
    · simp only [List.countP_append]
      calc
        t₁.countP (fun qr => isCutQuery qr.1)+t₂.countP (fun qr => isCutQuery qr.1) ≤
            cutBudget n+k*cutBudget n := Nat.add_le_add hcuts₁ hcuts₂
        _ = (k+1)*cutBudget n := by ring

end EnvyFreeResearch.Full.Chores.Snapshot
