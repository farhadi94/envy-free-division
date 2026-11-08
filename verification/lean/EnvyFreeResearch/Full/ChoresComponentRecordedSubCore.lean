import EnvyFreeResearch.Full.ChoresComponentRecording
import EnvyFreeResearch.Full.ChoresSubCoreMeasures

/-!
# Physical compensation primitives with recorded final retained pieces

The final alignment pass is inside the actual sequential query program.  The
program returns the SubCore assignment and both physical parts of every actual
participant mask, with all original-observer costs cached.  It pays at most
`n * k` additional Evals and no additional Cuts.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentRecording
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Persistent SubCore SubCorePhysical SubCoreLeaves Suffix SubCoreEntry
open scoped Classical

variable {n : ℕ} {Task Root : Type*} [Fintype Task] [DecidableEq Task]
  [Fintype Root] [Nonempty Root]

structure Recorded (Payload Task Root : Type*) (n : ℕ) where
  store : Store Root Payload
  allocation : Allocation Task Root (OrderedRecord n)
  cache : Masked.Cache Root n
  parts : Task → Split n

def finishProgram {Payload : Type*} (agent : Task → Fin n) (store : Store Root Payload)
    (out : Allocation Task Root (OrderedRecord n)) (cache : Masked.Cache Root n) :
    Program (Query (Fin n)) ℝ (Recorded Payload Task Root n) :=
  (recordTable (fun j => cache (out.assigned j) (agent j))
    (fun j => 1 - (out.point (out.assigned j)).record.point)).bind (fun parts =>
      .returned ⟨store, out, cache, parts⟩)

def clippedProgram (agent : Task → Fin n) (offset : Root → Fin n → ℝ)
    (cache : Masked.Cache Root n) (hcard : Fintype.card Task ≤ Fintype.card Root) :
    Program (Query (Fin n)) ℝ (Option (Recorded (ClippedRecord n) Task Root n)) :=
  (clippedPhysicalProgram agent offset cache hcard).bind (fun result =>
    match result.1.2 with
    | none => .returned none
    | some out => (finishProgram agent result.1.1 out result.2).bind
        (fun recorded => .returned (some recorded)))

def affineProgram (agent : Task → Fin n) (offset : Root → Fin n → ℝ)
    (cache : Masked.Cache Root n) (hcard : Fintype.card Task ≤ Fintype.card Root) :
    Program (Query (Fin n)) ℝ (Option (Recorded (Record n) Task Root n)) :=
  (affinePhysicalProgram agent offset cache hcard).bind (fun result =>
    match result.1.2 with
    | none => .returned none
    | some out => (finishProgram agent result.1.1 out result.2).bind
        (fun recorded => .returned (some recorded)))

def budget (n k : ℕ) : ℕ := physicalBudget n k + n * k

theorem budget_eq (n k : ℕ) :
    budget n k = n * (2 * n + 1) * sourceBudget k + n * k := by
  unfold budget physicalBudget
  ring

theorem budget_le (agent : Task → Fin n) (hinj : Function.Injective agent) :
    budget n (Fintype.card Task) ≤
      n * (2 * n + 1) * sourceBudget (Fintype.card Task) + n ^ 2 := by
  have hcard : Fintype.card Task ≤ n := by
    simpa using Fintype.card_le_of_injective agent hinj
  rw [budget_eq]
  nlinarith

def PartsCorrect (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Root → Fin n → Set ℝ) (agent : Task → Fin n) {Payload : Type*}
    (out : Recorded Payload Task Root n) : Prop := ∀ j,
  Correct (measureProfile cost) (domains (out.allocation.assigned j) (agent j))
    (1 - (out.allocation.point (out.allocation.assigned j)).record.point) (out.parts j)

theorem finish_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (domains : Root → Fin n → Set ℝ) (agent : Task → Fin n)
    {Payload : Type*} (store : Store Root Payload) (out : Allocation Task Root (OrderedRecord n))
    (cache : Masked.Cache Root n) (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ parts : Task → Split n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (finishProgram agent store out cache) prior ⟨store, out, cache, parts⟩ trace ∧
      trace.length ≤ n * Fintype.card Task ∧ trace.countP (fun qr => isCutQuery qr.1) = 0 ∧
      PartsCorrect cost domains agent (⟨store, out, cache, parts⟩ : Recorded Payload Task Root n) := by
  obtain ⟨parts, trace, hexec, hlen, hcuts, hcorrect⟩ :=
    record_table_correct cost oracle hpolicy
      (fun j => domains (out.assigned j) (agent j))
      (fun j => cache (out.assigned j) (agent j))
      (fun j => 1 - (out.point (out.assigned j)).record.point)
      (fun j => hc (out.assigned j) (agent j)) prior
  refine ⟨parts, trace, ?_, hlen, hcuts, hcorrect⟩
  simpa only [finishProgram, List.append_nil] using hexec.bind
    (fun parts => Program.returned (⟨store, out, cache, parts⟩ : Recorded Payload Task Root n))
    (Executes.returned _ (prior ++ trace))

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
  (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
  (agent : Task → Fin n) (offset : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
  (hpositive : 0 < Fintype.card Task) (hmany : Fintype.card Task < Fintype.card Root)
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
  (prior : History (Query (Fin n)) ℝ)
include hc hoffset hpositive hpolicy

theorem clipped_correct :
    ∃ out : Recorded (ClippedRecord n) Task Root n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (clippedProgram agent offset cache hmany.le) prior (some out) trace ∧
      PhysicalCorrect (clippedUtility cost domains offset) agent out.allocation ∧
      PartsCorrect cost domains agent out ∧
      trace.length ≤ budget n (Fintype.card Task) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card Task) ∧
      Masked.CacheCorrect (measureProfile cost) domains out.cache := by
  obtain ⟨store, out, next, t₁, hexec, hs, _, hr, ha, _, hQ, hC, hcache⟩ :=
    clipped_physical_correct cost domains cache hc agent offset hoffset hpositive hmany
      oracle hpolicy prior
  obtain ⟨parts, t₂, hfinish, hlen, hcuts, hparts⟩ :=
    finish_correct cost oracle hpolicy domains agent store out next hcache (prior ++ t₁)
  let result : Recorded (ClippedRecord n) Task Root n := ⟨store, out, next, parts⟩
  refine ⟨result, t₁ ++ t₂, ?_, ?_, hparts, ?_, ?_, hcache⟩
  · have htail := hfinish.bind (fun recorded => Program.returned (some recorded))
      (Executes.returned _ ((prior ++ t₁) ++ t₂))
    simpa only [clippedProgram, List.append_nil] using hexec.bind
      (fun result => match result.1.2 with
        | none => Program.returned none
        | some out => (finishProgram agent result.1.1 out result.2).bind
            (fun recorded => Program.returned (some recorded)))
      (by simpa only [List.append_nil] using htail)
  · exact clipped_allocation_physical cost domains offset (cachedTotals cache) agent
      store out hs hr ha
  · simpa only [budget, List.length_append] using Nat.add_le_add hQ hlen
  · simpa only [List.countP_append, hcuts, Nat.add_zero] using hC

theorem affine_correct
    (hwhole : ∀ p i, 0 ≤ (cost (agent i)).real (domains p (agent i)) - offset p (agent i)) :
    ∃ out : Recorded (Record n) Task Root n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (affineProgram agent offset cache hmany.le) prior (some out) trace ∧
      PhysicalCorrect (affineUtility cost domains offset) agent out.allocation ∧
      PartsCorrect cost domains agent out ∧
      trace.length ≤ budget n (Fintype.card Task) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card Task) ∧
      Masked.CacheCorrect (measureProfile cost) domains out.cache := by
  have hn : ∀ p i, 0 ≤ cachedTotals cache p (agent i) - offset p (agent i) := by
    intro p i
    rw [cached_totals_measure cost domains cache hc]
    exact hwhole p i
  obtain ⟨store, out, next, t₁, hexec, hs, _, hr, ha, hown, hQ, hC, hcache⟩ :=
    affine_physical_correct cost domains cache hc agent offset hoffset hpositive hmany
      oracle hpolicy hn prior
  obtain ⟨parts, t₂, hfinish, hlen, hcuts, hparts⟩ :=
    finish_correct cost oracle hpolicy domains agent store out next hcache (prior ++ t₁)
  let result : Recorded (Record n) Task Root n := ⟨store, out, next, parts⟩
  refine ⟨result, t₁ ++ t₂, ?_, ?_, hparts, ?_, ?_, hcache⟩
  · have htail := hfinish.bind (fun recorded => Program.returned (some recorded))
      (Executes.returned _ ((prior ++ t₁) ++ t₂))
    simpa only [affineProgram, List.append_nil] using hexec.bind
      (fun result => match result.1.2 with
        | none => Program.returned none
        | some out => (finishProgram agent result.1.1 out result.2).bind
            (fun recorded => Program.returned (some recorded)))
      (by simpa only [List.append_nil] using htail)
  · exact affine_allocation_physical cost domains offset (cachedTotals cache) agent
      store out hs hr ha hown
  · simpa only [budget, List.length_append] using Nat.add_le_add hQ hlen
  · simpa only [List.countP_append, hcuts, Nat.add_zero] using hC

end EnvyFreeResearch.Full.Chores.ComponentRecording
