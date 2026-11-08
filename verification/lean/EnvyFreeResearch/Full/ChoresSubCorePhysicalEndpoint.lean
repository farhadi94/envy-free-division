import EnvyFreeResearch.Full.ChoresSubCoreEntry
import EnvyFreeResearch.Full.ChoresSubCoreCache

/-! Complete ordinary Eval/Cut execution of affine and clipped SubCore.
The masked dispatcher is compiled once outside every recursive call, with
its full polynomial overhead and persistent original-cost cache recorded. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCoreEntry
open Set MeasureTheory QueryProgram Persistent SubCore SubCorePhysical SubCoreLeaves Suffix IntervalOracle
open scoped Classical
variable {n : ℕ} {Agent Root : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Root] [Nonempty Root]

def physicalBudget (n k : ℕ) : ℕ := n*(2*(n*sourceBudget k)+sourceBudget k)

def affinePhysicalProgram (agent : Agent → Fin n) (offset : Root → Fin n → ℝ)
    (cache : Masked.Cache Root n) (hcard : Fintype.card Agent ≤ Fintype.card Root) :=
  Masked.translate (affineProgram agent offset (cachedTotals cache) hcard) cache

def clippedPhysicalProgram (agent : Agent → Fin n) (offset : Root → Fin n → ℝ)
    (cache : Masked.Cache Root n) (hcard : Fintype.card Agent ≤ Fintype.card Root) :=
  Masked.translate (clippedProgram agent offset (cachedTotals cache) hcard) cache

def GoodResult {Payload : Type*} [RecordValidity Root Payload] (view : Payload → Record n)
    (baseline : Fin n → Lex (ℝ × ℚ)) (initial : Store Root Payload) (agent : Agent → Fin n)
    (whole : Root → OrderedRecord n) (benchmark : Agent → Lex (ℝ × ℚ))
    (result : Attempt Root Payload (Allocation Agent Root (OrderedRecord n))) : Prop :=
  ∃ out, result.2 = some out ∧ WellFormed view baseline result.1 ∧ Extends initial result.1 ∧
    Records view result.1 id out.point ∧
    SubCore.AllocationCorrect (cachedValue agent) univ whole benchmark out ∧
    (∀ i, 0 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
  (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
  (agent : Agent → Fin n) (offset : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
  (hpositive : 0 < Fintype.card Agent) (hmany : Fintype.card Agent < Fintype.card Root)
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)

include hc hoffset hpositive hpolicy

theorem affine_physical_correct
    (hwholeNonneg : ∀ p i, 0 ≤ cachedTotals cache p (agent i)-offset p (agent i))
    (prior : OracleProtocol.History (Query (Fin n)) ℝ) :
    let P := fun p => Masked.rowProfile cost (domains p)
    letI := affineValidity P offset (cachedTotals cache)
    ∃ store out next trace,
      Executes oracle (affinePhysicalProgram agent offset cache hmany.le) prior ((store,some out),next) trace ∧
      WellFormed id (affineBaseline offset) store ∧ Extends (affineInitial offset (cachedTotals cache)) store ∧
      Records id store id out.point ∧
      SubCore.AllocationCorrect (cachedValue agent) univ (affineWholeRecords offset (cachedTotals cache))
        (fun i => affineBaseline offset (agent i)) out ∧
      (∀ i, 0 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1) ∧
      trace.length ≤ physicalBudget n (Fintype.card Agent) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card Agent) ∧
      Masked.CacheCorrect (measureProfile cost) domains next := by
  let P := fun p => Masked.rowProfile cost (domains p)
  letI := affineValidity P offset (cachedTotals cache)
  let good := GoodResult id (affineBaseline offset) (affineInitial offset (cachedTotals cache)) agent
    (affineWholeRecords offset (cachedTotals cache)) (fun i => affineBaseline offset (agent i))
  have hsource : ∀ virtual, Masked.IsLegalPolicy P virtual →
      ∃ result trace, Executes virtual (affineProgram agent offset (cachedTotals cache) hmany.le) [] result trace ∧
        good result ∧ trace.length ≤ n*sourceBudget (Fintype.card Agent) ∧ Masked.virtualCuts trace ≤ sourceBudget (Fintype.card Agent) := by
    intro virtual hvirtual
    obtain ⟨store,out,trace,hexec,hs,he,hr,ha,hn,hQ,hC⟩ := affine_program_correct P
      (masked_profile_monotone cost domains) agent offset (cachedTotals cache) hoffset
      (cached_totals_profile cost domains cache hc) hwholeNonneg hpositive hmany virtual hvirtual []
    exact ⟨(store,some out),trace,hexec,⟨out,rfl,hs,he,hr,ha,hn⟩,hQ,hC⟩
  obtain ⟨result,next,trace,hexec,hgood,hQ,hC,hcache⟩ := Masked.compile_correct cost oracle hpolicy domains
    (affineProgram agent offset (cachedTotals cache) hmany.le) cache hc prior good
    (n*sourceBudget (Fintype.card Agent)) (sourceBudget (Fintype.card Agent)) hsource
  rcases result with ⟨store,maybe⟩
  obtain ⟨out,heq,hs,he,hr,ha,hn⟩ := hgood
  dsimp only at heq
  subst maybe
  exact ⟨store,out,next,trace,hexec,hs,he,hr,ha,hn,hQ,hC,hcache⟩

theorem clipped_physical_correct (prior : OracleProtocol.History (Query (Fin n)) ℝ) :
    let P := fun p => Masked.rowProfile cost (domains p)
    letI := clippedValidity P offset (cachedTotals cache)
    ∃ store out next trace,
      Executes oracle (clippedPhysicalProgram agent offset cache hmany.le) prior ((store,some out),next) trace ∧
      WellFormed ClippedRecord.record clippedBaseline store ∧ Extends (clippedInitial offset (cachedTotals cache)) store ∧
      Records ClippedRecord.record store id out.point ∧
      SubCore.AllocationCorrect (cachedValue agent) univ (clippedWholeRecords offset (cachedTotals cache))
        (fun i => clippedBaseline (agent i)) out ∧
      (∀ i, 0 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1) ∧
      trace.length ≤ physicalBudget n (Fintype.card Agent) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ sourceBudget (Fintype.card Agent) ∧
      Masked.CacheCorrect (measureProfile cost) domains next := by
  let P := fun p => Masked.rowProfile cost (domains p)
  letI := clippedValidity P offset (cachedTotals cache)
  let good := GoodResult ClippedRecord.record clippedBaseline (clippedInitial offset (cachedTotals cache)) agent
    (clippedWholeRecords offset (cachedTotals cache)) (fun i => clippedBaseline (agent i))
  have hsource : ∀ virtual, Masked.IsLegalPolicy P virtual →
      ∃ result trace, Executes virtual (clippedProgram agent offset (cachedTotals cache) hmany.le) [] result trace ∧
        good result ∧ trace.length ≤ n*sourceBudget (Fintype.card Agent) ∧ Masked.virtualCuts trace ≤ sourceBudget (Fintype.card Agent) := by
    intro virtual hvirtual
    obtain ⟨store,out,trace,hexec,hs,he,hr,ha,hn,hQ,hC⟩ := clipped_program_correct P
      (masked_profile_monotone cost domains) agent offset (cachedTotals cache) hoffset
      (cached_totals_profile cost domains cache hc) hpositive hmany virtual hvirtual []
    exact ⟨(store,some out),trace,hexec,⟨out,rfl,hs,he,hr,ha,hn⟩,hQ,hC⟩
  obtain ⟨result,next,trace,hexec,hgood,hQ,hC,hcache⟩ := Masked.compile_correct cost oracle hpolicy domains
    (clippedProgram agent offset (cachedTotals cache) hmany.le) cache hc prior good
    (n*sourceBudget (Fintype.card Agent)) (sourceBudget (Fintype.card Agent)) hsource
  rcases result with ⟨store,maybe⟩
  obtain ⟨out,heq,hs,he,hr,ha,hn⟩ := hgood
  dsimp only at heq
  subst maybe
  exact ⟨store,out,next,trace,hexec,hs,he,hr,ha,hn,hQ,hC,hcache⟩

end EnvyFreeResearch.Full.Chores.SubCoreEntry
