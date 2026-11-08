import EnvyFreeResearch.Full.ChoresSubCoreCorrect
import EnvyFreeResearch.Full.ChoresSubCoreLeavesMeasures

/-! Concrete affine and clipped SubCore programs. The executable definitions
read only cached totals, offsets, indices and ordinary query replies. Every
suffix-recorder premise is discharged by a proved physical leaf program. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCoreEntry
open Set QueryProgram Persistent SubCore SubCorePhysical SubCoreLeaves Suffix IntervalOracle
open scoped Classical
variable {n : ℕ} {Agent Root : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Root] [Nonempty Root]

def affineWholeRecords (offset total : Root → Fin n → ℝ) (p : Root) : OrderedRecord n :=
  orderedRecord (affineWhole (offset p) (total p))

def clippedWholeRecords (offset total : Root → Fin n → ℝ) (p : Root) : OrderedRecord n :=
  orderedRecord (clippedWhole (offset p) (total p)).record

def affineProgram (agent : Agent → Fin n) (offset total : Root → Fin n → ℝ)
    (hcard : Fintype.card Agent ≤ Fintype.card Root) :
    Program (Masked.TaggedQuery Root n) ℝ (Attempt Root (Record n) (Allocation Agent Root (OrderedRecord n))) :=
  SubCorePhysical.recursiveProgram (Fintype.card Agent) Agent Root id (affineEnsure offset) agent id
    (affineWholeRecords offset total) (fun i => affineBaseline offset (agent i))
    (entryAllocation hcard (fun _ => orderedRecord (virtualBottom offset))) (affineInitial offset total)

def clippedProgram (agent : Agent → Fin n) (offset total : Root → Fin n → ℝ)
    (hcard : Fintype.card Agent ≤ Fintype.card Root) :
    Program (Masked.TaggedQuery Root n) ℝ (Attempt Root (ClippedRecord n) (Allocation Agent Root (OrderedRecord n))) :=
  SubCorePhysical.recursiveProgram (Fintype.card Agent) Agent Root ClippedRecord.record clippedEnsure agent id
    (clippedWholeRecords offset total) (fun i => clippedBaseline (agent i))
    (entryAllocation hcard (fun p => orderedRecord (clippedEmpty (offset p)).record)) (clippedInitial offset total)

theorem affine_program_correct (P : Root → Profile (Fin n))
    (hmono : ∀ p i, Monotone ((P p).cumulative i))
    (agent : Agent → Fin n) (offset total : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (htotal : ∀ p i, total p i = (P p).cumulative i 1)
    (hwholeNonneg : ∀ p i, 0 ≤ total p (agent i)-offset p (agent i))
    (hpositive : 0 < Fintype.card Agent) (hmany : Fintype.card Agent < Fintype.card Root)
    (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ) (hpolicy : Masked.IsLegalPolicy P oracle)
    (prior : OracleProtocol.History (Masked.TaggedQuery Root n) ℝ) :
    letI := affineValidity P offset total
    ∃ store out trace, Executes oracle (affineProgram agent offset total hmany.le) prior (store,some out) trace ∧
      WellFormed id (affineBaseline offset) store ∧ Extends (affineInitial offset total) store ∧
      Records id store id out.point ∧
      SubCore.AllocationCorrect (cachedValue agent) univ (affineWholeRecords offset total)
        (fun i => affineBaseline offset (agent i)) out ∧
      (∀ i, 0 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1) ∧
      trace.length ≤ n * sourceBudget (Fintype.card Agent) ∧ Masked.virtualCuts trace ≤ sourceBudget (Fintype.card Agent) := by
  letI := affineValidity P offset total
  have hstore := affine_initial_wellFormed P hmono offset total htotal
  have hw : Records id (affineInitial offset total) id (affineWholeRecords offset total) :=
    fun p => affine_whole_stored P offset total _ p hstore
  have hi : Input id agent id (affineWholeRecords offset total) (fun i => affineBaseline offset (agent i))
      (entryAllocation hmany.le (fun _ => orderedRecord (virtualBottom offset))) (affineInitial offset total) :=
    Or.inl ⟨fun i p => record_baseline_le id _ _ hstore p _ (hw p) (agent i),fun i p => hwholeNonneg p i⟩
  exact recursive_correct id (affineEnsure offset) (affineBaseline offset) oracle
    (fun q => isCutQuery q.2) n (Fintype.card Agent) (affine_records_targets P hmono offset total hoffset oracle hpolicy)
    agent id hpositive le_rfl hmany (affineWholeRecords offset total) (fun i => affineBaseline offset (agent i))
    (entryAllocation hmany.le (fun _ => orderedRecord (virtualBottom offset))) (affineInitial offset total)
    hstore hw (fun _ => le_rfl) hi prior

theorem clipped_program_correct (P : Root → Profile (Fin n))
    (hmono : ∀ p i, Monotone ((P p).cumulative i))
    (agent : Agent → Fin n) (offset total : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (htotal : ∀ p i, total p i = (P p).cumulative i 1)
    (hpositive : 0 < Fintype.card Agent) (hmany : Fintype.card Agent < Fintype.card Root)
    (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ) (hpolicy : Masked.IsLegalPolicy P oracle)
    (prior : OracleProtocol.History (Masked.TaggedQuery Root n) ℝ) :
    letI := clippedValidity P offset total
    ∃ store out trace, Executes oracle (clippedProgram agent offset total hmany.le) prior (store,some out) trace ∧
      WellFormed ClippedRecord.record clippedBaseline store ∧ Extends (clippedInitial offset total) store ∧
      Records ClippedRecord.record store id out.point ∧
      SubCore.AllocationCorrect (cachedValue agent) univ (clippedWholeRecords offset total)
        (fun i => clippedBaseline (agent i)) out ∧
      (∀ i, 0 ≤ ((out.point (out.assigned i)).record.formal (agent i)).1) ∧
      trace.length ≤ n * sourceBudget (Fintype.card Agent) ∧ Masked.virtualCuts trace ≤ sourceBudget (Fintype.card Agent) := by
  letI := clippedValidity P offset total
  have hstore := clipped_initial_wellFormed P offset total hoffset htotal
  have hw : Records ClippedRecord.record (clippedInitial offset total) id (clippedWholeRecords offset total) :=
    fun p => clipped_whole_stored P offset total _ p hstore
  have hi : Input ClippedRecord.record agent id (clippedWholeRecords offset total) (fun i => clippedBaseline (agent i))
      (entryAllocation hmany.le (fun p => orderedRecord (clippedEmpty (offset p)).record)) (clippedInitial offset total) :=
    Or.inl ⟨fun i p => record_baseline_le ClippedRecord.record _ _ hstore p _ (hw p) (agent i),
      fun _ _ => le_max_left _ _⟩
  exact recursive_correct ClippedRecord.record clippedEnsure clippedBaseline oracle
    (fun q => isCutQuery q.2) n (Fintype.card Agent) (clipped_records_targets P hmono offset total hoffset oracle hpolicy)
    agent id hpositive le_rfl hmany (clippedWholeRecords offset total) (fun i => clippedBaseline (agent i))
    (entryAllocation hmany.le (fun p => orderedRecord (clippedEmpty (offset p)).record)) (clippedInitial offset total)
    hstore hw (fun _ => le_rfl) hi prior

end EnvyFreeResearch.Full.Chores.SubCoreEntry
