import EnvyFreeResearch.Full.ChoresComponentBoundarySubCoreProgram
import EnvyFreeResearch.Full.ChoresSubCorePhysicalEndpoint

/-! Concrete affine and clipped initial tables and complete recursive source
programs satisfy the parametric coordinate invariant. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle QueryProgram Persistent Suffix SubCorePhysical SubCoreLeaves SubCoreEntry
open scoped Classical

variable {n : ℕ} {Agent Root : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Root] [Nonempty Root]

theorem clipped_initial_known (points : Set ℝ) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (offset total : Root → Fin n → ℝ) :
    SuffixStoreKnown ClippedRecord.record points (clippedInitial offset total) := by
  intro p r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [clippedEmpty, sub_zero] using hone
  · have he := List.mem_singleton.mp hr
    subst r
    simpa only [clippedWhole, sub_self] using hzero

theorem affine_initial_known (points : Set ℝ) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (offset total : Root → Fin n → ℝ) :
    SuffixStoreKnown id points (affineInitial offset total) := by
  intro p r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [id_eq, affineEmpty, sub_zero] using hone
  · have he := List.mem_singleton.mp hr
    subst r
    simpa only [id_eq, affineWhole, sub_self] using hzero

theorem clipped_source_known (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ)
    (points : Set ℝ) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (agent : Agent → Fin n) (offset total : Root → Fin n → ℝ)
    (hcard : Fintype.card Agent ≤ Fintype.card Root)
    (prior : History (Masked.TaggedQuery Root n) ℝ)
    (out : Attempt Root (ClippedRecord n) (SubCore.Allocation Agent Root (OrderedRecord n)))
    (trace : History (Masked.TaggedQuery Root n) ℝ)
    (h : Executes oracle (SubCoreEntry.clippedProgram agent offset total hcard) prior out trace) :
    SuffixStoreKnown ClippedRecord.record (KnownBy Prod.snd points trace) out.1 ∧ ScopedBy Prod.snd points trace := by
  exact subcore_recursive_tracks Prod.snd ClippedRecord.record oracle clippedEnsure
    (clipped_leaf_tracks oracle) (Fintype.card Agent) Agent Root agent id
    (clippedWholeRecords offset total) (fun i => clippedBaseline (agent i))
    (entryAllocation hcard (fun p => orderedRecord (clippedEmpty (offset p)).record))
    (clippedInitial offset total) points hone (clipped_initial_known points hzero hone offset total)
    prior out trace h

theorem affine_source_known (oracle : AdaptiveOracle.Policy (Masked.TaggedQuery Root n) ℝ)
    (points : Set ℝ) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (agent : Agent → Fin n) (offset total : Root → Fin n → ℝ)
    (hcard : Fintype.card Agent ≤ Fintype.card Root)
    (prior : History (Masked.TaggedQuery Root n) ℝ)
    (out : Attempt Root (Record n) (SubCore.Allocation Agent Root (OrderedRecord n)))
    (trace : History (Masked.TaggedQuery Root n) ℝ)
    (h : Executes oracle (SubCoreEntry.affineProgram agent offset total hcard) prior out trace) :
    SuffixStoreKnown id (KnownBy Prod.snd points trace) out.1 ∧ ScopedBy Prod.snd points trace := by
  exact subcore_recursive_tracks Prod.snd id oracle (affineEnsure offset)
    (affine_leaf_tracks oracle offset) (Fintype.card Agent) Agent Root agent id
    (affineWholeRecords offset total) (fun i => affineBaseline offset (agent i))
    (entryAllocation hcard (fun _ => orderedRecord (virtualBottom offset)))
    (affineInitial offset total) points hone (affine_initial_known points hzero hone offset total)
    prior out trace h

theorem records_suffix_known {Payload : Type*} (view : Payload → Record n) (points : Set ℝ)
    (store : SubCorePhysical.Store Root Payload) (hstore : SuffixStoreKnown view points store)
    (out : Root → OrderedRecord n) (hrefs : Records view store id out) :
    ∀ p, 1-(out p).record.point ∈ points := by
  intro p
  obtain ⟨r, hr, heq⟩ := hrefs p
  rw [← heq]
  exact hstore p r hr

end EnvyFreeResearch.Full.Chores.Boundary
