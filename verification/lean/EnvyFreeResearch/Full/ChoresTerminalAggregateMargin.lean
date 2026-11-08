import EnvyFreeResearch.Full.ChoresTerminalAggregate
import EnvyFreeResearch.Full.ChoresTerminalAggregateDonorPhysical
import EnvyFreeResearch.Full.ChoresTerminalPhysicalWitness

/-! An actual retained donor deviation gives a margin in the literal full
terminal allocation. All previously frozen roots remain in this pool. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot
open ComponentRecording ComponentPayments SubCoreEntry ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (p : Fin n) (t : Reveal.TerminalClass n)
  (hmany : Fintype.card t.participants < Fintype.card (Fin data.size))
  (out : ComponentClosed.Result (Root := Fin data.size) t.participants)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost r H)
  (hlabel : ∀ j ∈ t.participants, data.pending.partition.representative j=p)
  (hparts : PartsCorrect cost (domains (blocks data original r H)
    data.pending.partition.representative) Subtype.val out)
  (hcorrect : SubCoreEntry.PhysicalCorrect
    (affineUtility cost (domains (blocks data original r H) data.pending.partition.representative)
      (offsets (Outer.originalGaps data original) data.pending.partition.representative))
    Subtype.val out.allocation)
  (hprotect : ∀ i ∉ t.participants, ∀ s,
    (cost i).real (blocks data original r H s p) ≤ Outer.originalGaps data original s p i)
  (hcard : Fintype.card (Fin data.size)=Fintype.card t.participants+1)
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hG : ∀ root p, G.piece root p=(original root).piece p)


include hsound good hlabel hparts hcorrect hprotect hcard hG

theorem actual_full_allocation_donor_margin (i : Fin n) (j : t.participants)
    (hij : i ≠ (j : Fin n)) (D : ℝ)
    (hdev : D ≤ (cost i).real
      ((original (data.source (out.allocation.assigned j))).piece p \
        material (out.parts j).suffixParts) -
      Equalizers.baselines (original (data.source (out.allocation.assigned j))).parents i) :
    D ≤ (cost i).real (material ((fullAllocation data original r H p t hmany out).pieces j)) -
      (cost i).real (material ((fullAllocation data original r H p t hmany out).pieces i)) := by
  let pool := finalPool data (terminalPackage data original p t hmany out)
  let cache := updatedCache data original r H t.participants out
  have hp : PoolValid pool := full_pool_valid data original r H p t hmany out cost
    good hlabel hparts hcorrect hprotect
  have hids := full_pool_ids data original r H p t hmany out cost c hsound
    good hlabel hparts hcorrect hprotect hcard
  have hd : PoolDistinct pool := hids.nodup_iff.mpr (Finset.nodup_toList _)
  have hcost := full_pool_realized data original r H p t hmany out cost c hsound
    good hlabel hparts hcorrect hprotect
  have hsub := updated_cache_subset data original r H t.participants out cost c hsound good hparts G hG
  have hv := updated_cache_valid data original r H t.participants out cost c hsound good hparts
  have ha : actualDonor data original t.participants out j ∈ pool.flatMap Package.allocations :=
    actual_donor_full_pool_member data original p t.participants out hmany hlabel j
  have hw : D ≤ (cost i).real (material (cache (actualDonor data original t.participants out j).root p)) -
      (actualDonor data original t.participants out j).baseline i := by
    rw [← hcost _ ha i p]
    rw [actual_donor_physical_value data original r H p t.participants out cost c hsound good hlabel hparts,
      actual_donor_original_baseline data original r H t.participants out cost c hsound good]
    exact hdev
  have hm := pool_recipient_witness_margin pool hp hd G cache hsub cost hcost i j p hij
    (actualDonor data original t.participants out j) ha
    (actual_donor_owner data original p t.participants out hlabel j) D hw
  have hnd : (Outer.closePool pool).ids.Nodup := by rw [Outer.close_pool_ids]; exact hd
  have hc (k : Fin n) := ComponentPhysical.bundle_cache_correct (Outer.closePool pool) hnd
    G cache hsub (measureProfile cost) hv k
  change D ≤ (cost i).real (material (ComponentPhysical.bundleCache (Outer.closePool pool) cache j)) -
    (cost i).real (material (ComponentPhysical.bundleCache (Outer.closePool pool) cache i))
  rw [(hc j).2.2,(hc i).2.2]
  exact hm

end EnvyFreeResearch.Full.Chores.Terminal
