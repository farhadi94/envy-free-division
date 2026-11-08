import EnvyFreeResearch.Full.ChoresTerminalPhysical

/-! Physical assembly of the actual closed compensation result with every
previously closed package and frozen ancestor. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
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

include good hlabel hparts hcorrect hprotect

theorem full_pool_valid :
    PoolValid (finalPool data (terminalPackage data original p t hmany out)) := by
  have hv := ComponentClosed.output_valid data.pending data.visited t.participants p
    data.packages data.frames (Outer.originalGaps data original) out hlabel cost
    (blocks data original r H) hparts hcorrect hmany good.live
    (Outer.active_package_valid data original cost r H good) good.allowed hprotect
  exact final_pool_valid data original cost r H good _ hv

include hsound

theorem full_pool_realized :
    ∀ a ∈ (finalPool data (terminalPackage data original p t hmany out)).flatMap Package.allocations,
      ∀ i q, a.cost i q=(cost i).real (material (updatedCache data original r H t.participants out a.root q)) := by
  intro a ha i q
  change a ∈ (data.closed++[terminalPackage data original p t hmany out]).flatMap Package.allocations at ha
  rw [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact closed_cost_after_patch data original cost r H good
      (ComponentClosed.nextCache data.pending data.visited t.participants data.frames
        (Outer.originalGaps data original) out (Outer.equalizerCache data original) (fronts data original r H))
      a ha i q
  · exact updated_cache_realizes data original r H t.participants out cost c hsound good hparts p hmany hlabel a ha i q

include hcard

theorem full_pool_ids :
    ((finalPool data (terminalPackage data original p t hmany out)).flatMap Package.ids).Perm
      Finset.univ.toList := by
  have hi := ComponentClosed.output_ids data.pending data.visited t.participants p
    data.packages data.frames (Outer.originalGaps data original) out hmany hlabel cost
    (blocks data original r H) hparts hcorrect good.live
    (Outer.active_package_valid data original cost r H good) good.allowed hprotect hcard
  have hperm : (Finset.univ.toList : List (Fin data.size)).Perm (List.finRange data.size) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange _)).mpr
    intro s
    simp
  apply final_pool_ids data original cost r H good
  apply hi.trans
  simpa only [List.ofFn_eq_map,List.flatMap_map] using
    hperm.flatMap_right (fun s => (data.packages s).ids)

end EnvyFreeResearch.Full.Chores.Terminal
