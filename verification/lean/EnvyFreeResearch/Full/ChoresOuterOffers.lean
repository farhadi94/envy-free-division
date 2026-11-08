import EnvyFreeResearch.Full.ChoresOuterMergeGeometry
import EnvyFreeResearch.Full.ChoresComponentPhysicalProgram

/-! Actual original equalizer records instantiate the open compensation
call. In particular the protection and containment inequalities follow
from the recorded scan and clearance, rather than being input certificates. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical

variable {n : ℕ} {RootId : Type*}

def equalizerCache (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (s : Fin data.size) (p j : Fin n) : List (Parent n) :=
  ((original (data.source s)).equalizers (p,j)).parts.prefixParts

def offeredFrontier (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (s : Fin data.size) (p : Fin n) : List (Parent n) :=
  equalizerCache data original s p (ComponentFrames.nextAgent data.pending s p)

def offeredCache (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (s : Fin data.size) (p : Fin n) : List (Parent n) :=
  ((original (data.source s)).equalizers (p,ComponentFrames.nextAgent data.pending s p)).parts.suffixParts

def offeredBlocks (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (s : Fin data.size) (p : Fin n) : Set ℝ := material (offeredCache data original s p)

def offeredMaskedCache (data : Data n RootId) (original : RootId → Snapshot.Output n) : Masked.Cache (Fin data.size) n :=
  fun s i => offeredCache data original s (data.pending.partition.representative i)

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (data : Data n RootId)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)

include hsound

theorem offered_blocks_complement (s : Fin data.size) (p : Fin n) :
    offeredBlocks data (fun root => xs.get (index root)) s p=
      (xs.get (index (data.source s))).piece p \ material (offeredFrontier data (fun root => xs.get (index root)) s p) := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact offer_complement cost _ _ (snapshot_parent_cache hs p) _ p _ (snapshot_equalizers hs p)
    (hs.own_equalizers p).1 (.outside (ComponentFrames.nextAgent data.pending s p))

theorem offered_frontier_valid (s : Fin data.size) (p : Fin n) :
    CacheValid (measureProfile cost)
      (material (offeredFrontier data (fun root => xs.get (index root)) s p))
      (offeredFrontier data (fun root => xs.get (index root)) s p) := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  have hc := (snapshot_equalizers hs p (ComponentFrames.nextAgent data.pending s p)).2.1
  exact ⟨hc.1,hc.2.1,rfl⟩

theorem offered_equalizer_valid (s : Fin data.size) (p j : Fin n) :
    CacheValid (measureProfile cost)
      (material (equalizerCache data (fun root => xs.get (index root)) s p j))
      (equalizerCache data (fun root => xs.get (index root)) s p j) := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  have hc := (snapshot_equalizers hs p j).2.1
  exact ⟨hc.1,hc.2.1,rfl⟩

theorem offered_equalizer_subset (s : Fin data.size) (p j : Fin n) :
    material (equalizerCache data (fun root => xs.get (index root)) s p j) ⊆
      (xs.get (index (data.source s))).piece p := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact original_equalizer_subset cost hs p j

theorem offered_masked_cache : Masked.CacheCorrect (measureProfile cost)
    (ComponentPayments.domains (offeredBlocks data (fun root => xs.get (index root)))
      data.pending.partition.representative)
    (offeredMaskedCache data (fun root => xs.get (index root))) := by
  intro s i
  obtain ⟨U,hs⟩ := hsound (data.source s)
  have hc := (snapshot_equalizers hs (data.pending.partition.representative i)
    (ComponentFrames.nextAgent data.pending s (data.pending.partition.representative i))).2.2.1
  exact ⟨hc.1,hc.2.1,rfl⟩

include good hall

theorem selected_scan (p : Fin n) (hp : p ∈ data.pending.partition.labels) (s : Fin data.size) :
    Frontier.scan (xs.get (index (data.source s))).equalizers p (fun i => (cost i).real R) H
      (data.pending.partition.component p)=.outside (ComponentFrames.nextAgent data.pending s p) := by
  let cp : data.pending.Component := ⟨p,hp⟩
  rw [ComponentFrames.nextAgent_proposalAt data.pending hall s cp]
  exact good.pending_scan p (data.pending.proposalAt hall cp) (data.pending.proposalAt_spec hall cp) s

include hsep hr hH hscale

theorem offered_small (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (s : Fin data.size) (i : Fin n) :
    (cost i).real (offeredBlocks data (fun root => xs.get (index root)) s p) ≤
      (n : ℝ)*(cost i).real R/H := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  have hscan := selected_scan cost xs index c hsound R H data good hall p hp s
  have hv := (tracked_scan_correct hsep (index (data.source s)) hs p hr hH hscale
    (data.pending.partition.component p)).1
  rw [hscan] at hv
  exact hv.2.2.2.2 i

theorem offered_protection (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (s : Fin data.size) (i : Fin n) (hi : i ∉ data.pending.partition.component p) :
    (cost i).real (offeredBlocks data (fun root => xs.get (index root)) s p) ≤
      Clearance.gap (xs.get (index (data.source s))) i p := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  have hscan := selected_scan cost xs index c hsound R H data good hall p hp s
  have hv := (tracked_scan_correct hsep (index (data.source s)) hs p hr hH hscale
    (data.pending.partition.component p)).1
  rw [hscan] at hv
  have hprotect := hv.2.2.2.1 i hi
  change (cost i).real (offeredBlocks data (fun root => xs.get (index root)) s p) ≤ _ at hprotect
  rw [original_gap cost hs (data.frames s) (good.original_frame s) p i]
  rw [(good.original_frame s).baseline]
  exact hprotect

omit hsep hscale in
theorem offered_containment (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (s : Fin data.size) (i j : Fin n) (hj : j ∈ (data.frames s).allowed p) :
    (data.frames s).gap i j p ≤
      (data.frames s).gap i (ComponentFrames.nextAgent data.pending s p) p := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  have hscan := selected_scan cost xs index c hsound R H data good hall p hp s
  obtain ⟨hstop,_⟩ := Reveal.scan_outside_stop _ p _ H _ _ hscan (hr p).le (by linarith)
  have hinv := good.frontier s p
  have hpfix := (data.pending.partition.mem_labels p).mp hp
  change Frontier.Invariant _ _ _ _ _ (data.pending.partition.component (data.pending.partition.representative p)) _ _ _ at hinv
  rw [hpfix] at hinv
  exact original_contained_gap cost hs (data.frames s) (good.original_frame s) p _ H
    _ _ _ _ _ hinv hstop j hj i

omit hsep hr hH hscale hall in
theorem offered_frontier_value (s : Fin data.size) (p i : Fin n) :
    (data.frames s).gap i (ComponentFrames.nextAgent data.pending s p) p=
      (cost i).real (offeredBlocks data (fun root => xs.get (index root)) s p)-
        Clearance.gap (xs.get (index (data.source s))) i p := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact original_frontier_gap cost hs (data.frames s) (good.original_frame s) p _ i

end EnvyFreeResearch.Full.Chores.Outer
