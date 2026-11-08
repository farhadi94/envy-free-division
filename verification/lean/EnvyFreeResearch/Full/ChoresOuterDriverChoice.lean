import EnvyFreeResearch.Full.ChoresOuterProtected

/-! The deterministic next action reads only the current finite pending
state. Revelation scans use cached original tables, never measure values. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Scheduler Components
open scoped Classical
variable {n : ℕ} {RootId : Type*}

inductive DriverAction (data : Data n RootId) where
  | reveal (p : Fin n) (representative : p ∈ data.pending.partition.labels)
      (fresh : p ∉ data.pending.pending)
  | merge (allPending : data.pending.partition.labels ⊆ data.pending.pending)
      (cycle : ProposalCycle (data.pending.outgoing allPending))

def nextAction [NeZero n] (data : Data n RootId) : DriverAction data :=
  if h : data.pending.unrevealed.Nonempty then
    .reveal (data.pending.unrevealed.min' h)
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h)).1
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h)).2
  else
    let hall : data.pending.partition.labels ⊆ data.pending.pending :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    .merge hall (data.pending.cycle hall)

def revelationChoice (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (p : Fin n) (r : Fin n → ℝ) (H : ℝ) : Reveal.Choice n (Fin data.size) :=
  Reveal.actualChoice (fun s => (original (data.source s)).equalizers) p r H
    (data.pending.partition.component p) data.pending.partition.representative

theorem revelation_choice_correct (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (p : Fin n) (r : Fin n → ℝ) (H : ℝ) :
    (revelationChoice data original p r H).Correct
      (fun s => Reveal.classify (original (data.source s)).equalizers p r H
        (data.pending.partition.component p) data.pending.partition.representative) :=
  Reveal.actual_choice_correct _ p r H _ _

theorem action_reveal_unrevealed (data : Data n RootId) (p : Fin n)
    (hp : p ∈ data.pending.partition.labels) (hf : p ∉ data.pending.pending) :
    p ∈ data.pending.unrevealed := Finset.mem_sdiff.mpr ⟨hp,hf⟩

end EnvyFreeResearch.Full.Chores.Outer
