import EnvyFreeResearch.Full.ChoresOuterFilterSound

/-! A complete continuing revelation on the actual committed state.
The scan chooses the retained roots; rejected packages are closed, old
proposals restrict, and the new proposal is installed. The finite guard
is proved to pass from the generated original snapshots and clearance. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical

variable {n : ℕ} {RootId : Type*}

def outsideCommit (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (p : Fin n) (hp : p ∈ data.pending.partition.labels) (r : Fin n → ℝ) (H : ℝ)
    (roots : List (Fin data.size)) (target : Fin n) : Option (Data n RootId) :=
  let filtered := data.filter roots
  let proposed := Reveal.outsideProposal data.pending
    (fun s => (original (data.source s)).equalizers) p r H roots target
  if h : proposed.Valid filtered.pending.partition p then
    some (filtered.reveal p hp proposed h)
  else none

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (data : Data n RootId)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (p : Fin n) (hp : p ∈ data.pending.partition.labels)
  (roots : List (Fin data.size)) (target : Fin n)
  (hchoice : Reveal.actualChoice (fun s => (xs.get (index (data.source s))).equalizers) p
    (fun i => (cost i).real R) H (data.pending.partition.component p)
    data.pending.partition.representative=.outside target roots)
  (hpool : n*(4^n+2^n)+n ≤ data.size)

include hsound hsep hr hH hscale good hp hchoice hpool

theorem outside_commit_correct :
    ∃ updated : Data n RootId,
      outsideCommit data (fun root => xs.get (index root)) p hp (fun i => (cost i).real R) H roots target=some updated ∧
      updated.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H ∧
      updated.size=roots.length ∧
      (data.size-n*(4^n+2^n))/n ≤ updated.size ∧
      updated.cache=data.cache ∧
      updated.pending.partition=data.pending.partition ∧
      updated.pending.pending=insert p data.pending.pending ∧
      (updated.allPackages.flatMap ChoreComposition.Package.allocations).Perm
        (data.allPackages.flatMap ChoreComposition.Package.allocations) := by
  obtain ⟨hvalid,hnd,hcount⟩ := Reveal.continuing_proposal_valid cost xs
    (fun s : Fin data.size => index (data.source s)) c (fun s => hsound (data.source s))
    R H hsep hr hH hscale data.pending p hp roots target hchoice
    (by simpa only [Fintype.card_fin] using hpool)
  let original := fun root => xs.get (index root)
  let r := fun i => (cost i).real R
  let filtered := data.filter roots
  let proposed := Reveal.outsideProposal data.pending (fun s => (original (data.source s)).equalizers)
    p r H roots target
  let updated := filtered.reveal p hp proposed hvalid
  have hfiltered : filtered.Good original cost r H :=
    filter_good data original cost r H good roots hnd
  have hchosen := Reveal.actual_choice_correct (fun s => (xs.get (index (data.source s))).equalizers) p
    r H (data.pending.partition.component p) data.pending.partition.representative
  rw [hchoice] at hchosen
  have hscan : ∀ s, Frontier.scan (original (filtered.source s)).equalizers p r H
      (filtered.pending.partition.component p)=Frontier.Outcome.outside (proposed.nextAgent s) := by
    intro s
    exact Reveal.outside_agent_scan _ p r H _ data.pending.partition.representative target
      (hchosen.2.2 _ (List.get_mem _ _))
  refine ⟨updated,?_,reveal_good filtered original cost r H hfiltered p hp proposed hvalid hscan,
    rfl,?_,rfl,rfl,?_,?_⟩
  · unfold outsideCommit
    dsimp only
    exact dite_eq_left hvalid
  · change (data.size-n*(4^n+2^n))/n ≤ roots.length
    simpa only [Fintype.card_fin] using hcount
  · exact (filtered.pending.reveal_pending p hp proposed hvalid).trans
      (congrArg (insert p) (data.pending.restrict_pending roots.get))
  · exact filter_allocations_perm data roots hnd

end EnvyFreeResearch.Full.Chores.Outer
