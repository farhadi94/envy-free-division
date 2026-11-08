import EnvyFreeResearch.Full.ChoresSchedulerPartition
import EnvyFreeResearch.Full.ChoresComponentProposalCycle

/-!
# Persistent root-local pending proposals

Each proposal stores actual next-agent labels in each retained original root.
Its target is stored as an agent label, so merging that target does not leave a
stale component identifier.  Source proposals survive exactly when their source
does not merge; subset filtering restricts their root-local records literally.
-/

namespace EnvyFreeResearch.Full.Chores.Scheduler

variable {Root Agent : Type*} [Fintype Agent] [DecidableEq Agent]

structure Proposal (Root Agent : Type*) where
  targetAnchor : Agent
  nextAgent : Root → Agent

def Proposal.Valid (P : Partition Agent) (source : Agent) (q : Proposal Root Agent) : Prop :=
  P.representative q.targetAnchor ≠ source ∧
    ∀ s, P.representative (q.nextAgent s) = P.representative q.targetAnchor

def Proposal.restrict {Root' : Type*} (q : Proposal Root Agent) (includeRoot : Root' → Root) :
    Proposal Root' Agent := ⟨q.targetAnchor, q.nextAgent ∘ includeRoot⟩

theorem Proposal.Valid.restrict {P : Partition Agent} {source : Agent}
    {q : Proposal Root Agent} (h : q.Valid P source) {Root' : Type*}
    (includeRoot : Root' → Root) : (q.restrict includeRoot).Valid P source :=
  ⟨h.1, fun s => h.2 (includeRoot s)⟩

theorem Proposal.Valid.merge {P : Partition Agent} {source : Agent}
    {q : Proposal Root Agent} (h : q.Valid P source)
    (hs : source ∈ P.labels) (selected : Finset Agent) (keep : Agent)
    (hsub : selected ⊆ P.labels) (hk : keep ∈ selected) (hsource : source ∉ selected) :
    q.Valid (P.merge selected keep hsub hk) source := by
  constructor
  · intro heq
    have hfixed := (P.mem_labels source).mp hs
    have hnew : (P.merge selected keep hsub hk).representative source = source := by
      simp [Partition.merge_representative, Partition.collapse, hfixed, hsource]
    have hrel := (P.merge_relation selected keep hsub hk q.targetAnchor source).mp
      (heq.trans hnew.symm)
    rcases hrel with hrel | hrel
    · exact h.1 (hrel.trans hfixed)
    · exact hsource (hfixed ▸ hrel.2)
  · intro s
    exact congrArg (Partition.collapse selected keep) (h.2 s)

structure PendingState (Root Agent : Type*) [Fintype Agent] [DecidableEq Agent] where
  partition : Partition Agent
  proposals : Agent → Option (Proposal Root Agent)
  sound : ∀ p q, proposals p = some q → p ∈ partition.labels ∧ q.Valid partition p

namespace PendingState

def pending (state : PendingState Root Agent) : Finset Agent :=
  Finset.univ.filter (fun p => (state.proposals p).isSome)

@[simp] theorem mem_pending (state : PendingState Root Agent) (p : Agent) :
    p ∈ state.pending ↔ ∃ q, state.proposals p = some q := by
  simp [pending, Option.isSome_iff_exists]

theorem pending_subset (state : PendingState Root Agent) :
    state.pending ⊆ state.partition.labels := by
  intro p hp
  obtain ⟨q, hq⟩ := (state.mem_pending p).mp hp
  exact (state.sound p q hq).1

def unrevealed (state : PendingState Root Agent) : Finset Agent :=
  state.partition.labels \ state.pending

def initial : PendingState Root Agent where
  partition := Partition.initial
  proposals := fun _ => none
  sound := by simp

@[simp] theorem initial_pending : (initial : PendingState Root Agent).pending = ∅ := by
  ext p
  simp [initial]

def reveal (state : PendingState Root Agent) (p : Agent)
    (hp : p ∈ state.partition.labels) (q : Proposal Root Agent)
    (hq : q.Valid state.partition p) : PendingState Root Agent where
  partition := state.partition
  proposals := Function.update state.proposals p (some q)
  sound := by
    intro x r hr
    by_cases hxp : x = p
    · subst x
      simp only [Function.update_self, Option.some.injEq] at hr
      subst r
      exact ⟨hp, hq⟩
    · rw [Function.update_of_ne hxp] at hr
      exact state.sound x r hr

theorem reveal_pending (state : PendingState Root Agent) (p : Agent)
    (hp : p ∈ state.partition.labels) (q : Proposal Root Agent)
    (hq : q.Valid state.partition p) :
    (state.reveal p hp q hq).pending = insert p state.pending := by
  ext x
  by_cases h : x = p
  · subst x
    simp [reveal]
  · simp [reveal, Function.update_of_ne h, h]

def merge (state : PendingState Root Agent) (selected : Finset Agent) (keep : Agent)
    (hsub : selected ⊆ state.partition.labels) (hk : keep ∈ selected) :
    PendingState Root Agent where
  partition := state.partition.merge selected keep hsub hk
  proposals p := if p ∈ selected then none else state.proposals p
  sound := by
    intro p q hq
    by_cases hp : p ∈ selected
    · simp [hp] at hq
    · simp only [ite_eq_right hp] at hq
      obtain ⟨hlabel, hvalid⟩ := state.sound p q hq
      refine ⟨?_, hvalid.merge hlabel selected keep hsub hk hp⟩
      rw [Partition.merge_labels]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hlabel, hp⟩))

theorem merge_pending (state : PendingState Root Agent) (selected : Finset Agent) (keep : Agent)
    (hsub : selected ⊆ state.partition.labels) (hk : keep ∈ selected) :
    (state.merge selected keep hsub hk).pending = state.pending \ selected := by
  ext p
  by_cases hp : p ∈ selected <;> simp [merge, hp]

def restrict {Root' : Type*} (state : PendingState Root Agent) (includeRoot : Root' → Root) :
    PendingState Root' Agent where
  partition := state.partition
  proposals p := (state.proposals p).map (fun q => q.restrict includeRoot)
  sound := by
    intro p q hq
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hq
    exact ⟨(state.sound p r hr).1, (state.sound p r hr).2.restrict includeRoot⟩

theorem restrict_pending {Root' : Type*} (state : PendingState Root Agent)
    (includeRoot : Root' → Root) : (state.restrict includeRoot).pending = state.pending := by
  ext p
  simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [restrict]

noncomputable def proposalAt (state : PendingState Root Agent)
    (hall : state.partition.labels ⊆ state.pending) (p : state.partition.labels) :
    Proposal Root Agent :=
  ((state.mem_pending p).mp (hall p.property)).choose

theorem proposalAt_spec (state : PendingState Root Agent)
    (hall : state.partition.labels ⊆ state.pending) (p : state.partition.labels) :
    state.proposals p = some (state.proposalAt hall p) :=
  ((state.mem_pending p).mp (hall p.property)).choose_spec

noncomputable def outgoing (state : PendingState Root Agent)
    (hall : state.partition.labels ⊆ state.pending) :
    state.partition.labels → state.partition.labels := fun p =>
  ⟨state.partition.representative (state.proposalAt hall p).targetAnchor,
    state.partition.representative_mem _⟩

theorem outgoing_ne (state : PendingState Root Agent)
    (hall : state.partition.labels ⊆ state.pending) (p : state.partition.labels) :
    state.outgoing hall p ≠ p := by
  intro h
  exact (state.sound p (state.proposalAt hall p) (state.proposalAt_spec hall p)).2.1
    (congrArg Subtype.val h)

noncomputable def cycle [Nonempty Agent] (state : PendingState Root Agent)
    (hall : state.partition.labels ⊆ state.pending) :
    Components.ProposalCycle (state.outgoing hall) := by
  letI : Nonempty state.partition.labels :=
    ⟨⟨state.partition.labels_nonempty.choose, state.partition.labels_nonempty.choose_spec⟩⟩
  exact Components.proposalCycle (state.outgoing hall) (state.outgoing_ne hall)

end PendingState

end EnvyFreeResearch.Full.Chores.Scheduler
