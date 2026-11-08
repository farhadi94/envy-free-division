import EnvyFreeResearch.Full.ChoresComponentTasks
import EnvyFreeResearch.Full.ChoresSchedulerGraphRound
import EnvyFreeResearch.ChoreComposition

/-! The survivor frame is computed from its actual executed cycle matching. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentFrames
open Components Scheduler ChoreComposition
open scoped Classical

variable {Agent Root RootId : Type*} [Fintype Agent] [DecidableEq Agent]

def nextAgent (state : PendingState Root Agent) (s : Root) (p : Agent) : Agent :=
  ((state.proposals p).map (fun q => q.nextAgent s)).getD p

theorem nextAgent_proposalAt (state : PendingState Root Agent)
    (hall : state.partition.labels ⊆ state.pending) (s : Root) (p : state.Component) :
    nextAgent state s p = (state.proposalAt hall p).nextAgent s := by
  simp only [nextAgent, state.proposalAt_spec hall p, Option.map_some, Option.getD_some]

theorem nextAgent_outside (state : PendingState Root Agent)
    (hall : state.partition.labels ⊆ state.pending) (s : Root) (p : state.Component) :
    nextAgent state s p ∉ state.partition.component p := by
  rw [nextAgent_proposalAt state hall s p, Partition.mem_component]
  have h := (state.sound p (state.proposalAt hall p) (state.proposalAt_spec hall p)).2
  exact fun heq => h.1 ((h.2 s).symm.trans heq)

variable (state : PendingState Root Agent) (hall : state.partition.labels ⊆ state.pending)
  (cycle : Components.ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (frames : Root → Frame Agent RootId)

def advance (s : Root) : Frame Agent RootId :=
  { frames s with
    owner := state.survivor hall cycle visited s
    allowed := fun p => if p ∈ state.selected hall cycle then
      insert (nextAgent state s p) ((frames s).allowed p) else (frames s).allowed p
    forbidden := fun p => if p ∈ state.selected hall cycle then
      (frames s).forbidden p ∪ (state.partition.component p \ (frames s).allowed p)
      else (frames s).forbidden p
    frontierGap := fun i p => if p ∈ state.selected hall cycle then
      (frames s).gap i (nextAgent state s p) p else (frames s).frontierGap i p }

theorem selected_iff_cycle (p : Agent) :
    p ∈ state.selected hall cycle ↔ ∃ c : state.Component, c ∈ cycle.vertices ∧ (c : Agent) = p := by
  change p ∈ (cycle.vertices.map Subtype.val).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_map]

theorem advanced_allowed (s : Root)
    (hallowed : ∀ p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
    (p i : Agent) :
    i ∈ (advance state hall cycle visited frames s).allowed p ↔
      Edge (state.survivor hall cycle visited s :: visited.graph s) p i := by
  rw [state.survivor_edges hall cycle visited s p i]
  change i ∈ (if p ∈ state.selected hall cycle then
    insert (nextAgent state s p) ((frames s).allowed p) else (frames s).allowed p) ↔ _
  by_cases hp : p ∈ state.selected hall cycle
  · rw [ite_eq_left hp, Finset.mem_insert, hallowed]
    obtain ⟨c, hc, rfl⟩ := (selected_iff_cycle state hall cycle p).mp hp
    rw [nextAgent_proposalAt state hall s c]
    constructor
    · rintro (heq | hold)
      · exact Or.inr ⟨c, hc, rfl, heq⟩
      · exact Or.inl hold
    · rintro (hold | ⟨d, hd, heq, hi⟩)
      · exact Or.inr hold
      · have hdc : d = c := Subtype.ext heq.symm
        subst d
        exact Or.inl hi
  · rw [ite_eq_right hp, hallowed]
    constructor
    · exact Or.inl
    · rintro (hold | ⟨c, hc, heq, hi⟩)
      · exact hold
      · exact False.elim (hp ((selected_iff_cycle state hall cycle p).mpr ⟨c, hc, heq.symm⟩))

theorem advance_good (s : Root)
    (hallowed : ∀ p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
    (hequalized : ∀ p i, (frames s).equalizerCost i p i = (frames s).baseline i) :
    (advance state hall cycle visited frames s).Good := by
  constructor
  · intro p
    apply (advanced_allowed state hall cycle visited frames s hallowed p _).mpr
    exact ⟨_, List.mem_cons_self, rfl⟩
  · exact fun p i _ => hequalized p i

theorem allowed_internal (s : Root) (p : Agent) (hp : p ∈ state.partition.labels)
    (hallowed : ∀ p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i) :
    (frames s).allowed p ⊆ state.partition.component p := by
  intro i hi
  rw [Partition.mem_component]
  have h := (visited.exact s p i).mp (edge_component ((hallowed p i).mp hi))
  rw [(state.partition.mem_labels p).mp hp] at h
  exact h.symm

theorem reserve_unchanged (s : Root) (p : Agent) (hp : p ∉ state.selected hall cycle)
    (i j : Agent) :
    (advance state hall cycle visited frames s).reserve i j p = (frames s).reserve i j p := by
  simp only [Frame.reserve, Frame.gap, advance, ite_eq_right hp]

theorem reserve_internal (s : Root) (p : Agent) (hp : p ∈ state.selected hall cycle)
    (i j : Agent) (hj : j ∈ state.partition.component p) :
    (advance state hall cycle visited frames s).reserve i j p ≤ (frames s).reserve i j p := by
  have hlabel := state.selected_subset hall cycle hp
  have hq := nextAgent_outside state hall s (⟨p, hlabel⟩ : state.Component)
  simpa only [Frame.reserve, Frame.gap, advance, ite_eq_left hp] using
    EnvyFreeResearch.R7Chores.internal_skip_forbid_no_growth
      (state.partition.component p) ((frames s).allowed p) ((frames s).forbidden p)
      (fun k => (frames s).gap i k p) ((frames s).frontierGap i p)
      ((frames s).gap i (nextAgent state s p) p) (nextAgent state s p) j hq hj

theorem reserve_external (s : Root) (p : Agent) (hp : p ∈ state.selected hall cycle)
    (hallowed : ∀ p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
    (hforbidden : (frames s).forbidden p ⊆ state.partition.component p)
    (i j : Agent) (hj : j ∉ state.partition.component p) :
    (advance state hall cycle visited frames s).reserve i j p =
      max 0 ((frames s).gap i (nextAgent state s p) p) := by
  have ha := allowed_internal state visited frames s p
    (state.selected_subset hall cycle hp) hallowed
  simpa only [Frame.reserve, Frame.gap, advance, ite_eq_left hp, EnvyFreeResearch.R7Chores.clipped]
    using EnvyFreeResearch.R7Chores.external_skip_forbid_reserve
      (state.partition.component p) ((frames s).allowed p) ((frames s).forbidden p)
      (fun k => (frames s).gap i k p) ((frames s).gap i (nextAgent state s p) p)
      (nextAgent state s p) j ha hforbidden hj rfl

theorem reserve_zero (s : Root) (p : Agent) (hp : p ∈ state.selected hall cycle)
    (i j : Agent) (hnew : (frames s).gap i (nextAgent state s p) p ≤ 0)
    (hcontain : ∀ k ∈ (frames s).allowed p,
      (frames s).gap i k p ≤ (frames s).gap i (nextAgent state s p) p) :
    (advance state hall cycle visited frames s).reserve i j p = 0 := by
  change EnvyFreeResearch.R7Chores.recipientReserve _ _ _ _ _ = _
  simp only [advance, ite_eq_left hp, Frame.gap]
  unfold EnvyFreeResearch.R7Chores.recipientReserve
  split_ifs with ha hf
  · rcases Finset.mem_insert.mp ha with rfl | ha
    · exact max_eq_left hnew
    · exact max_eq_left ((hcontain j ha).trans hnew)
  · rfl
  · exact max_eq_left hnew

end EnvyFreeResearch.Full.Chores.ComponentFrames
