import EnvyFreeResearch.Full.ChoresRevealPhysical
import EnvyFreeResearch.Full.ChoresSchedulerGraphRound
import EnvyFreeResearch.Full.ChoresComponentTasks

/-! The actual continuing cohort installs a valid root-local pending
proposal. Its target is an agent label, so subsequent target mergers can
be resolved by the existing persistent proposal machinery. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Reveal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical

variable {n : ℕ} {Root : Type*} [Fintype Root] [DecidableEq Root]

def outsideAgent (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ) (C : Finset (Fin n)) : Fin n :=
  match scan table p r H C with
  | .outside q => q
  | _ => p

theorem outside_agent_component (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) (representative : Fin n → Fin n) (target : Fin n)
    (h : classify table p r H C representative=.inr target) :
    representative (outsideAgent table p r H C)=target := by
  obtain ⟨q,hq,heq⟩ := classify_outside table p r H C representative target h
  simpa only [outsideAgent,hq] using heq

def outsideProposal (state : PendingState Root (Fin n)) (tables : Root → Table n)
    (p : Fin n) (r : Fin n → ℝ) (H : ℝ) (roots : List Root) (target : Fin n) :
    Proposal (Fin roots.length) (Fin n) :=
  ⟨target,fun s => outsideAgent (tables (roots.get s)) p r H (state.partition.component p)⟩

def outsidePending (state : PendingState Root (Fin n)) (tables : Root → Table n)
    (p : Fin n) (hp : p ∈ state.partition.labels) (r : Fin n → ℝ) (H : ℝ)
    (roots : List Root) (target : Fin n) : Option (PendingState (Fin roots.length) (Fin n)) :=
  let restricted := state.restrict roots.get
  let proposed := outsideProposal state tables p r H roots target
  if h : proposed.Valid restricted.partition p then
    some (restricted.reveal p hp proposed h)
  else none

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Output n)) (index : Root → Fin xs.length) (c : Fin n)
  (hsound : ∀ s, ∃ U, Sound cost U c (xs.get (index s)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (state : PendingState Root (Fin n)) (p : Fin n) (hp : p ∈ state.partition.labels)
  (roots : List Root) (target : Fin n)
  (hchoice : actualChoice (fun s => (xs.get (index s)).equalizers) p (fun i => (cost i).real R)
    H (state.partition.component p) state.partition.representative=.outside target roots)
  (hpool : n*(4^n+2^n)+n ≤ Fintype.card Root)

include hsound hsep hr hH hscale hp hchoice hpool

theorem continuing_proposal_valid :
    (outsideProposal state (fun s => (xs.get (index s)).equalizers) p
      (fun i => (cost i).real R) H roots target).Valid state.partition p ∧
    roots.Nodup ∧
    (Fintype.card Root-n*(4^n+2^n))/n ≤ roots.length := by
  have hchosen := actual_choice_correct (fun s => (xs.get (index s)).equalizers) p
    (fun i => (cost i).real R) H (state.partition.component p) state.partition.representative
  rw [hchoice] at hchosen
  have hn : 0 < n := Nat.zero_lt_of_lt p.isLt
  have hnum : n ≤ Fintype.card Root-n*(4^n+2^n) := by omega
  have hpos : 0 < roots.length := (Nat.div_pos hnum hn).trans_le hchosen.2.1
  let s₀ : Root := roots.get ⟨0,hpos⟩
  have hm : s₀ ∈ roots := List.get_mem _ _
  have hclass := hchosen.2.2 s₀ hm
  obtain ⟨U,hs⟩ := hsound s₀
  have hpfix := (state.partition.mem_labels p).mp hp
  have hcomponent : ∀ i, i ∈ state.partition.component p ↔
      state.partition.representative i=state.partition.representative p := by
    intro i
    rw [Partition.mem_component,hpfix]
  obtain ⟨hexternal,q,hq,hphysical⟩ := tracked_outside_member hsep (index s₀) hs p hr hH hscale
    (state.partition.component p) state.partition.representative target hcomponent hclass
  have hfixed : state.partition.representative target=target := by
    rw [← hq]
    exact state.partition.fixed q
  refine ⟨⟨?_,?_⟩,hchosen.1,hchosen.2.1⟩
  · change state.partition.representative target ≠ p
    rw [hfixed,← hpfix]
    exact hexternal
  · intro s
    change state.partition.representative (outsideAgent _ p _ H (state.partition.component p))=
      state.partition.representative target
    rw [hfixed]
    exact outside_agent_component _ p _ H _ state.partition.representative target
      (hchosen.2.2 _ (List.get_mem _ _))

theorem continuing_pending_correct :
    ∃ updated : PendingState (Fin roots.length) (Fin n),
      outsidePending state (fun s => (xs.get (index s)).equalizers) p hp
        (fun i => (cost i).real R) H roots target=some updated ∧
      updated.partition=state.partition ∧
      updated.pending=insert p state.pending ∧
      Function.Injective (fun s : Fin roots.length => roots.get s) ∧
      (Fintype.card Root-n*(4^n+2^n))/n ≤ roots.length := by
  obtain ⟨hvalid,hnd,hcount⟩ := continuing_proposal_valid cost xs index c hsound R H hsep hr hH hscale
    state p hp roots target hchoice hpool
  let proposed := outsideProposal state (fun s => (xs.get (index s)).equalizers) p
    (fun i => (cost i).real R) H roots target
  let restricted := state.restrict roots.get
  let updated := restricted.reveal p hp proposed hvalid
  refine ⟨updated,?_,rfl,?_,List.nodup_iff_injective_get.mp hnd,hcount⟩
  · unfold outsidePending
    dsimp only
    exact dite_eq_left hvalid
  · exact (restricted.reveal_pending p hp proposed hvalid).trans
      (congrArg (insert p) (state.restrict_pending roots.get))

end EnvyFreeResearch.Full.Chores.Reveal
