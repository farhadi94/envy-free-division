import EnvyFreeResearch.Full.RefinedChoresRootState
import EnvyFreeResearch.Full.RefinedChoresPendingFrontier
import EnvyFreeResearch.Full.RefinedChoresCapacityRun

/-! Pending frontier geometry attached to the exact root-local paid graph.
Cycle normalization enlarges components while leaving the immutable atom
ranks and the physical live frame unchanged. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresRootFrontier
open ChoreComposition Chores.Scheduler Chores.Frontier RefinedChoresPartialGraph
open RefinedChoresRootState RefinedChoresCapacityRun RefinedChoresStateCapacity
open scoped Classical
variable {n : ℕ} {Root : Type*}
    (frame : Frame (Fin n) Root) (tracked : Tracked frame)
    (w : Fin n → Fin n → Fin n → ℝ) (rank : Fin n → Fin n → ℕ)
    (r : Fin n → ℝ) (H : ℝ) (E : Fin n → Finset (Fin n))

structure Frontiers where
  frontier : Fin n → Fin n
  valid : ∀ a, RefinedChoresPendingFrontier.Pending (w a) (rank a) r H (E a)
    (componentSet tracked.state (tracked.state.component a))
    (frame.allowed a) (frame.forbidden a) (frontier a)

/-- The singleton root graph and the original top-ranked owner marks
supply the full pending-frontier state before any payment. -/
def initial_frontiers (ho : frame.owner = 1) (ha : ∀ a, frame.allowed a = {a})
    (hf : ∀ a, frame.forbidden a = ∅)
    (howner : ∀ a, rank a a = n) (hrank : ∀ a i, rank a i ≤ n)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H) :
    Frontiers frame (RefinedChoresRootState.initial frame ho ha) w rank r H
      (fun a => eligible (w a) (rank a) r H) where
  frontier := id
  valid a := by
    have hcomponent : componentSet (RefinedChoresRootState.initial frame ho ha).state
        ((RefinedChoresRootState.initial frame ho ha).state.component a) = {a} := by
      apply Finset.ext
      intro b
      rw [mem_componentSet,Finset.mem_singleton]
      rfl
    rw [hcomponent,ha,hf]
    exact RefinedChoresPendingFrontier.of_invariant _ _ _ _ _ _ _ _ _
      (initial_invariant (w a) (rank a) r H a (howner a) (hrank a) (hr a) hH)
      (Finset.mem_singleton_self _)

/-- The old complete scan invariant is recovered at every selected sink. -/
theorem sink_invariant (frontiers : Frontiers frame tracked w rank r H E)
    (c : tracked.state.Component) (hc : (c : Fin n) ∉ tracked.state.pending) :
    Invariant (w c) (rank c) r H (E c) (componentSet tracked.state c)
      (frame.allowed c) (frame.forbidden c) (frontiers.frontier c) := by
  have h := frontiers.valid c
  rw [tracked.state.component_label c] at h
  exact RefinedChoresPendingFrontier.at_sink _ _ _ _ _ _ _ _ _ h
    (sink_allowed frame tracked c hc h.frontier_allowed)

/-- The actual paid frame update and recorded proposal preserve all label
frontiers; the source's outside target remains marked as pending. -/
def pay_frontiers (frontiers : Frontiers frame tracked w rank r H E)
    (c : tracked.state.Component) (hc : (c : Fin n) ∉ tracked.state.pending)
    (q : Fin n) (hq : q ∉ componentSet tracked.state c)
    (hstop : (Stop.outside q).Valid (rank c) (E c) (componentSet tracked.state c))
    (hsmall : ∀ a : Fin n, rank c q ≤ a.val → Small (w c) r H a) :
    Frontiers (RefinedChoresDeferredPayment.pay frame (componentSet tracked.state c) c q)
      (payTracked frame tracked c hc q hq) w rank r H E where
  frontier := Function.update frontiers.frontier c q
  valid a := by
    by_cases ha : a = c
    · subst a
      have h := RefinedChoresPendingFrontier.pay (w c) (rank c) r H (E c)
        (componentSet tracked.state c) (frame.allowed c) (frame.forbidden c)
        (frontiers.frontier c) q (sink_invariant frame tracked w rank r H E frontiers c hc)
        hstop hsmall
      simp only [Function.update_self,RefinedChoresDeferredPayment.pay,ite_true]
      change RefinedChoresPendingFrontier.Pending (w c) (rank c) r H (E c)
        (componentSet tracked.state (tracked.state.component c))
        (insert q (frame.allowed c)) (frame.forbidden c ∪ (componentSet tracked.state c \ frame.allowed c)) q
      rw [tracked.state.component_label c]
      exact h
    · change RefinedChoresPendingFrontier.Pending (w a) (rank a) r H (E a)
        (componentSet tracked.state (tracked.state.component a))
        ((RefinedChoresDeferredPayment.pay frame (componentSet tracked.state c) c q).allowed a)
        ((RefinedChoresDeferredPayment.pay frame (componentSet tracked.state c) c q).forbidden a)
        (Function.update frontiers.frontier c q a)
      simpa only [RefinedChoresDeferredPayment.pay,ha,ite_false,Function.update_of_ne ha]
        using frontiers.valid a

/-- Normalization preserves every label's frontier invariant, not only
that of the representative retained by a merger. -/
theorem normalize_frontiers (frontiers : Frontiers frame tracked w rank r H E)
    (protectedLabel : Fin n)
    (hp : tracked.state.partition.representative protectedLabel = protectedLabel) :
    ∃ result : Tracked frame,
      ¬ Nonempty (Cycle result.state) ∧
      capacity tracked.state ≤ capacity result.state ∧
      result.state.partition.representative protectedLabel = protectedLabel ∧
      Nonempty (Frontiers frame result w rank r H E) := by
  obtain ⟨state,graph,hn,hcap,hp,hgrow,hexact⟩ :=
    normalization_with_capacity tracked.state tracked.graph protectedLabel hp
  let result : Tracked frame := ⟨state,graph,
    fun a b => (tracked.exact a b).trans (hexact a b).symm,tracked.owner_identity⟩
  refine ⟨result,hn,hcap,hp,⟨⟨frontiers.frontier,?_⟩⟩⟩
  intro a
  apply RefinedChoresPendingFrontier.grow _ _ _ _ _ _ _ _ _ _ (frontiers.valid a)
  intro b hb
  rw [mem_componentSet] at hb ⊢
  exact hgrow b a hb

end EnvyFreeResearch.Full.RefinedChoresRootFrontier
#print axioms EnvyFreeResearch.Full.RefinedChoresRootFrontier.normalize_frontiers

#print axioms EnvyFreeResearch.Full.RefinedChoresRootFrontier.pay_frontiers
