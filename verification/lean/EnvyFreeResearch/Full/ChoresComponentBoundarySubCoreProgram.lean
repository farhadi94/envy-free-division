import EnvyFreeResearch.Full.ChoresComponentBoundarySubCoreStore

/-! Every actual recursive SubCore execution preserves the coordinate ledger.
The induction follows executable fuel and records the entire explored store;
neither successful allocation nor source fairness is used in this theorem. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle QueryProgram Persistent Suffix SubCore SubCorePhysical
open scoped Classical

universe u v
variable {n : ℕ} {GlobalParent Payload Q : Type*} [DecidableEq GlobalParent]
    (project : Q → Query (Fin n)) (view : Payload → Record n)
    (oracle : AdaptiveOracle.Policy Q ℝ)

variable {Agent Parent : Type*} [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem subcore_loop_tracks (agent : Agent → Fin n) (whole : Parent → OrderedRecord n)
    (target : Agent → Lex (ℝ × ℚ))
    (table : TrimTable (SubCorePhysical.cachedValue agent) Set.univ whole target)
    (oldOwner : Parent ↪ Agent) (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, SubCorePhysical.Store GlobalParent Payload →
      Node selected Parent (OrderedRecord n) →
      Program Q ℝ (Attempt GlobalParent Payload (Node selected Parent (OrderedRecord n))))
    (hrecurse : ∀ selected store before, Tracks project view oracle store Prod.fst (recurse selected store before))
    (fuel : ℕ) (store : SubCorePhysical.Store GlobalParent Payload)
    (s : LoopState Agent Parent (OrderedRecord n)) :
    Tracks project view oracle store Prod.fst
      (SubCorePhysical.loopProgram agent whole target table oldOwner hOwner recurse fuel store s) := by
  induction fuel generalizing store s with
  | zero =>
    unfold SubCorePhysical.loopProgram
    split_ifs <;> apply tracks_pure project view oracle <;> rfl
  | succ fuel ih =>
    rw [SubCorePhysical.loopProgram]
    split_ifs
    · apply tracks_pure project view oracle <;> rfl
    · apply tracks_bind project view oracle store Prod.fst Prod.fst
      · exact hrecurse s.selected store s.node
      · intro returned
        cases hr : returned.2 with
        | none => simp only [hr]; apply tracks_pure project view oracle <;> rfl
        | some node => simp only [hr]; exact ih returned.1 _
    · apply tracks_pure project view oracle <;> rfl

theorem subcore_stage_tracks (agent : Agent → Fin n) (whole : Parent → OrderedRecord n)
    (processed : Finset Agent) (old : Node processed Parent (OrderedRecord n))
    (hcard : processed.card < Fintype.card Parent) (hstage : processed.card+1 = Fintype.card Agent)
    (inherited : SubCore.Allocation Agent Parent (OrderedRecord n)) (benchmark : Agent → Lex (ℝ × ℚ))
    (table : TrimTable (fun i (p : contestedParents processed old.assigned) => SubCorePhysical.cachedValue agent i p.val)
      Set.univ (fun p => whole p.val)
      (stageTarget processed old.assigned hcard (fun i p => SubCorePhysical.cachedValue agent i p (whole p)) benchmark))
    (hOwner : ∀ p, contestedOwner processed old.assigned p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, SubCorePhysical.Store GlobalParent Payload →
      Node selected (contestedParents processed old.assigned) (OrderedRecord n) →
      Program Q ℝ (Attempt GlobalParent Payload (Node selected (contestedParents processed old.assigned) (OrderedRecord n))))
    (hrecurse : ∀ selected store before, Tracks project view oracle store Prod.fst (recurse selected store before))
    (store : SubCorePhysical.Store GlobalParent Payload) :
    Tracks project view oracle store Prod.fst
      (SubCorePhysical.stageProgram agent whole processed old hcard hstage inherited benchmark table hOwner recurse store) := by
  unfold SubCorePhysical.stageProgram
  apply tracks_bind project view oracle store Prod.fst Prod.fst
  · exact subcore_loop_tracks project view oracle agent _ _ table _ hOwner recurse hrecurse _ store _
  · intro returned
    cases hr : returned.2 with
    | none => simp only [hr]; apply tracks_pure project view oracle <;> rfl
    | some out =>
      simp only [hr]
      split_ifs <;> apply tracks_pure project view oracle <;> rfl

set_option maxRecDepth 3000 in
set_option maxHeartbeats 800000 in
theorem subcore_recursive_tracks
    (ensure : GlobalParent → Fin n → ℝ × ℚ → List Payload → Program Q ℝ (Lookup.Result Payload))
    (hleaf : LeafTracks project view ensure oracle) (fuel : ℕ) :
    ∀ (Agent : Type u) (Parent : Type v) [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent],
      ∀ (agent : Agent → Fin n) (parent : Parent → GlobalParent) (whole : Parent → OrderedRecord n)
        (benchmark : Agent → Lex (ℝ × ℚ)) (inherited : SubCore.Allocation Agent Parent (OrderedRecord n))
        (store : SubCorePhysical.Store GlobalParent Payload),
      Tracks project view oracle store Prod.fst
        (SubCorePhysical.recursiveProgram fuel Agent Parent view ensure agent parent whole benchmark inherited store) := by
  induction fuel with
  | zero =>
    intro Agent Parent _ _ _ _ agent parent whole benchmark inherited store
    rw [SubCorePhysical.recursiveProgram]
    apply tracks_pure project view oracle <;> rfl
  | succ fuel ih =>
    intro Agent Parent _ _ _ _ agent parent whole benchmark inherited store
    rw [SubCorePhysical.recursiveProgram]
    split_ifs with hpositive
    · apply tracks_bind project view oracle store Prod.fst Prod.fst
      · split_ifs with hzero
        · apply tracks_pure project view oracle <;> rfl
        · apply tracks_bind project view oracle store Prod.fst Prod.fst
          · exact ih _ _ _ _ _ _ _ store
          · intro out
            apply tracks_pure project view oracle <;> rfl
      · intro previous
        cases hp : previous.2 with
        | none => simp only [hp]; apply tracks_pure project view oracle <;> rfl
        | some old =>
          simp only [hp]
          split_ifs with hcard
          · apply tracks_bind project view oracle previous.1 Prod.fst Prod.fst
            · exact trim_table_tracks project view ensure oracle hleaf _ _ _ _ previous.1
            · intro prepared
              cases ht : prepared.2 with
              | none => simp only [ht]; apply tracks_pure project view oracle <;> rfl
              | some table =>
                simp only [ht]
                split_ifs with hOwner
                · apply subcore_stage_tracks project view oracle
                  intro selected current before
                  split_ifs with hzero
                  · apply tracks_pure project view oracle <;> rfl
                  · apply tracks_bind project view oracle current Prod.fst Prod.fst
                    · exact ih _ _ _ _ _ _ _ current
                    · intro out
                      apply tracks_pure project view oracle <;> rfl
                · apply tracks_pure project view oracle <;> rfl
          · apply tracks_pure project view oracle <;> rfl
    · apply tracks_pure project view oracle <;> rfl

end EnvyFreeResearch.Full.Chores.Boundary
