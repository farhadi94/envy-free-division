import EnvyFreeResearch.Full.MixedPhysicalFailure
import EnvyFreeResearch.Full.IntervalValues
import EnvyFreeResearch.Full.MixedFiniteStep

/-! Protected actual executions, with preservation proved from the concrete
least-root oracle and the signed-density update. -/

namespace EnvyFreeResearch.Full.MixedExecution
open Set TranscriptAdversary IntervalOracle OracleProtocol MixedReplay
open MixedDensity MixedFrontier MixedPhysicalFailure IntervalAllocation IntervalValues

variable {Agent Tape : Type*} {α : ℝ}

noncomputable def profile (S : State Agent α) : Profile Agent := toProfile S.rows

structure Extends (S T : State Agent α) : Prop where
  frontier : S.frontier ≤ T.frontier
  cumulative : ∀ i x, x ∈ Icc (0 : ℝ) S.frontier →
    (T.rows i).cumulative x = (S.rows i).cumulative x
  steps : MixedFiniteStep.AllStep S → MixedFiniteStep.AllStep T

theorem Extends.refl (S : State Agent α) : Extends S S := ⟨le_rfl, fun _ _ _ => rfl, id⟩

theorem Extends.trans {S T U : State Agent α} (hst : Extends S T) (htu : Extends T U) :
    Extends S U := by
  refine ⟨hst.frontier.trans htu.frontier, ?_, fun h => htu.steps (hst.steps h)⟩
  intro i x hx
  rw [htu.cumulative i x ⟨hx.1, hx.2.trans hst.frontier⟩, hst.cumulative i x hx]

theorem advance_extends (S : State Agent α) (hα : 0 < α) (j : Agent)
    (r : ℝ) (hlr : S.frontier < r) (hr : r < 1) :
    Extends S (advance S hα j r hlr hr) :=
  ⟨hlr.le, advance_prefix S hα j r hlr hr, MixedFiniteStep.advance_allStep S hα j r hlr hr⟩

theorem frozen_mono {l r x : ℝ} (hlr : l ≤ r) (hx : FrozenCoordinate l x) :
    FrozenCoordinate r x := hx.imp (fun h => h.trans hlr) id

theorem frozen_answer_mono {l r : ℝ} (hlr : l ≤ r) (q : Query Agent) (x : ℝ)
    (h : FrozenAnswer l q x) : FrozenAnswer r q x := by
  refine ⟨frozen_mono hlr h.1, frozen_mono hlr h.2.1, ?_⟩
  cases q with
  | eval i a b => trivial
  | cut i a b t => exact frozen_mono hlr h.2.2

def FrozenTrace (next : Protocol Tape (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Tape) (fuel : ℕ) : Prop :=
  (∀ q r, (q, r) ∈ (run next (oracle (profile S)) tape fuel []).answered →
    FrozenAnswer S.frontier q r) ∧
  (∀ q, (run next (oracle (profile S)) tape fuel []).stop = .illegal q →
    Geometry q → FrozenCoordinate S.frontier q.left ∧ FrozenCoordinate S.frontier q.right)

def FrozenOutput (S : State Agent α) (A : Allocation Agent) : Prop :=
  (∀ k, FrozenCoordinate S.frontier (A.left k)) ∧
  (∀ k, FrozenCoordinate S.frontier (A.right k))

def Protected (next : Protocol Tape (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Tape) (fuel : ℕ) : Prop :=
  FrozenTrace next S tape fuel ∧
  ∀ A, (run next (oracle (profile S)) tape fuel []).stop = .returned A → FrozenOutput S A

theorem replay_of_extends
    (next : Protocol Tape (Query Agent) ℝ (Allocation Agent))
    {S T : State Agent α} (hst : Extends S T) (tape : Tape) (fuel : ℕ)
    (hf : FrozenTrace next S tape fuel) :
    run next (oracle (profile T)) tape fuel [] =
      run next (oracle (profile S)) tape fuel [] := by
  apply replay_under_frontier next (profile S) (profile T) S.frontier tape fuel []
    hst.cumulative (fun i => (S.ceiling i).1) T.ceiling hf.1 hf.2

theorem protected_of_extends
    (next : Protocol Tape (Query Agent) ℝ (Allocation Agent))
    {S T : State Agent α} (hst : Extends S T) (tape : Tape) (fuel : ℕ)
    (hp : Protected next S tape fuel) : Protected next T tape fuel := by
  have he := replay_of_extends next hst tape fuel hp.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro q r hmem
    rw [he] at hmem
    exact frozen_answer_mono hst.frontier q r (hp.1.1 q r hmem)
  · intro q hstop hgeo
    rw [he] at hstop
    have h := hp.1.2 q hstop hgeo
    exact ⟨frozen_mono hst.frontier h.1, frozen_mono hst.frontier h.2⟩
  · intro A hret
    rw [he] at hret
    have h := hp.2 A hret
    exact ⟨fun k => frozen_mono hst.frontier (h.1 k),
      fun k => frozen_mono hst.frontier (h.2 k)⟩

/-- Protection implies failure of the actual returned physical allocation. -/
theorem protected_failure [Fintype Agent]
    (next : Protocol Tape (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Tape) (fuel : ℕ) (ε : ℝ)
    (hn : 3 ≤ Fintype.card Agent) (hα : 0 ≤ α) (hε : ε < α)
    (hp : Protected next S tape fuel) :
    ∀ A, (run next (oracle (profile S)) tape fuel []).stop = .returned A →
      ¬ ApproximateEF S A ε := by
  intro A hret
  exact frozen_output_failure S A hn hα hε (hp.2 A hret).1 (hp.2 A hret).2

theorem Extends.preserves_output_values {S T : State Agent α} (hst : Extends S T)
    (A : Allocation Agent) (hf : FrozenOutput S A) (observer owner : Agent) :
    MixedObstruction.value (T.rows observer) (A.share owner) =
      MixedObstruction.value (S.rows observer) (A.share owner) := by
  apply value_share_preserved (S.rows observer) (T.rows observer) A owner S.frontier
    (hst.cumulative observer) _ hf.1 hf.2
  rw [(T.ceiling observer).1, (S.ceiling observer).1]

end EnvyFreeResearch.Full.MixedExecution
