import EnvyFreeResearch.Full.RightmostExecution
import EnvyFreeResearch.Full.MixedCoordinates
import EnvyFreeResearch.Full.OracleStep

/-! An actual next-query protection step for the signed-density adversary.
No replay or capture property is assumed of the protocol. -/

noncomputable section
namespace EnvyFreeResearch.Full.RightmostCaptureStep
open Set OracleProtocol RightmostOracle RightmostReplay
open IntervalOracle (Profile Query)
open MixedFrontier RightmostExecution MixedCoordinates OracleStep IntervalAllocation
open RightmostOracle RightmostReplay
open scoped Classical

variable {Agent Tape : Type*} {α : ℝ}

def cutPoint (P : Profile Agent) : Query Agent → ℝ
  | .eval _ _ _ => 0
  | q@(.cut _ _ _ _) => (oracle P q).getD 0

theorem cutPoint_le_one (P : Profile Agent) (q : Query Agent) : cutPoint P q ≤ 1 := by
  cases q with
  | eval i a b => norm_num [cutPoint]
  | cut i a b t =>
    cases ho : oracle P (.cut i a b t) with
    | none => simp [cutPoint, ho]
    | some r =>
      have hv := oracle_some_valid P (.cut i a b t) r ho
      have hr : r ≤ b := hv.2.1.2
      simpa [cutPoint, ho] using hr.trans hv.1.2.2.1

def coordinate (P : Profile Agent) (q : Query Agent) (k : ℕ) : ℝ :=
  if Geometry q then
    if k = 0 then 1-q.left else if k = 1 then 1-q.right else if k = 2 then 1-cutPoint P q else 0
  else 0

def coordinateMaximum (P : Profile Agent) (q : Query Agent) : ℝ :=
  properMaximum 3 (coordinate P q)

theorem coordinateMaximum_lt_one (P : Profile Agent) (q : Query Agent) :
    coordinateMaximum P q < 1 := properMaximum_lt_one _ _

theorem coordinate_frozen {count : ℕ} {c : ℕ → ℝ} {j : ℕ} {r : ℝ}
    (hj : j < count) (hc : c j ≤ 1) (hm : properMaximum count c ≤ r) :
    TranscriptAdversary.FrozenCoordinate r (c j) := by
  by_cases heq : c j = 1
  · exact Or.inr heq
  · exact Or.inl ((coordinate_le_properMaximum count c j hj (lt_of_le_of_ne hc heq)).trans hm)

theorem maximum_frozen_geometry (P : Profile Agent) (q : Query Agent) (r : ℝ)
    (hm : coordinateMaximum P q ≤ r) (hg : Geometry q) :
    FrozenCoordinate r q.left ∧ FrozenCoordinate r q.right := by
  have hl : coordinate P q 0 ≤ 1 := by
    simpa [coordinate, hg] using (show 1-q.left ≤ 1 by linarith [hg.1])
  have hr : coordinate P q 1 ≤ 1 := by
    simpa [coordinate, hg] using (show 1-q.right ≤ 1 by linarith [hg.1, hg.2.1])
  have hfl := coordinate_frozen (count := 3) (j := 0) (by decide) hl hm
  have hfr := coordinate_frozen (count := 3) (j := 1) (by decide) hr hm
  exact ⟨by simpa [coordinate, hg, RightmostReplay.FrozenCoordinate] using hfl, by simpa [coordinate, hg, RightmostReplay.FrozenCoordinate] using hfr⟩

theorem maximum_frozen_answer (P : Profile Agent) (q : Query Agent) (x r : ℝ)
    (hx : oracle P q = some x) (hm : coordinateMaximum P q ≤ r) : FrozenAnswer r q x := by
  have hv := oracle_some_valid P q x hx
  have hg := legal_geometry hv.1
  have he := maximum_frozen_geometry P q r hm hg
  refine ⟨he.1, he.2, ?_⟩
  cases q with
  | eval i a b => trivial
  | cut i a b t =>
    have heq : coordinate P (.cut i a b t) 2 = 1-x := by simp [coordinate, hg, cutPoint, hx]
    have hb : coordinate P (.cut i a b t) 2 ≤ 1 := by
      rw [heq]
      linarith [hv.2.1.1, hv.1.1]
    have hf := coordinate_frozen (count := 3) (j := 2) (by decide) hb hm
    simpa [heq, RightmostReplay.FrozenCoordinate] using hf

/-- A formal descriptor after a return, illegal call or nonreturn is harmless;
it is not an instruction to decide or resume query-free divergence. -/
def descriptor (next : Protocol Tape (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Tape) (fuel : ℕ) (base : Agent) : Query Agent :=
  match (run next (oracle (profile S)) tape fuel []).stop with
  | .exhausted q => q
  | _ => .eval base 0 0

/-- One state update protects the actual next request on every tape whose
descriptor has the selected row and whose coordinates lie behind r. -/
theorem advance_protects_next
    (next : Protocol Tape (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Tape) (fuel : ℕ) (base j : Agent)
    (hα : 0 < α) (r : ℝ) (hlr : S.frontier < r) (hr : r < 1)
    (hf : FrozenTrace next S tape fuel)
    (hrow : (descriptor next S tape fuel base).agent = j)
    (hmax : coordinateMaximum (profile S) (descriptor next S tape fuel base) ≤ r) :
    let T := advance S hα j r hlr hr
    run next (oracle (profile T)) tape (fuel + 1) [] =
      run next (oracle (profile S)) tape (fuel + 1) [] ∧
    FrozenTrace next T tape (fuel + 1) := by
  let T := advance S hα j r hlr hr
  have hst : Extends S T := advance_extends S hα j r hlr hr
  have hquery : ∀ q, (run next (oracle (profile S)) tape fuel []).stop = .exhausted q →
      oracle (profile T) q = oracle (profile S) q := by
    intro q hq
    have hqj : q.agent = j := by simpa [descriptor, hq] using hrow
    apply RightmostOracle.oracle_eq_of_row_eq
    change (T.rows q.agent).cumulative = (S.rows q.agent).cumulative
    rw [hqj]
    change ((advance S hα j r hlr hr).rows j).cumulative = (S.rows j).cumulative
    rw [advance_fixed_row]
  have he : run next (oracle (profile T)) tape (fuel + 1) [] =
      run next (oracle (profile S)) tape (fuel + 1) [] := by
    apply OracleProtocol.replay
    · intro q x hx
      rcases succ_answer next (oracle (profile S)) tape fuel [] q x hx with hold | ⟨hq, hreply⟩
      · exact answer_preserved (profile S) (profile T) S.frontier hst.cumulative
          (fun i => (S.ceiling i).1) T.ceiling q x
          (answers_sound next (oracle (profile S)) tape fuel [] q x hold) (hf.1 q x hold)
      · rw [hquery q hq]
        exact hreply
    · intro q hq
      rcases succ_illegal next (oracle (profile S)) tape fuel [] q hq with hold | ⟨hnext, hbad⟩
      · apply illegal_preserved (profile S) (profile T) S.frontier hst.cumulative
          (fun i => by exact (T.ceiling i).1.trans (S.ceiling i).1.symm) q
          (illegal_sound next (oracle (profile S)) tape fuel [] q hold)
        exact hf.2 q hold
      · rw [hquery q hnext]
        exact hbad
  refine ⟨he, ?_, ?_⟩
  · intro q x hx
    rw [he] at hx
    rcases succ_answer next (oracle (profile S)) tape fuel [] q x hx with hold | ⟨hnext, hreply⟩
    · exact frozen_answer_mono hst.frontier q x (hf.1 q x hold)
    · have hm : coordinateMaximum (profile S) q ≤ r := by simpa [descriptor, hnext] using hmax
      exact maximum_frozen_answer (profile S) q x r hreply hm
  · intro q hq hg
    rw [he] at hq
    rcases succ_illegal next (oracle (profile S)) tape fuel [] q hq with hold | ⟨hnext, hbad⟩
    · have he := hf.2 q hold hg
      exact ⟨frozen_mono hst.frontier he.1, frozen_mono hst.frontier he.2⟩
    · have hm : coordinateMaximum (profile S) q ≤ r := by simpa [descriptor, hnext] using hmax
      exact maximum_frozen_geometry (profile S) q r hm hg

end EnvyFreeResearch.Full.RightmostCaptureStep
