import EnvyFreeResearch.Full.RightmostOracle

/-! Actual greatest-root replies are preserved by frozen reflected
coordinates. Illegal requests and arbitrary finite adaptive executions
are included. -/

namespace EnvyFreeResearch.Full.RightmostReplay
open Set TranscriptAdversary IntervalOracle OracleProtocol RightmostOracle

variable {Agent Tape Output : Type*}

abbrev Geometry (q : Query Agent) := MixedReplay.Geometry q

def FrozenCoordinate (l x : ℝ) : Prop := TranscriptAdversary.FrozenCoordinate l (1-x)

def FrozenAnswer (l : ℝ) (q : Query Agent) (r : ℝ) : Prop :=
  FrozenCoordinate l q.left ∧ FrozenCoordinate l q.right ∧
    match q with
    | .eval _ _ _ => True
    | .cut _ _ _ _ => FrozenCoordinate l r

theorem legal_geometry {P : Profile Agent} {q : Query Agent}
    (h : Legal P q) : Geometry q := MixedReplay.legal_geometry h

theorem mirrorQuery_preserved (P P' : Profile Agent) (l : ℝ)
    (hprefix : ∀ i x, x ∈ Icc (0 : ℝ) l → P'.cumulative i x = P.cumulative i x)
    (htotal : ∀ i, P'.cumulative i 1 = P.cumulative i 1)
    (q : Query Agent) (hg : Geometry q)
    (hf : FrozenCoordinate l q.left ∧ FrozenCoordinate l q.right) :
    mirrorQuery P' q = mirrorQuery P q := by
  have ha := frozen_coordinate_value (hprefix q.agent) (htotal q.agent)
    (by linarith [hg.2.1, hg.2.2] : 0 ≤ 1-q.left) hf.1
  have hb := frozen_coordinate_value (hprefix q.agent) (htotal q.agent)
    (by linarith [hg.2.2] : 0 ≤ 1-q.right) hf.2
  cases q with
  | eval i a b => rfl
  | cut i a b t =>
    change P'.cumulative i (1-a) = P.cumulative i (1-a) at ha
    change P'.cumulative i (1-b) = P.cumulative i (1-b) at hb
    simp only [mirrorQuery, ha, hb]

theorem answer_preserved (P P' : Profile Agent) (l : ℝ)
    (hprefix : ∀ i x, x ∈ Icc (0 : ℝ) l → P'.cumulative i x = P.cumulative i x)
    (htotal : ∀ i, P.cumulative i 1 = 1)
    (hceiling : ∀ i, TerminalCeiling (P'.cumulative i))
    (q : Query Agent) (r : ℝ) (hanswer : RightmostOracle.oracle P q = some r)
    (hfrozen : FrozenAnswer l q r) : RightmostOracle.oracle P' q = some r := by
  have hg := legal_geometry (RightmostOracle.oracle_some_valid P q r hanswer).1
  have h1 (i : Agent) : P'.cumulative i 1 = P.cumulative i 1 := by
    rw [(hceiling i).1, htotal i]
  have hq := mirrorQuery_preserved P P' l hprefix h1 q hg ⟨hfrozen.1,hfrozen.2.1⟩
  obtain ⟨u, hu, hur⟩ := Option.map_eq_some_iff.mp hanswer
  have hf : MixedReplay.FrozenAnswer l (mirrorQuery P q) u := by
    refine ⟨by simpa only [mirrorQuery_left, FrozenCoordinate] using hfrozen.2.1,
      by simpa only [mirrorQuery_right, FrozenCoordinate] using hfrozen.1, ?_⟩
    cases q with
    | eval i a b => trivial
    | cut i a b t =>
      have hur' : 1-u = r := hur
      have heq : 1-r = u := by linarith
      simpa only [FrozenCoordinate, heq, mirrorQuery] using hfrozen.2.2
  have hnew := MixedReplay.answer_preserved P P' l hprefix htotal hceiling
    (mirrorQuery P q) u hu hf
  unfold RightmostOracle.oracle
  rw [hq, hnew]
  simpa only [Option.map_some] using congrArg some hur

theorem illegal_preserved (P P' : Profile Agent) (l : ℝ)
    (hprefix : ∀ i x, x ∈ Icc (0 : ℝ) l → P'.cumulative i x = P.cumulative i x)
    (htotal : ∀ i, P'.cumulative i 1 = P.cumulative i 1)
    (q : Query Agent) (hillegal : RightmostOracle.oracle P q = none)
    (hfrozen : Geometry q → FrozenCoordinate l q.left ∧ FrozenCoordinate l q.right) :
    RightmostOracle.oracle P' q = none := by
  by_cases hg : Geometry q
  · have hf := hfrozen hg
    have hq := mirrorQuery_preserved P P' l hprefix htotal q hg hf
    have hnone : IntervalOracle.oracle P (mirrorQuery P q) = none :=
      Option.map_eq_none_iff.mp hillegal
    have hnew := MixedReplay.illegal_preserved P P' l hprefix htotal
      (mirrorQuery P q) hnone (fun _ =>
        ⟨by simpa only [mirrorQuery_left, FrozenCoordinate] using hf.2,
         by simpa only [mirrorQuery_right, FrozenCoordinate] using hf.1⟩)
    unfold RightmostOracle.oracle
    rw [hq,hnew]
    rfl
  · apply (RightmostOracle.oracle_none_iff P' q).mpr
    exact fun h => hg (legal_geometry h)

theorem replay_under_frontier
    (next : Protocol Tape (Query Agent) ℝ Output)
    (P P' : Profile Agent) (l : ℝ) (tape : Tape) (fuel : ℕ)
    (history : History (Query Agent) ℝ)
    (hprefix : ∀ i x, x ∈ Icc (0 : ℝ) l → P'.cumulative i x = P.cumulative i x)
    (htotal : ∀ i, P.cumulative i 1 = 1)
    (hceiling : ∀ i, TerminalCeiling (P'.cumulative i))
    (hanswers : ∀ q r, (q,r) ∈ (run next (RightmostOracle.oracle P) tape fuel history).answered →
      FrozenAnswer l q r)
    (hillegal : ∀ q, (run next (RightmostOracle.oracle P) tape fuel history).stop = .illegal q →
      Geometry q → FrozenCoordinate l q.left ∧ FrozenCoordinate l q.right) :
    run next (RightmostOracle.oracle P') tape fuel history =
      run next (RightmostOracle.oracle P) tape fuel history := by
  apply OracleProtocol.replay
  · intro q r hmem
    exact answer_preserved P P' l hprefix htotal hceiling q r
      (answers_sound next (RightmostOracle.oracle P) tape fuel history q r hmem) (hanswers q r hmem)
  · intro q hstop
    exact illegal_preserved P P' l hprefix
      (fun i => by rw [(hceiling i).1,htotal i]) q
      (illegal_sound next (RightmostOracle.oracle P) tape fuel history q hstop) (hillegal q hstop)

end EnvyFreeResearch.Full.RightmostReplay
