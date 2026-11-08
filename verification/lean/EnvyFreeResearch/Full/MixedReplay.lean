import EnvyFreeResearch.Full.IntervalOracle

/-!
Actual adaptive replay for the concrete always-leftmost signed interval oracle.
Frozen endpoints preserve Eval answers and Cut legality, while frozen Cut
answers preserve the least-root rule. Malformed brackets need no protection.
-/

namespace EnvyFreeResearch.Full.MixedReplay

open Set ExtremalRoots TranscriptAdversary IntervalOracle OracleProtocol

variable {Agent Tape Output : Type*}

def Geometry (q : Query Agent) : Prop :=
  0 ≤ q.left ∧ q.left ≤ q.right ∧ q.right ≤ 1

theorem legal_geometry {P : Profile Agent} {q : Query Agent}
    (h : Legal P q) : Geometry q := by
  cases q with
  | eval i a b => exact h
  | cut i a b t => exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Eval values are not geometric coordinates. Only a Cut answer needs to
belong to the frozen prefix or equal the terminal endpoint. -/
def FrozenAnswer (l : ℝ) (q : Query Agent) (r : ℝ) : Prop :=
  FrozenCoordinate l q.left ∧ FrozenCoordinate l q.right ∧
    match q with
    | .eval _ _ _ => True
    | .cut _ _ _ _ => FrozenCoordinate l r

theorem answer_preserved (P P' : Profile Agent) (l : ℝ)
    (hprefix : ∀ i x, x ∈ Icc (0 : ℝ) l → P'.cumulative i x = P.cumulative i x)
    (htotal : ∀ i, P.cumulative i 1 = 1)
    (hceiling : ∀ i, TerminalCeiling (P'.cumulative i))
    (q : Query Agent) (r : ℝ) (hanswer : oracle P q = some r)
    (hfrozen : FrozenAnswer l q r) : oracle P' q = some r := by
  classical
  have hvalid := oracle_some_valid P q r hanswer
  have hgeo := legal_geometry hvalid.1
  have h1 : P'.cumulative q.agent 1 = P.cumulative q.agent 1 := by
    rw [(hceiling q.agent).1, htotal q.agent]
  have ha := frozen_coordinate_value (hprefix q.agent) h1 hgeo.1 hfrozen.1
  have hb := frozen_coordinate_value (hprefix q.agent) h1
    (le_trans hgeo.1 hgeo.2.1) hfrozen.2.1
  have hlegal : Legal P' q := (legal_iff_of_endpoint_eq P P' q ha hb).mpr hvalid.1
  cases q with
  | eval i a b =>
    have hr : r = P.cumulative i b - P.cumulative i a := hvalid.2
    change P'.cumulative i a = P.cumulative i a at ha
    change P'.cumulative i b = P.cumulative i b at hb
    simp [oracle, hlegal, ha, hb, hr]
  | cut i a b t =>
    have hroot := oracle_cut_first P i a b t r hanswer
    have hnew : FirstRoot (P'.cumulative i) a b t r :=
      first_reply_preserved (hprefix i) (htotal i) (hceiling i)
        hgeo.1 hfrozen.1 hfrozen.2.2 hroot
    have hcanonical := firstCut_spec P' i a b t hlegal.2.1 hlegal.2.2.2
    have heq := first_root_unique hcanonical hnew
    simp [oracle, hlegal, heq]

/-- Illegal targets are preserved as actual terminal failures. Geometry
violations are independent of the profile and need no frozen coordinates. -/
theorem illegal_preserved (P P' : Profile Agent) (l : ℝ)
    (hprefix : ∀ i x, x ∈ Icc (0 : ℝ) l → P'.cumulative i x = P.cumulative i x)
    (htotal : ∀ i, P'.cumulative i 1 = P.cumulative i 1)
    (q : Query Agent) (hillegal : oracle P q = none)
    (hfrozen : Geometry q →
      FrozenCoordinate l q.left ∧ FrozenCoordinate l q.right) :
    oracle P' q = none := by
  apply (oracle_none_iff P' q).mpr
  intro hlegal
  have hgeo := legal_geometry hlegal
  obtain ⟨hl, hr⟩ := hfrozen hgeo
  have ha := frozen_coordinate_value (hprefix q.agent) (htotal q.agent) hgeo.1 hl
  have hb := frozen_coordinate_value (hprefix q.agent) (htotal q.agent)
    (le_trans hgeo.1 hgeo.2.1) hr
  exact ((oracle_none_iff P q).mp hillegal)
    ((legal_iff_of_endpoint_eq P P' q ha hb).mp hlegal)

/-- Replay of the recursively defined adaptive execution, including its
actual terminal output, divergence, or illegal request. -/
theorem replay_under_frontier
    (next : Protocol Tape (Query Agent) ℝ Output)
    (P P' : Profile Agent) (l : ℝ) (tape : Tape) (fuel : ℕ)
    (history : History (Query Agent) ℝ)
    (hprefix : ∀ i x, x ∈ Icc (0 : ℝ) l → P'.cumulative i x = P.cumulative i x)
    (htotal : ∀ i, P.cumulative i 1 = 1)
    (hceiling : ∀ i, TerminalCeiling (P'.cumulative i))
    (hanswers : ∀ q r, (q, r) ∈ (run next (oracle P) tape fuel history).answered →
      FrozenAnswer l q r)
    (hillegal : ∀ q, (run next (oracle P) tape fuel history).stop = .illegal q →
      Geometry q → FrozenCoordinate l q.left ∧ FrozenCoordinate l q.right) :
    run next (oracle P') tape fuel history = run next (oracle P) tape fuel history := by
  apply OracleProtocol.replay
  · intro q r hmem
    exact answer_preserved P P' l hprefix htotal hceiling q r
      (answers_sound next (oracle P) tape fuel history q r hmem) (hanswers q r hmem)
  · intro q hstop
    apply illegal_preserved P P' l hprefix
      (fun i => by rw [(hceiling i).1, htotal i]) q
      (illegal_sound next (oracle P) tape fuel history q hstop)
    exact hillegal q hstop

end EnvyFreeResearch.Full.MixedReplay
