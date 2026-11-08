import EnvyFreeResearch.Full.MixedViews
import EnvyFreeResearch.Full.PhysicalReflection

/-! The concrete greatest-root oracle on a reflected signed profile. This
is a fixed mathematical oracle, not a protocol-dependent root selector. -/

noncomputable section
namespace EnvyFreeResearch.Full.RightmostOracle
open Set MeasureTheory IntervalOracle MixedReplay MixedExecution MixedFrontier
open ExtremalRoots TranscriptAdversary PhysicalReflection
open MixedViews ProtocolMeasurable OracleStep
open scoped Classical

variable {Agent : Type*}

def reflectedProfile (P : Profile Agent) : Profile Agent where
  cumulative i x := P.cumulative i 1 - P.cumulative i (1 - x)
  continuous i := continuous_const.sub ((P.continuous i).comp (continuous_const.sub continuous_id))
  zero i := by simp

def mirrorQuery (P : Profile Agent) : Query Agent → Query Agent
  | .eval i a b => .eval i (1 - b) (1 - a)
  | .cut i a b t => .cut i (1 - b) (1 - a)
      (P.cumulative i (1 - a) - P.cumulative i (1 - b) - t)

def mirrorReply : Query Agent → ℝ → ℝ
  | .eval _ _ _ => id
  | .cut _ _ _ _ => reflectPoint

def oracle (P : Profile Agent) (q : Query Agent) : Option ℝ :=
  (IntervalOracle.oracle P (mirrorQuery P q)).map (mirrorReply q)

@[simp] theorem mirrorQuery_agent (P : Profile Agent) (q : Query Agent) :
    (mirrorQuery P q).agent = q.agent := by cases q <;> rfl

@[simp] theorem mirrorQuery_left (P : Profile Agent) (q : Query Agent) :
    (mirrorQuery P q).left = 1 - q.right := by cases q <;> rfl

@[simp] theorem mirrorQuery_right (P : Profile Agent) (q : Query Agent) :
    (mirrorQuery P q).right = 1 - q.left := by cases q <;> rfl

theorem mirror_geometry (P : Profile Agent) (q : Query Agent) :
    Geometry (mirrorQuery P q) ↔ Geometry q := by
  simp only [Geometry, mirrorQuery_left, mirrorQuery_right]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem mirror_legal (P : Profile Agent) (q : Query Agent) :
    Legal P (mirrorQuery P q) ↔ Legal (reflectedProfile P) q := by
  cases q with
  | eval i a b =>
    change Geometry (mirrorQuery P (.eval i a b)) ↔ Geometry (.eval i a b)
    exact mirror_geometry P _
  | cut i a b t =>
    have hg := mirror_geometry P (.cut i a b t)
    have ht : LegalTarget (P.cumulative i) (1 - b) (1 - a)
        (P.cumulative i (1 - a) - P.cumulative i (1 - b) - t) ↔
        LegalTarget ((reflectedProfile P).cumulative i) a b t := by
      simp only [LegalTarget, reflectedProfile]
      have heq : (P.cumulative i 1 - P.cumulative i (1 - b)) -
          (P.cumulative i 1 - P.cumulative i (1 - a)) =
          P.cumulative i (1 - a) - P.cumulative i (1 - b) := by ring
      rw [heq]
      by_cases hB : 0 ≤ P.cumulative i (1 - a) - P.cumulative i (1 - b)
      · simp only [min_eq_left hB, max_eq_right hB]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      · have hB' := le_of_not_ge hB
        simp only [min_eq_right hB', max_eq_left hB']
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    change (0 ≤ 1-b ∧ 1-b ≤ 1-a ∧ 1-a ≤ 1 ∧ _) ↔
      (0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ _)
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, ht.mp h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, ht.mpr h4⟩

theorem oracle_none_iff (P : Profile Agent) (q : Query Agent) :
    oracle P q = none ↔ ¬ Legal (reflectedProfile P) q := by
  simp only [oracle, Option.map_eq_none_iff, IntervalOracle.oracle_none_iff, mirror_legal]

theorem oracle_cut_last (P : Profile Agent) (i : Agent) (a b t r : ℝ)
    (h : oracle P (.cut i a b t) = some r) :
    LastRoot ((reflectedProfile P).cumulative i) a b t r := by
  obtain ⟨u, hu, hur⟩ := Option.map_eq_some_iff.mp h
  have hroot := IntervalOracle.oracle_cut_first P i (1-b) (1-a)
    (P.cumulative i (1-a) - P.cumulative i (1-b) - t) u hu
  have hr := first_reflects_to_last hroot
  change LastRoot (fun x => P.cumulative i 1 - P.cumulative i (1-x))
    (1-(1-a)) (1-(1-b))
    (P.cumulative i (1-a) - P.cumulative i (1-b) -
      (P.cumulative i (1-a) - P.cumulative i (1-b) - t)) (1-u) at hr
  have ha : 1 - (1 - a) = a := by ring
  have hb : 1 - (1 - b) = b := by ring
  have ht : P.cumulative i (1-a) - P.cumulative i (1-b) -
      (P.cumulative i (1-a) - P.cumulative i (1-b) - t) = t := by ring
  have hueq : 1 - u = r := hur
  simpa only [ha, hb, ht, hueq, reflectedProfile] using hr

theorem oracle_some_valid (P : Profile Agent) (q : Query Agent) (r : ℝ)
    (h : oracle P q = some r) : Legal (reflectedProfile P) q ∧ ValidReply (reflectedProfile P) q r := by
  have hl : Legal (reflectedProfile P) q := by
    by_contra hn
    have he := (oracle_none_iff P q).mpr hn
    rw [h] at he
    contradiction
  refine ⟨hl, ?_⟩
  cases q with
  | eval i a b =>
    obtain ⟨u, hu, hur⟩ := Option.map_eq_some_iff.mp h
    have hv := (IntervalOracle.oracle_some_valid P _ u hu).2
    change u = P.cumulative i (1-a) - P.cumulative i (1-b) at hv
    change u = r at hur
    change r = (P.cumulative i 1 - P.cumulative i (1-b)) -
      (P.cumulative i 1 - P.cumulative i (1-a))
    linarith
  | cut i a b t =>
    have hr := oracle_cut_last P i a b t r h
    exact ⟨hr.location, hr.equation⟩

theorem oracle_isLegal (P : Profile Agent) :
    IsLegalOracle (reflectedProfile P) (oracle P) := by
  refine ⟨oracle_some_valid P, ?_⟩
  intro q hq
  cases ho : oracle P q with
  | some r => exact ⟨r, rfl⟩
  | none => exact False.elim (((oracle_none_iff P q).mp ho) hq)

theorem oracle_eq_of_row_eq (P P' : Profile Agent) (q : Query Agent)
    (heq : P'.cumulative q.agent = P.cumulative q.agent) : oracle P' q = oracle P q := by
  have hq : mirrorQuery P' q = mirrorQuery P q := by
    cases q with
    | eval i a b => rfl
    | cut i a b t =>
      change P'.cumulative i = P.cumulative i at heq
      simp only [mirrorQuery, heq]
  unfold oracle
  rw [hq, OracleStep.oracle_eq_of_row_eq P P' (mirrorQuery P q) (by simpa using heq)]

end EnvyFreeResearch.Full.RightmostOracle
