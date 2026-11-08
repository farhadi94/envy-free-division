import EnvyFreeResearch.TranscriptAdversary
import EnvyFreeResearch.Full.OracleProtocol

/-!
Concrete signed interval queries and the always-leftmost oracle.
The oracle is constructed from continuous cumulative functions; its root
equations and preservation are proved, not assumed as protocol fields.
Finite-variation signed-measure realization is a separate profile adapter.
-/

namespace EnvyFreeResearch.Full.IntervalOracle

open Set ExtremalRoots TranscriptAdversary

/-- The cumulative representation needed by the interval oracle. -/
structure Profile (Agent : Type*) where
  cumulative : Agent → ℝ → ℝ
  continuous : ∀ i, Continuous (cumulative i)
  zero : ∀ i, cumulative i 0 = 0

inductive Query (Agent : Type*)
  | eval (agent : Agent) (left right : ℝ)
  | cut (agent : Agent) (left right target : ℝ)

namespace Query
variable {Agent : Type*}

def agent : Query Agent → Agent
  | .eval i _ _ => i
  | .cut i _ _ _ => i

def left : Query Agent → ℝ
  | .eval _ a _ => a
  | .cut _ a _ _ => a

def right : Query Agent → ℝ
  | .eval _ _ b => b
  | .cut _ _ b _ => b

end Query

variable {Agent : Type*}

def Legal (P : Profile Agent) : Query Agent → Prop
  | .eval _ a b => 0 ≤ a ∧ a ≤ b ∧ b ≤ 1
  | .cut i a b t => 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      LegalTarget (P.cumulative i) a b t

def ValidReply (P : Profile Agent) : Query Agent → ℝ → Prop
  | .eval i a b, r => r = P.cumulative i b - P.cumulative i a
  | .cut i a b t, r => r ∈ Icc a b ∧
      P.cumulative i r = P.cumulative i a + t

/-- The ordinary oracle contract: every reply is valid, and every legal
query receives a reply. It imposes no envy-freeness or algorithm property. -/
structure IsLegalOracle (P : Profile Agent) (O : Query Agent → Option ℝ) : Prop where
  sound : ∀ q r, O q = some r → Legal P q ∧ ValidReply P q r
  complete : ∀ q, Legal P q → ∃ r, O q = some r

theorem first_root_unique {F : ℝ → ℝ} {a b t r s : ℝ}
    (hr : FirstRoot F a b t r) (hs : FirstRoot F a b t s) : r = s :=
  le_antisymm (hr.first s hs.location hs.equation)
    (hs.first r hr.location hr.equation)

/-- Every legal signed bracket has a least root. -/
theorem exists_first_root {F : ℝ → ℝ} (hF : Continuous F)
    {a b t : ℝ} (hab : a ≤ b) (ht : LegalTarget F a b t) :
    ∃ r, FirstRoot F a b t r := by
  have hroot : ∃ r ∈ Icc a b, F r = F a + t := by
    by_cases horder : F a ≤ F b
    · have hB : 0 ≤ F b - F a := sub_nonneg.mpr horder
      have htarget : F a + t ∈ Icc (F a) (F b) := by
        simp only [LegalTarget, min_eq_left hB, max_eq_right hB] at ht
        constructor <;> linarith [ht.1, ht.2]
      exact intermediate_value_Icc hab hF.continuousOn htarget
    · have hB : F b - F a ≤ 0 := sub_nonpos.mpr (le_of_not_ge horder)
      have htarget : F a + t ∈ Icc (F b) (F a) := by
        simp only [LegalTarget, min_eq_right hB, max_eq_left hB] at ht
        constructor <;> linarith [ht.1, ht.2]
      exact intermediate_value_Icc' hab hF.continuousOn htarget
  let roots := Icc a b ∩ {x | F x = F a + t}
  have hcompact : IsCompact roots :=
    isCompact_Icc.inter_right (isClosed_eq hF continuous_const)
  have hnonempty : roots.Nonempty := by
    obtain ⟨r, hr, heq⟩ := hroot
    exact ⟨r, hr, heq⟩
  obtain ⟨r, hr, hmin⟩ := hcompact.exists_isMinOn hnonempty
    (continuousOn_id : ContinuousOn (fun x : ℝ => x) roots)
  refine ⟨r, hr.1, hr.2, ?_⟩
  intro x hx heq
  exact hmin ⟨hx, heq⟩

noncomputable def firstCut (P : Profile Agent) (i : Agent) (a b t : ℝ) : ℝ := by
  classical
  exact if h : a ≤ b ∧ LegalTarget (P.cumulative i) a b t then
    Classical.choose (exists_first_root (P.continuous i) h.1 h.2)
  else a

theorem firstCut_spec (P : Profile Agent) (i : Agent) (a b t : ℝ)
    (hab : a ≤ b) (ht : LegalTarget (P.cumulative i) a b t) :
    FirstRoot (P.cumulative i) a b t (firstCut P i a b t) := by
  classical
  unfold firstCut
  rw [dite_eq_left ⟨hab, ht⟩]
  exact Classical.choose_spec (exists_first_root (P.continuous i) hab ht)

noncomputable def oracle (P : Profile Agent) (q : Query Agent) : Option ℝ := by
  classical
  exact if Legal P q then
    some (match q with
      | .eval i a b => P.cumulative i b - P.cumulative i a
      | .cut i a b t => firstCut P i a b t)
  else none

theorem oracle_none_iff (P : Profile Agent) (q : Query Agent) :
    oracle P q = none ↔ ¬ Legal P q := by
  classical
  unfold oracle
  split_ifs <;> simp_all

theorem oracle_some_valid (P : Profile Agent) (q : Query Agent) (r : ℝ)
    (h : oracle P q = some r) : Legal P q ∧ ValidReply P q r := by
  classical
  have hlegal : Legal P q := by
    by_contra hn
    have := (oracle_none_iff P q).mpr hn
    rw [h] at this
    contradiction
  refine ⟨hlegal, ?_⟩
  cases q with
  | eval i a b =>
    simpa [oracle, hlegal, ValidReply] using h.symm
  | cut i a b t =>
    have heq : firstCut P i a b t = r := by
      simpa [oracle, hlegal] using h
    obtain ⟨ha, hab, hb, ht⟩ := hlegal
    rw [← heq]
    exact ⟨(firstCut_spec P i a b t hab ht).location,
      (firstCut_spec P i a b t hab ht).equation⟩

theorem oracle_cut_first (P : Profile Agent) (i : Agent) (a b t r : ℝ)
    (h : oracle P (.cut i a b t) = some r) :
    FirstRoot (P.cumulative i) a b t r := by
  classical
  have hlegal := (oracle_some_valid P (.cut i a b t) r h).1
  have heq : firstCut P i a b t = r := by
    simpa [oracle, hlegal] using h
  rw [← heq]
  exact firstCut_spec P i a b t hlegal.2.1 hlegal.2.2.2

theorem oracle_isLegal (P : Profile Agent) : IsLegalOracle P (oracle P) := by
  classical
  refine ⟨oracle_some_valid P, ?_⟩
  intro q hq
  simp only [oracle, ite_eq_left hq]
  exact ⟨_, rfl⟩

/-- Agreement at both bracket endpoints preserves legality, including a
terminal illegal target. Geometry is unchanged because it is part of the query. -/
theorem legal_iff_of_endpoint_eq (P P' : Profile Agent) (q : Query Agent)
    (ha : P'.cumulative q.agent q.left = P.cumulative q.agent q.left)
    (hb : P'.cumulative q.agent q.right = P.cumulative q.agent q.right) :
    Legal P' q ↔ Legal P q := by
  cases q with
  | eval i a b => rfl
  | cut i a b t =>
    change P'.cumulative i a = P.cumulative i a at ha
    change P'.cumulative i b = P.cumulative i b at hb
    simp only [Legal, LegalTarget, ha, hb]

end EnvyFreeResearch.Full.IntervalOracle
