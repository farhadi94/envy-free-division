import EnvyFreeResearch.Full.IntervalOracle

/-!
# Positive-density oracle replay, including counted unavailable-target flags

A successful Cut is determined by just the interval from its left endpoint
to its returned root. Its bracket total is not imposed as a second equality.
Unavailable targets use the full bracket, regardless of whether the syntax
returns a counted flag or stops with an uncounted illegal request.
-/

namespace EnvyFreeResearch.Full.NonnegativeOracle

open Set IntervalOracle OracleProtocol TranscriptAdversary ExtremalRoots

variable {Agent : Type*}

def Syntax (q : Query Agent) : Prop :=
  0 ≤ q.left ∧ q.left ≤ q.right ∧ q.right ≤ 1

def StrictlyPositive (P : Profile Agent) : Prop :=
  ∀ i, StrictMonoOn (P.cumulative i) (Icc (0 : ℝ) 1)

inductive Reply
  | value (r : ℝ)
  | unavailable

/-- `flag = true` returns an answered unavailable-target flag; `false` makes
that request terminal and uncounted. Malformed brackets are always terminal. -/
noncomputable def flaggedOracle (flag : Bool) (P : Profile Agent) (q : Query Agent) : Option Reply := by
  classical
  exact if Syntax q then
    match IntervalOracle.oracle P q with
    | some r => some (.value r)
    | none => if flag then some .unavailable else none
  else none

/-- The right endpoint of the sole determining interval for this request. -/
noncomputable def determiningRight (P : Profile Agent) (q : Query Agent) : ℝ :=
  match q, IntervalOracle.oracle P q with
  | .cut _ _ _ _, some r => r
  | _, _ => q.right

def Determined (P P' : Profile Agent) (q : Query Agent) : Prop :=
  Syntax q →
    P'.cumulative q.agent (determiningRight P q) - P'.cumulative q.agent q.left =
      P.cumulative q.agent (determiningRight P q) - P.cumulative q.agent q.left

theorem cut_reply_preserved (P P' : Profile Agent) (hpositive : StrictlyPositive P')
    (i : Agent) (a b target r : ℝ)
    (hbefore : IntervalOracle.oracle P (.cut i a b target) = some r)
    (hincrement : P'.cumulative i r - P'.cumulative i a =
      P.cumulative i r - P.cumulative i a) :
    IntervalOracle.oracle P' (.cut i a b target) = some r := by
  have hlegal := (oracle_some_valid P (.cut i a b target) r hbefore).1
  have hroot := (oracle_some_valid P (.cut i a b target) r hbefore).2
  rcases hlegal with ⟨ha, hab, hb, _⟩
  rcases hroot with ⟨hr, heq⟩
  have haunit : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbunit : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have hrunit : r ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hr.1, hr.2.trans hb⟩
  have heq' : P'.cumulative i r = P'.cumulative i a + target := by linarith
  have hmono := (hpositive i).monotoneOn
  have har := hmono haunit hrunit hr.1
  have hrb := hmono hrunit hbunit hr.2
  have hab' := hmono haunit hbunit hab
  have htarget : LegalTarget (P'.cumulative i) a b target := by
    unfold LegalTarget
    rw [min_eq_left (sub_nonneg.mpr hab'), max_eq_right (sub_nonneg.mpr hab')]
    constructor <;> linarith
  have hlegal' : Legal P' (.cut i a b target) := ⟨ha, hab, hb, htarget⟩
  have hfirst : FirstRoot (P'.cumulative i) a b target r := by
    refine ⟨hr, heq', ?_⟩
    intro x hx hxeq
    have hxunit : x ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans hb⟩
    have hsame : r = x := (hpositive i).injOn hrunit hxunit (by linarith)
    exact hsame.le
  have hcut : firstCut P' i a b target = r :=
    first_root_unique (firstCut_spec P' i a b target hab htarget) hfirst
  simp [IntervalOracle.oracle, hlegal', hcut]

/-- Preserving the one selected determining interval preserves the concrete
positive oracle reply, including terminal illegality. -/
theorem oracle_eq_of_determined (P P' : Profile Agent) (hpositive : StrictlyPositive P')
    (q : Query Agent) (hdet : Determined P P' q) :
    IntervalOracle.oracle P' q = IntervalOracle.oracle P q := by
  classical
  by_cases hs : Syntax q
  · cases q with
    | eval i a b =>
      have hlegal : Legal P (.eval i a b) := hs
      have hlegal' : Legal P' (.eval i a b) := hs
      have hd := hdet hs
      simp only [determiningRight, Query.agent, Query.left, Query.right] at hd
      simpa [IntervalOracle.oracle, hlegal, hlegal'] using congrArg some hd
    | cut i a b target =>
      cases ho : IntervalOracle.oracle P (.cut i a b target) with
      | some r =>
        have hd := hdet hs
        simp only [determiningRight, ho, Query.agent, Query.left] at hd
        exact cut_reply_preserved P P' hpositive i a b target r ho hd
      | none =>
        have hd := hdet hs
        simp only [determiningRight, ho, Query.agent, Query.left, Query.right] at hd
        apply (oracle_none_iff P' _).mpr
        intro hlegal'
        have hlegal : Legal P (.cut i a b target) := by
          rcases hlegal' with ⟨ha, hab, hb, ht⟩
          refine ⟨ha, hab, hb, ?_⟩
          simpa only [LegalTarget, hd] using ht
        exact (oracle_none_iff P _).mp ho hlegal
  · have hnone (R : Profile Agent) : IntervalOracle.oracle R q = none := by
      apply (oracle_none_iff R q).mpr
      cases q <;> simp_all [Legal, Syntax, Query.left, Query.right]
    rw [hnone P, hnone P']

theorem flaggedOracle_eq_of_determined (flag : Bool) (P P' : Profile Agent)
    (hpositive : StrictlyPositive P') (q : Query Agent) (hdet : Determined P P' q) :
    flaggedOracle flag P' q = flaggedOracle flag P q := by
  classical
  simp only [flaggedOracle, oracle_eq_of_determined P P' hpositive q hdet]

/-- Concrete all-outcome adaptive replay for either unavailable-target
accounting convention, from one determining interval per actually issued
request. The baseline full tape is fixed throughout the induction. -/
theorem flagged_run_replay {Tape Output : Type*}
    (next : Protocol Tape (Query Agent) Reply Output) (flag : Bool)
    (P P' : Profile Agent) (hpositive : StrictlyPositive P')
    (tape : Tape) (fuel : ℕ) (history : History (Query Agent) Reply)
    (hpreserve : ∀ q,
      (∃ reply, (q, reply) ∈ (run next (flaggedOracle flag P) tape fuel history).answered) ∨
      (run next (flaggedOracle flag P) tape fuel history).stop = .illegal q →
      Determined P P' q) :
    run next (flaggedOracle flag P') tape fuel history =
      run next (flaggedOracle flag P) tape fuel history := by
  apply replay_of_oracle_eq
  intro q hq
  exact flaggedOracle_eq_of_determined flag P P' hpositive q (hpreserve q hq)

end EnvyFreeResearch.Full.NonnegativeOracle

#print axioms EnvyFreeResearch.Full.NonnegativeOracle.cut_reply_preserved
#print axioms EnvyFreeResearch.Full.NonnegativeOracle.oracle_eq_of_determined
#print axioms EnvyFreeResearch.Full.NonnegativeOracle.flagged_run_replay
