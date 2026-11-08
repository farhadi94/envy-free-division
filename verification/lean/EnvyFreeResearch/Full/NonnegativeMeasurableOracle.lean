import EnvyFreeResearch.Full.NonnegativeOracle
import EnvyFreeResearch.Full.ProtocolMeasurable

namespace EnvyFreeResearch.Full.NonnegativeMeasurableOracle

open Set MeasureTheory IntervalOracle NonnegativeOracle
open ProtocolMeasurable TranscriptAdversary ExtremalRoots
open scoped Classical

variable {Parameter Agent : Type*} [MeasurableSpace Parameter]

abbrev CutParameters := ℝ × ℝ × ℝ

def cutLegal (P : Parameter → Profile Agent) (i : Agent)
    (z : Parameter × CutParameters) : Prop :=
  0 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2.1 ∧ z.2.2.1 ≤ 1 ∧
    LegalTarget ((P z.1).cumulative i) z.2.1 z.2.2.1 z.2.2.2

noncomputable def boundedCut (P : Parameter → Profile Agent) (i : Agent)
    (z : Parameter × CutParameters) : ℝ :=
  if cutLegal P i z then firstCut (P z.1) i z.2.1 z.2.2.1 z.2.2.2 else 0

/-- Strict positivity gives an explicit sublevel test for the actual Cut
root. This proves parameter measurability without assuming a selector. -/
theorem firstCut_lt_iff (P : Profile Agent) (hP : StrictlyPositive P) (i : Agent)
    (a b t z : ℝ) (hlegal : Legal P (.cut i a b t)) :
    firstCut P i a b t < z ↔ b < z ∨
      (a < z ∧ z ≤ b ∧ t < P.cumulative i z - P.cumulative i a) := by
  have hr := firstCut_spec P i a b t hlegal.2.1 hlegal.2.2.2
  have hrunit : firstCut P i a b t ∈ Icc (0 : ℝ) 1 :=
    ⟨hlegal.1.trans hr.location.1, hr.location.2.trans hlegal.2.2.1⟩
  constructor
  · intro hrz
    by_cases hbz : b < z
    · exact Or.inl hbz
    · have hzb := le_of_not_gt hbz
      have haz := hr.location.1.trans_lt hrz
      have hzunit : z ∈ Icc (0 : ℝ) 1 := ⟨hlegal.1.trans haz.le, hzb.trans hlegal.2.2.1⟩
      have hF := hP i hrunit hzunit hrz
      rw [hr.equation] at hF
      exact Or.inr ⟨haz, hzb, by linarith⟩
  · rintro (hbz | ⟨haz, hzb, ht⟩)
    · exact hr.location.2.trans_lt hbz
    · have hzunit : z ∈ Icc (0 : ℝ) 1 := ⟨hlegal.1.trans haz.le, hzb.trans hlegal.2.2.1⟩
      by_contra hn
      have hF := (hP i).monotoneOn hzunit hrunit (le_of_not_gt hn)
      rw [hr.equation] at hF
      linarith

theorem measurable_cutLegal (P : Parameter → Profile Agent) (i : Agent)
    (hF : Measurable (fun z : Parameter × ℝ => (P z.1).cumulative i z.2)) :
    MeasurableSet {z | cutLegal P i z} := by
  have ha : Measurable (fun z : Parameter × CutParameters => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hb : Measurable (fun z : Parameter × CutParameters => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have ht : Measurable (fun z : Parameter × CutParameters => z.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hFa := hF.comp (measurable_fst.prodMk ha)
  have hFb := hF.comp (measurable_fst.prodMk hb)
  exact (measurableSet_le measurable_const ha).inter
    ((measurableSet_le ha hb).inter ((measurableSet_le hb measurable_const).inter
      ((measurableSet_le (measurable_const.min (hFb.sub hFa)) ht).inter
        (measurableSet_le ht (measurable_const.max (hFb.sub hFa))))))

theorem measurable_boundedCut (P : Parameter → Profile Agent)
    (hP : ∀ p, StrictlyPositive (P p)) (i : Agent)
    (hF : Measurable (fun z : Parameter × ℝ => (P z.1).cumulative i z.2)) :
    Measurable (boundedCut P i) := by
  apply measurable_of_Iio
  intro x
  have heq : boundedCut P i ⁻¹' Iio x =
      ({z | ¬ cutLegal P i z} ∩ {z : Parameter × CutParameters | 0 < x}) ∪
      ({z | cutLegal P i z} ∩
        ({z | z.2.2.1 < x} ∪ ({z | z.2.1 < x} ∩ {z | x ≤ z.2.2.1} ∩
          {z | z.2.2.2 < (P z.1).cumulative i x - (P z.1).cumulative i z.2.1}))) := by
    ext z
    by_cases hz : cutLegal P i z
    · have hc : Legal (P z.1) (.cut i z.2.1 z.2.2.1 z.2.2.2) := hz
      simp only [mem_preimage, mem_Iio, boundedCut, mem_union,
        mem_inter_iff, mem_ofPred_eq, hz, ite_true, not_true_eq_false, false_and, true_and,
        false_or, firstCut_lt_iff _ (hP z.1) _ _ _ _ _ hc]
      tauto
    · simp [boundedCut, hz]
  rw [heq]
  have ha : Measurable (fun z : Parameter × CutParameters => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hb : Measurable (fun z : Parameter × CutParameters => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have ht : Measurable (fun z : Parameter × CutParameters => z.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hFa := hF.comp (measurable_fst.prodMk ha)
  have hparamX : Measurable (fun z : Parameter × CutParameters => (z.1, x)) :=
    measurable_fst.prodMk measurable_const
  have hFx := hF.comp hparamX
  have hlegal := measurable_cutLegal P i hF
  exact (hlegal.compl.inter (by by_cases h : 0 < x <;> simp [h])).union
    (hlegal.inter ((measurableSet_lt hb measurable_const).union
      (((measurableSet_lt ha measurable_const).inter
        (measurableSet_le measurable_const hb)).inter (measurableSet_lt ht (hFx.sub hFa)))))

theorem measurable_cutOracle (P : Parameter → Profile Agent)
    (hP : ∀ p, StrictlyPositive (P p)) (i : Agent)
    (hF : Measurable (fun z : Parameter × ℝ => (P z.1).cumulative i z.2)) :
    Measurable (fun z : Parameter × CutParameters =>
      IntervalOracle.oracle (P z.1) (.cut i z.2.1 z.2.2.1 z.2.2.2)) := by
  have heq : (fun z : Parameter × CutParameters =>
      IntervalOracle.oracle (P z.1) (.cut i z.2.1 z.2.2.1 z.2.2.2)) =
      (fun z => if cutLegal P i z then some (boundedCut P i z) else none) := by
    funext z
    by_cases hz : cutLegal P i z
    · have hc : Legal (P z.1) (.cut i z.2.1 z.2.2.1 z.2.2.2) := hz
      simp [IntervalOracle.oracle, hc, boundedCut, hz]
    · have hc : ¬ Legal (P z.1) (.cut i z.2.1 z.2.2.1 z.2.2.2) := hz
      simp [IntervalOracle.oracle, hc, hz]
  rw [heq]
  exact (measurable_some.comp (measurable_boundedCut P hP i hF)).ite
    (measurable_cutLegal P i hF) measurable_const

theorem measurable_evalOracle (P : Parameter → Profile Agent) (i : Agent)
    (hF : Measurable (fun z : Parameter × ℝ => (P z.1).cumulative i z.2)) :
    Measurable (fun z : Parameter × (ℝ × ℝ) =>
      IntervalOracle.oracle (P z.1) (.eval i z.2.1 z.2.2)) := by
  have ha : Measurable (fun z : Parameter × (ℝ × ℝ) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hb : Measurable (fun z : Parameter × (ℝ × ℝ) => z.2.2) :=
    measurable_snd.comp measurable_snd
  have hFa := hF.comp (measurable_fst.prodMk ha)
  have hFb := hF.comp (measurable_fst.prodMk hb)
  exact (measurable_some.comp (hFb.sub hFa)).ite
    ((measurableSet_le measurable_const ha).inter
      ((measurableSet_le ha hb).inter (measurableSet_le hb measurable_const))) measurable_const

theorem measurable_oracle [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    [Countable Agent] (P : Parameter → Profile Agent)
    (hP : ∀ p, StrictlyPositive (P p))
    (hF : ∀ i, Measurable (fun z : Parameter × ℝ => (P z.1).cumulative i z.2)) :
    Measurable (fun z : Parameter × Query Agent => IntervalOracle.oracle (P z.1) z.2) := by
  have heval : Measurable (fun z : Parameter × (Agent × ℝ × ℝ) =>
      IntervalOracle.oracle (P z.1) (.eval z.2.1 z.2.2.1 z.2.2.2)) := by
    have hfixed : Measurable (fun z : (Parameter × (ℝ × ℝ)) × Agent =>
        IntervalOracle.oracle (P z.1.1) (.eval z.2 z.1.2.1 z.1.2.2)) :=
      measurable_from_prod_countable_left fun i => measurable_evalOracle P i (hF i)
    have hmap : Measurable (fun z : Parameter × (Agent × ℝ × ℝ) =>
        ((z.1, z.2.2), z.2.1)) :=
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp measurable_snd)
    exact hfixed.comp hmap
  have hcut : Measurable (fun z : Parameter × (Agent × ℝ × ℝ × ℝ) =>
      IntervalOracle.oracle (P z.1) (.cut z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)) := by
    have hfixed : Measurable (fun z : (Parameter × CutParameters) × Agent =>
        IntervalOracle.oracle (P z.1.1) (.cut z.2 z.1.2.1 z.1.2.2.1 z.1.2.2.2)) :=
      measurable_from_prod_countable_left fun i => measurable_cutOracle P hP i (hF i)
    have hmap : Measurable (fun z : Parameter × (Agent × ℝ × ℝ × ℝ) =>
        ((z.1, z.2.2), z.2.1)) :=
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp measurable_snd)
    exact hfixed.comp hmap
  have hsum := measurable_prod_sum_cases
    (left := fun p (q : Agent × ℝ × ℝ) =>
      IntervalOracle.oracle (P p) (.eval q.1 q.2.1 q.2.2))
    (right := fun p (q : Agent × ℝ × ℝ × ℝ) =>
      IntervalOracle.oracle (P p) (.cut q.1 q.2.1 q.2.2.1 q.2.2.2)) heval hcut
  have hmap : Measurable (fun z : Parameter × Query Agent => (z.1, queryCode z.2)) :=
    measurable_fst.prodMk (measurable_queryCode.comp measurable_snd)
  convert hsum.comp hmap using 1
  funext z
  rcases z with ⟨p, q⟩
  cases q <;> rfl

def replyCode : Reply → ℝ ⊕ Unit
  | .value r => .inl r
  | .unavailable => .inr ()

instance replyMeasurableSpace : MeasurableSpace Reply :=
  MeasurableSpace.comap replyCode inferInstance

theorem measurable_reply_value : Measurable Reply.value :=
  measurable_comap_iff.mpr measurable_inl

theorem measurable_query_left [MeasurableSpace Agent] :
    Measurable (Query.left (Agent := Agent)) := by
  apply measurable_query_cases
  · exact measurable_fst.comp measurable_snd
  · exact measurable_fst.comp measurable_snd

theorem measurable_query_right [MeasurableSpace Agent] :
    Measurable (Query.right (Agent := Agent)) := by
  apply measurable_query_cases
  · exact measurable_snd.comp measurable_snd
  · exact measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_syntax [MeasurableSpace Agent] : MeasurableSet {q : Query Agent | Syntax q} :=
  (measurableSet_le measurable_const measurable_query_left).inter
    ((measurableSet_le measurable_query_left measurable_query_right).inter
      (measurableSet_le measurable_query_right measurable_const))

/-- Both legal-target conventions produce standard measurable actual replies.
The unavailable flag remains an answered call in the protocol executor. -/
theorem measurable_flaggedOracle [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    [Countable Agent] (flag : Bool) (P : Parameter → Profile Agent)
    (hP : ∀ p, StrictlyPositive (P p))
    (hF : ∀ i, Measurable (fun z : Parameter × ℝ => (P z.1).cumulative i z.2)) :
    Measurable (fun z : Parameter × Query Agent => flaggedOracle flag (P z.1) z.2) := by
  have hbody : Measurable (fun z : Parameter × Query Agent =>
      match IntervalOracle.oracle (P z.1) z.2 with
      | some r => some (Reply.value r)
      | none => if flag then some Reply.unavailable else none) := by
    convert measurable_option_cases
      (present := fun (_ : Parameter × Query Agent) r => some (Reply.value r))
      (absent := fun (_ : Parameter × Query Agent) => if flag then some Reply.unavailable else none)
      (measurable_oracle P hP hF)
      (measurable_some.comp (measurable_reply_value.comp measurable_snd)) measurable_const using 1
    funext z
    cases IntervalOracle.oracle (P z.1) z.2 <;> rfl
  have hsyntax : MeasurableSet {z : Parameter × Query Agent | Syntax z.2} :=
    measurable_syntax.preimage measurable_snd
  exact hbody.ite hsyntax measurable_const

end EnvyFreeResearch.Full.NonnegativeMeasurableOracle

#print axioms EnvyFreeResearch.Full.NonnegativeMeasurableOracle.measurable_cutOracle
#print axioms EnvyFreeResearch.Full.NonnegativeMeasurableOracle.measurable_flaggedOracle
