import EnvyFreeResearch.Full.NonnegativeMeasurableOracle
import EnvyFreeResearch.Full.NonnegativeMeasurablePulse
import EnvyFreeResearch.Full.NonnegativeFailure

namespace EnvyFreeResearch.Full.NonnegativeExperiment

open MeasureTheory Set IntervalOracle IntervalAllocation MixedDensity
open NonnegativeOracle NonnegativeProfile NonnegativeShift NonnegativeFailure
open NonnegativeMeasurableOracle NonnegativeMeasurablePulse NonnegativeRandomOutput
open ProtocolMeasurable OracleProtocol
open scoped Classical

abbrev Circle := NonnegativeCircle.Circle
abbrev Input (n : ℕ) := Fin n × (ℝ × Circle)

noncomputable def inputRows {n : ℕ} (h : ℝ) (z : Input n) : Fin n → Row :=
  perturbedRows z.1 h (first z.2) (second z.2)

noncomputable def inputProfile {n : ℕ} (h : ℝ) (z : Input n) : Profile (Fin n) :=
  perturbed z.1 h (first z.2) (second z.2)

theorem uniform_positive {Agent : Type*} : StrictlyPositive (uniform (Agent := Agent)) := by
  intro i a ha b hb hab
  simpa only [uniform, toProfile, uniform_cumulative a ha, uniform_cumulative b hb] using hab

theorem uniformOracle_measurable {n : ℕ} :
    Measurable (IntervalOracle.oracle (uniform (Agent := Fin n))) := by
  have hF (i : Fin n) : Measurable (fun z : Unit × ℝ =>
      (uniform (Agent := Fin n)).cumulative i z.2) :=
    uniformRow.cumulative_continuous.measurable.comp measurable_snd
  exact (NonnegativeMeasurableOracle.measurable_oracle (fun (_ : Unit) => uniform)
    (fun _ => uniform_positive) hF).comp ((measurable_const (a := ())).prodMk measurable_id)

theorem uniformFlagged_measurable {n : ℕ} (flag : Bool) :
    Measurable (flaggedOracle flag (uniform (Agent := Fin n))) := by
  have hF (i : Fin n) : Measurable (fun z : Unit × ℝ =>
      (uniform (Agent := Fin n)).cumulative i z.2) :=
    uniformRow.cumulative_continuous.measurable.comp measurable_snd
  exact (measurable_flaggedOracle flag (fun (_ : Unit) => uniform)
    (fun _ => uniform_positive) hF).comp ((measurable_const (a := ())).prodMk measurable_id)

theorem inputProfile_positive {n : ℕ} (h : ℝ) (z : Input n) :
    StrictlyPositive (inputProfile h z) := perturbed_strictlyPositive _ _ _ _

theorem inputProfile_cumulative_measurable {n : ℕ} (h : ℝ) (i : Fin n) :
    Measurable (fun z : Input n × ℝ => (inputProfile h z.1).cumulative i z.2) := by
  have hcenter : Measurable (fun z : Input n × ℝ =>
      ((first z.1.2, second z.1.2), z.2)) :=
    ((measurable_first.comp (measurable_snd.comp measurable_fst)).prodMk
      (measurable_second.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  have hpulse := (rowCumulative_joint h).comp hcenter
  have huniform : Measurable (fun z : Input n × ℝ => uniformRow.cumulative z.2) :=
    uniformRow.cumulative_continuous.measurable.comp measurable_snd
  have hsame : MeasurableSet {z : Input n × ℝ | i = z.1.1} :=
    measurableSet_eq_fun measurable_const (measurable_fst.comp measurable_fst)
  have heq : (fun z : Input n × ℝ => (inputProfile h z.1).cumulative i z.2) =
      (fun z => if i = z.1.1 then
        (NonnegativePulse.row h (first z.1.2) (second z.1.2)).cumulative z.2
        else uniformRow.cumulative z.2) := by
    funext z
    by_cases hi : i = z.1.1 <;> simp [inputProfile, perturbed, toProfile, perturbedRows, hi]
  rw [heq]
  exact hpulse.ite hsame huniform

noncomputable def inputOracle {n : ℕ} (flag : Bool) (h : ℝ) (z : Input n) :
    Query (Fin n) → Option Reply := flaggedOracle flag (inputProfile h z)

/-- The actual perturbation family has a jointly measurable physical oracle;
the parameter is the same observer/real-shift/Haar point used in detection. -/
theorem inputOracle_measurable {n : ℕ} (flag : Bool) (h : ℝ) :
    Measurable (fun z : Input n × Query (Fin n) => inputOracle flag h z.1 z.2) :=
  measurable_flaggedOracle flag (inputProfile h) (inputProfile_positive h)
    (inputProfile_cumulative_measurable h)

theorem inputShareValue_measurable {n : ℕ} (h : ℝ) (i j : Fin n) :
    Measurable (fun z : Input n × Allocation (Fin n) =>
      (inputRows h z.1 i).signedMeasure (z.2.share j)) := by
  have hcenter : Measurable (fun z : Input n × Allocation (Fin n) =>
      ((first z.1.2, second z.1.2), z.2)) :=
    ((measurable_first.comp (measurable_snd.comp measurable_fst)).prodMk
      (measurable_second.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  have hpulse := (shareValue_joint h j).comp hcenter
  have huniform : Measurable (fun z : Input n × Allocation (Fin n) =>
      volume.real (z.2.share j)) := (measurable_share_length j).comp measurable_snd
  have hsame : MeasurableSet {z : Input n × Allocation (Fin n) | i = z.1.1} :=
    measurableSet_eq_fun measurable_const (measurable_fst.comp measurable_fst)
  have heq : (fun z : Input n × Allocation (Fin n) =>
      (inputRows h z.1 i).signedMeasure (z.2.share j)) =
      (fun z => if i = z.1.1 then
        (NonnegativePulse.row h (first z.1.2) (second z.1.2)).signedMeasure (z.2.share j)
        else volume.real (z.2.share j)) := by
    funext z
    by_cases hi : i = z.1.1 <;>
      simp [inputRows, perturbedRows, hi, uniform_share_value]
  rw [heq]
  exact hpulse.ite hsame huniform

theorem inputCakeEF_measurable {n : ℕ} (h : ℝ) :
    MeasurableSet {z : Input n × Allocation (Fin n) | CakeEF (inputRows h z.1) z.2} := by
  have heq : {z : Input n × Allocation (Fin n) | CakeEF (inputRows h z.1) z.2} =
      ⋂ i, ⋂ j, {z | (inputRows h z.1 i).signedMeasure (z.2.share j) ≤
        (inputRows h z.1 i).signedMeasure (z.2.share i)} := by
    ext z
    simp [CakeEF]
  rw [heq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_le (inputShareValue_measurable h i j) (inputShareValue_measurable h i i)

theorem inputChoreEF_measurable {n : ℕ} (h : ℝ) :
    MeasurableSet {z : Input n × Allocation (Fin n) | ChoreEF (inputRows h z.1) z.2} := by
  have heq : {z : Input n × Allocation (Fin n) | ChoreEF (inputRows h z.1) z.2} =
      ⋂ i, ⋂ j, {z | (inputRows h z.1 i).signedMeasure (z.2.share i) ≤
        (inputRows h z.1 i).signedMeasure (z.2.share j)} := by
    ext z
    simp [ChoreEF]
  rw [heq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_le (inputShareValue_measurable h i i) (inputShareValue_measurable h i j)

theorem inputRun_measurable {n : ℕ} {Tape : Type*} [MeasurableSpace Tape]
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (hnext : Measurable (fun z : Tape × History (Query (Fin n)) Reply => next z.1 z.2))
    (flag : Bool) (h : ℝ) (fuel : ℕ) :
    Measurable (fun z : Input n × Tape => run next (inputOracle flag h z.1) z.2 fuel []) :=
  measurable_run_parameterized_at_history next (inputOracle flag h) hnext
    (inputOracle_measurable flag h) fuel []

end EnvyFreeResearch.Full.NonnegativeExperiment

#print axioms EnvyFreeResearch.Full.NonnegativeExperiment.inputOracle_measurable
#print axioms EnvyFreeResearch.Full.NonnegativeExperiment.inputCakeEF_measurable
#print axioms EnvyFreeResearch.Full.NonnegativeExperiment.inputRun_measurable
