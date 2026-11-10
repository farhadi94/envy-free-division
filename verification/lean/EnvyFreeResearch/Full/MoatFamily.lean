import EnvyFreeResearch.Full.MoatMeasurable
import EnvyFreeResearch.Full.MoatDecoder

/-! One concrete family covers one or two perturbed rows. Inputs are finite
sets of changed observers and a circle center. Every row belongs to the
existing public finite-step class, and the ordinary oracle is jointly Borel. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatFamily
open Set MeasureTheory MixedDensity IntervalOracle IntervalAllocation OracleProtocol
open NonnegativeOracle NonnegativeProfile NonnegativeFailure NonnegativeRandomOutput
open MoatDensity MoatPhysical MoatMeasurable NonnegativeRetainedFailure
open scoped Classical
abbrev Circle := NonnegativeCircle.Circle
abbrev Input (n : ℕ) := Finset (Fin n) × Circle

def rows {n : ℕ} (chores : Bool) (w h : ℝ) (input : Input n) (i : Fin n) : Row :=
  if i ∈ input.1 then row chores w h input.2 else uniformRow

def profile {n : ℕ} (chores : Bool) (w h : ℝ) (input : Input n) : Profile (Fin n) :=
  toProfile (rows chores w h input)

theorem admissible {n : ℕ} (chores : Bool) {w h : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 ≤ h) (hhw : h ≤ w) (input : Input n) :
    NonnegativeInputClass.Admissible (rows chores w h input) := by
  intro i
  by_cases hi : i ∈ input.1
  · simpa only [rows, ite_eq_left hi] using row_admissible chores hw hw1 hh hhw input.2
  · simpa only [rows, ite_eq_right hi] using NonnegativeInputClass.uniform_admissible

theorem positive {n : ℕ} (chores : Bool) {w h : ℝ} (hw : 0 < w)
    (hh : 0 ≤ h) (hhw : h ≤ w) (input : Input n) : StrictlyPositive (profile chores w h input) := by
  intro i
  by_cases hi : i ∈ input.1
  · simpa only [profile, toProfile, rows, ite_eq_left hi] using row_strictMonoOn chores hw hh hhw input.2
  · intro a ha b hb hab
    simpa only [profile, toProfile, rows, ite_eq_right hi, uniform_cumulative a ha, uniform_cumulative b hb] using hab

theorem cumulative_measurable {n : ℕ} (chores : Bool) (w h : ℝ) (i : Fin n) :
    Measurable (fun z : Input n × ℝ => (profile chores w h z.1).cumulative i z.2) := by
  classical
  have hcenter : Measurable (fun z : Input n × ℝ => (z.1.2,z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hpulse := (rowCumulative_joint chores w h).comp hcenter
  have huniform := uniformRow.cumulative_continuous.measurable.comp
    (measurable_snd : Measurable (Prod.snd : Input n × ℝ → ℝ))
  have hselected : MeasurableSet {z : Input n × ℝ | i ∈ z.1.1} :=
    (measurableSet_mem_finset i).preimage (measurable_fst.comp measurable_fst)
  have heq : (fun z : Input n × ℝ => (profile chores w h z.1).cumulative i z.2) =
      (fun z => if i ∈ z.1.1 then (row chores w h z.1.2).cumulative z.2 else uniformRow.cumulative z.2) := by
    funext z
    by_cases hi : i ∈ z.1.1 <;> simp [profile, toProfile, rows, hi]
  rw [heq]
  exact hpulse.ite hselected huniform

def oracle {n : ℕ} (flag chores : Bool) (w h : ℝ) (input : Input n) :
    Query (Fin n) → Option Reply := flaggedOracle flag (profile chores w h input)

theorem oracle_measurable {n : ℕ} (flag chores : Bool) {w h : ℝ} (hw : 0 < w)
    (hh : 0 ≤ h) (hhw : h ≤ w) :
    Measurable (fun z : Input n × Query (Fin n) => oracle flag chores w h z.1 z.2) :=
  NonnegativeMeasurableOracle.measurable_flaggedOracle flag (profile chores w h)
    (positive chores hw hh hhw) (cumulative_measurable chores w h)

theorem share_value_measurable {n : ℕ} (chores : Bool) (w h : ℝ) (i j : Fin n) :
    Measurable (fun z : Input n × Allocation (Fin n) =>
      (rows chores w h z.1 i).signedMeasure (z.2.share j)) := by
  classical
  have hcenter : Measurable (fun z : Input n × Allocation (Fin n) => (z.1.2,z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hpulse := (shareValue_joint chores w h j).comp hcenter
  have huniform : Measurable (fun z : Input n × Allocation (Fin n) => volume.real (z.2.share j)) :=
    (NonnegativeRandomOutput.measurable_share_length j).comp measurable_snd
  have hselected : MeasurableSet {z : Input n × Allocation (Fin n) | i ∈ z.1.1} :=
    (measurableSet_mem_finset i).preimage (measurable_fst.comp measurable_fst)
  have heq : (fun z : Input n × Allocation (Fin n) =>
      (rows chores w h z.1 i).signedMeasure (z.2.share j)) =
      (fun z => if i ∈ z.1.1 then (row chores w h z.1.2).signedMeasure (z.2.share j)
        else volume.real (z.2.share j)) := by
    funext z
    by_cases hi : i ∈ z.1.1 <;> simp [rows, hi, uniform_share_value]
  rw [heq]
  exact hpulse.ite hselected huniform

theorem fair_measurable {n : ℕ} (chores : Bool) (w h : ℝ) :
    MeasurableSet {z : Input n × Allocation (Fin n) | Fair chores (rows chores w h z.1) z.2} := by
  cases chores
  · change MeasurableSet {z : Input n × Allocation (Fin n) |
      ∀ i j, (rows false w h z.1 i).signedMeasure (z.2.share j) ≤
        (rows false w h z.1 i).signedMeasure (z.2.share i)}
    simpa only [Set.setOf_forall] using (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le (share_value_measurable false w h i j) (share_value_measurable false w h i i))
  · change MeasurableSet {z : Input n × Allocation (Fin n) |
      ∀ i j, (rows true w h z.1 i).signedMeasure (z.2.share i) ≤
        (rows true w h z.1 i).signedMeasure (z.2.share j)}
    simpa only [Set.setOf_forall] using (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le (share_value_measurable true w h i i) (share_value_measurable true w h i j))

/-- Every old strict uniform failure survives, irrespective of how many
rows are simultaneously changed. -/
theorem old_failure {n : ℕ} [NeZero n] (chores : Bool) {w h : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1) (hh : 0 ≤ h) (hhw : h ≤ w)
    (input : Input n) (A : Allocation (Fin n)) (hgap : h < uniformGap A) :
    ¬ Fair chores (rows chores w h input) A := by
  have hchange (i j : Fin n) :
      |(rows chores w h input i).signedMeasure (A.share j)-volume.real (A.share j)| ≤ h/2 := by
    by_cases hi : i ∈ input.1
    · simpa only [rows, ite_eq_left hi] using MoatDecoder.bundle_change_abs_le chores hw hw1 hh hhw input.2
        (A.share j) (A.share_measurable j) (NonnegativeAllocation.share_subset A j)
    · simp only [rows, ite_eq_right hi, uniform_share_value, sub_self, abs_zero]
      linarith
  obtain ⟨i,j,hij⟩ := exists_gap_pair A h hgap
  intro hfair
  cases chores
  · have hf := hfair i j
    have hi := abs_le.mp (hchange i i)
    have hj := abs_le.mp (hchange i j)
    linarith
  · have hf := hfair j i
    have hi := abs_le.mp (hchange j i)
    have hj := abs_le.mp (hchange j j)
    linarith

end EnvyFreeResearch.Full.MoatFamily
