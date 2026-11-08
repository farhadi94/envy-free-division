import EnvyFreeResearch.Full.UpperAggregateInterpolationPhysical
import EnvyFreeResearch.Full.UpperAggregateInterpolationLoop

/-!
# The reached endpoint stream and the common bad-union event

Two finite slots represent each actually reached proposal. Stopped slots are
filled by the original outer boundary zero, whose interpolation error and
charge are proved zero. The first rejecting proposal's two slots remain.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperCorrectionExecution UpperCorrectionLoop UpperRecordedDomain
  UpperGridInterpolation UpperGridSensitivity

variable {n m : ℕ}

def loopPoint (policy : UpperCircularStage.Policy n) (jobs : Fin m → Job n) (initial : LoopState n)
    (tape : Fin m → Start) (slot : Fin m × Bool) : ℝ :=
  let state := reached (loopTransition policy jobs) initial tape slot.1
  if state.stopped then 0 else
    let r := descriptor policy state.current (jobs slot.1).owner (jobs slot.1).deficit (tape slot.1)
    if slot.2 then r.last else r.first

/-- This is exactly the charge accumulated along the actual transition
trace; zero-valued padding contributes no fictitious endpoint charge. -/
theorem sum_loopPoint_charge (policy : UpperCircularStage.Policy n) (jobs : Fin m → Job n)
    (u : ℝ → ℝ≥0∞) (hu0 : u 0 = 0) (initial : LoopState n) (tape : Fin m → Start) :
    (∑ slot : Fin m × Bool, u (loopPoint policy jobs initial tape slot)) =
      tapeTotal (loopTransition policy jobs) (fun i => proposalCharge policy (jobs i) u) initial tape := by
  rw [tapeTotal_eq_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool, loopPoint, Bool.true_eq, ↓reduceIte, proposalCharge]
  split_ifs <;> simp_all [add_comm]

/-- A descriptor is kept in the charged stream whenever its preceding state
is open; the acceptance result of that descriptor does not enter this test. -/
theorem reached_descriptor_in_stream (policy : UpperCircularStage.Policy n) (jobs : Fin m → Job n)
    (initial : LoopState n) (tape : Fin m → Start) (i : Fin m)
    (hopen : (reached (loopTransition policy jobs) initial tape i).stopped = false) :
    loopPoint policy jobs initial tape (i, false) =
      (descriptor policy (reached (loopTransition policy jobs) initial tape i).current
        (jobs i).owner (jobs i).deficit (tape i)).first ∧
    loopPoint policy jobs initial tape (i, true) =
      (descriptor policy (reached (loopTransition policy jobs) initial tape i).current
        (jobs i).owner (jobs i).deficit (tape i)).last := by
  simp [loopPoint, hopen]

def RecordedEndpoints {g : ℕ} {Generated : Type*} (cuts : Fin (g + 2) → ℝ)
    (points : Generated → ℝ) (pieces : List Component) : Prop :=
  ∀ c ∈ pieces,
    ((∃ p, cuts p = c.left) ∨ ∃ j, points j = c.left) ∧
    ((∃ p, cuts p = c.right) ∨ ∃ j, points j = c.right)

variable {Row Generated : Type*} [Fintype Row] [Nonempty Row] [Fintype Generated] {g : ℕ}

def BadRecordedUnion (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (buffer : List Component)
    (cuts : Fin (g + 2) → ℝ) (points : Generated → ℝ) (b : ℝ) : Prop :=
  ∃ i j pieces, RecordedEndpoints cuts points pieces ∧
    b * distance (physicalRows μ normalizer buffer cuts) i j <
      |discrepancy μ normalizer buffer cuts i j (domain pieces)|

theorem physicalMaximum_nonneg (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (buffer : List Component) (cuts : Fin (g + 2) → ℝ) (z : ℝ) :
    0 ≤ physicalMaximum μ normalizer buffer cuts z := by
  obtain ⟨i⟩ := ‹Nonempty Row›
  apply le_trans (b := physicalError μ normalizer buffer cuts z i i /
    (distance (physicalRows μ normalizer buffer cuts) i i + physicalError μ normalizer buffer cuts z i i))
  · exact div_nonneg (abs_nonneg _) (add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg _))
  · exact Finset.le_sup' (fun ij : Row × Row => physicalError μ normalizer buffer cuts z ij.1 ij.2 /
        (distance (physicalRows μ normalizer buffer cuts) ij.1 ij.2 + physicalError μ normalizer buffer cuts z ij.1 ij.2))
      (Finset.mem_univ (i, i))

/-- Every violating recorded union forces the same common endpoint charge
past the single Markov threshold. All pairs, adaptive unions, zero
 disagreements, and endpoint reuse are handled in this implication. -/
theorem badRecordedUnion_implies_charge (μ : Row → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (normalizer : Row → ℝ) (buffer : List Component) (cuts : Fin (g + 2) → ℝ)
    (hmono : Monotone cuts) (hzero : cuts 0 = 0) (points : Generated → ℝ)
    (b : ℝ) (hb : 0 < b) (hbad : BadRecordedUnion μ normalizer buffer cuts points b) :
    ENNReal.ofReal (b / (1 + b)) ≤
      ∑ p, ENNReal.ofReal (physicalMaximum μ normalizer buffer cuts (points p)) := by
  obtain ⟨i, j, pieces, hendpoints, hbad⟩ := hbad
  have htotal : b * distance (physicalRows μ normalizer buffer cuts) i j <
      ∑ p, physicalError μ normalizer buffer cuts (points p) i j :=
    hbad.trans_le (physical_recorded_union_error_le μ normalizer buffer cuts hmono hzero points pieces hendpoints i j)
  have hcommon := any_error_implies_charge
    (fun ij : Row × Row => distance (physicalRows μ normalizer buffer cuts) ij.1 ij.2)
    (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (fun ij p => physicalError μ normalizer buffer cuts (points p) ij.1 ij.2)
    (fun _ _ => abs_nonneg _)
    (fun p => physicalMaximum μ normalizer buffer cuts (points p))
    (fun ij p => Finset.le_sup' (fun ij : Row × Row =>
      physicalError μ normalizer buffer cuts (points p) ij.1 ij.2 /
        (distance (physicalRows μ normalizer buffer cuts) ij.1 ij.2 +
          physicalError μ normalizer buffer cuts (points p) ij.1 ij.2)) (Finset.mem_univ ij)) b hb ⟨(i, j), htotal⟩
  calc
    _ ≤ ENNReal.ofReal (∑ p, physicalMaximum μ normalizer buffer cuts (points p)) :=
      ENNReal.ofReal_le_ofReal hcommon.le
    _ = _ := ENNReal.ofReal_sum_of_nonneg (fun _ _ => physicalMaximum_nonneg _ _ _ _ _)

/-- Specialization to the actual reached/rejecting correction stream. -/
theorem loop_badRecordedUnion_implies_charge (μ : Row → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (normalizer : Row → ℝ) (buffer : List Component) (cuts : Fin (g + 2) → ℝ)
    (hmono : Monotone cuts) (hzero : cuts 0 = 0)
    (policy : UpperCircularStage.Policy n) (jobs : Fin m → Job n) (initial : LoopState n)
    (tape : Fin m → Start) (b : ℝ) (hb : 0 < b)
    (hbad : BadRecordedUnion μ normalizer buffer cuts (loopPoint policy jobs initial tape) b) :
    ENNReal.ofReal (b / (1 + b)) ≤ tapeTotal (loopTransition policy jobs)
      (fun i => proposalCharge policy (jobs i)
        (fun z => ENNReal.ofReal (physicalMaximum μ normalizer buffer cuts z))) initial tape := by
  have h := badRecordedUnion_implies_charge μ normalizer buffer cuts hmono hzero
    (loopPoint policy jobs initial tape) b hb hbad
  rw [sum_loopPoint_charge policy jobs
    (fun z => ENNReal.ofReal (physicalMaximum μ normalizer buffer cuts z))] at h
  · exact h
  · rw [← hzero, physicalMaximum_at_boundary μ normalizer buffer cuts hmono hzero 0]
    simp

end EnvyFreeResearch.Full.UpperAggregateInterpolation
