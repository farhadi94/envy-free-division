import EnvyFreeResearch.Full.UpperShrinkBounds

/-! Semantic facts needed from the deterministic carving executor. The
near-EF and buffer bounds are derived from its one-sided color moments and
literal partition, not supplied as separate successful Repair hypotheses.
The actual logarithmic-precision carving executor remains to be joined. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace EnvyFreeResearch.Full.UpperShrink
open UpperRecordedDomain UpperCorrectionExecution UpperRepairPreparationChecks

variable {n k : ℕ}

structure Carved (n k : ℕ) where
  old : Fin k → State n
  buffer : State n

structure Carved.Valid (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Fin k → Fin n)
    (origin : State n) (G tau : ℝ) (out : Carved n k) : Prop where
  old_wellFormed : ∀ j, WellFormed μ (out.old j)
  buffer_wellFormed : WellFormed μ out.buffer
  old_disjoint : Pairwise (fun i j => Disjoint (domain (out.old i).cells) (domain (out.old j).cells))
  old_buffer : ∀ j, Disjoint (domain (out.old j).cells) (domain out.buffer.cells)
  material : (⋃ j, domain (out.old j).cells) ∪ domain out.buffer.cells = domain origin.cells
  common_history : ∀ j, (out.old j).history = out.buffer.history
  lower : ∀ i j, (fraction k G - error tau G) * (μ (active i)).real (domain origin.cells) ≤
    (μ (active i)).real (domain (out.old j).cells)
  upper : ∀ i j, (μ (active i)).real (domain (out.old j).cells) ≤
    fraction k G * (μ (active i)).real (domain origin.cells)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Fin k → Fin n)
    (origin : State n) (G tau : ℝ) (out : Carved n k)
    (valid : out.Valid μ active origin G tau)

include valid in
theorem carved_row_partition (i : Fin k) :
    (μ (active i)).real (domain out.buffer.cells) +
      ∑ j, (μ (active i)).real (domain (out.old j).cells) =
        (μ (active i)).real (domain origin.cells) := by
  rw [← measureReal_iUnion_fintype valid.old_disjoint (fun j => domain_measurable (out.old j).cells)]
  rw [← measureReal_union (disjoint_iUnion_right.mpr (fun j => (valid.old_buffer j).symm))
    (MeasurableSet.iUnion (fun j => domain_measurable (out.old j).cells))]
  rw [union_comm, valid.material]

include valid in
theorem carved_buffer_bounds (hk : 0 < k) (hG : 0 < G) (htau : 0 ≤ tau)
    (hktau : (k : ℝ) * tau ≤ 2) (i : Fin k) :
    (μ (active i)).real (domain origin.cells) / (2 * G) ≤ (μ (active i)).real (domain out.buffer.cells) ∧
    (μ (active i)).real (domain out.buffer.cells) ≤ (μ (active i)).real (domain origin.cells) / G :=
  carving_buffer_bounds hk hG htau (measureReal_nonneg) hktau
    (fun j => (μ (active i)).real (domain (out.old j).cells))
    (valid.lower i) (valid.upper i) (carved_row_partition μ active origin G tau out valid i)

include valid in
theorem carved_near (hk : 0 < k) (hG : 0 < G) (htau : 0 ≤ tau)
    (hktau : (k : ℝ) * tau ≤ 2) (chores : Bool) : Near chores μ active out.buffer out.old tau := by
  intro i j
  have hb := (carved_buffer_bounds μ active origin G tau out valid hk hG htau hktau i).1
  cases chores <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact carving_range hG htau measureReal_nonneg hb (valid.upper i j) (valid.lower i i)
  · exact carving_range hG htau measureReal_nonneg hb (valid.upper i i) (valid.lower i j)

end EnvyFreeResearch.Full.UpperShrink
