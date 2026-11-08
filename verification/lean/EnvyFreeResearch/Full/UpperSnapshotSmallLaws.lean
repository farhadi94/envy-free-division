import EnvyFreeResearch.Full.UpperSnapshotSmallPartition

/-! Exact cutter masses for the actual sequential shared-circle partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperUnionSampling
  UpperCircularStage UpperStageMeasurable Chores
variable {n J : ℕ}

def partitionRun (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) : (Fin J → ℝ) × State n :=
  execute policy origin cutter (shifts q) start

def actualPrefix (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin (J + 1)) : Set ℝ :=
  circularPrefix hJ (domain origin.cells) q start (partitionRun policy origin cutter q start).1 j

def actualPart (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin J) : Set ℝ :=
  part hJ (domain origin.cells) q start (partitionRun policy origin cutter q start).1 j

theorem project_zero : project (0 : I) = 0 := AddCircle.coe_zero 1

theorem project_one : project (1 : I) = 0 := AddCircle.coe_period 1

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (hJ : 0 < J) (q : Fin (J + 1) → I) (hq0 : q 0 = 0) (hq1 : q (Fin.last J) = 1)
include hpolicy hgood hpositive hq0

theorem first_boundary_cdf (start : Circle) :
    cdf (cond (μ cutter) (domain origin.cells))
      ((partitionRun policy origin cutter q start).1 ⟨0, hJ⟩) = (value start : ℝ) := by
  have he := endpoint_cdf μ policy hpolicy origin hgood cutter hpositive (shifts q) start ⟨0, hJ⟩
  have hi : (⟨0, hJ⟩ : Fin J).castSucc = 0 := rfl
  simpa only [partitionRun, shifts, hi, hq0, project_zero, add_zero] using he

include hq1 in
theorem boundary_cdf (start : Circle) (j : Fin (J + 1)) :
    cdf (cond (μ cutter) (domain origin.cells))
      (boundary hJ (partitionRun policy origin cutter q start).1 j) =
        (value (start + project (q j)) : ℝ) := by
  by_cases hj : j.val < J
  · have hi : (⟨j.val, hj⟩ : Fin J).castSucc = j := rfl
    simpa only [partitionRun, boundary, hj, dite_true, shifts, hi] using
      endpoint_cdf μ policy hpolicy origin hgood cutter hpositive (shifts q) start ⟨j.val, hj⟩
  · have hi : j = Fin.last J := by apply Fin.ext; have hh := j.isLt; simp only [Fin.val_last]; omega
    rw [hi, boundary_last, hq1, project_one, add_zero]
    exact first_boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0 start

include hq1 in
theorem actual_partition (hq : StrictMono q) (start : Circle) :
    (⋃ j, actualPart hJ policy origin cutter q start j) = domain origin.cells ∧
      Pairwise (fun i j => Disjoint (actualPart hJ policy origin cutter q start i)
        (actualPart hJ policy origin cutter q start j)) :=
  parts_partition hJ (domain origin.cells) q hq hq0 hq1 start _ _
    (monotone_cdf _) (boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1 start)

include hq1 in
theorem actual_prefix_mass (start : Circle) (j : Fin (J + 1)) :
    (μ cutter).real (actualPrefix hJ policy origin cutter q start j) =
      (q j : ℝ) * (μ cutter).real (domain origin.cells) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain origin.cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  have hown := physicalPiece_own_value (cond (μ cutter) (domain origin.cells))
    (domain origin.cells) (ae_cond_mem (domain_measurable origin.cells)) (q j) start _ _
    (first_boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0 start)
    (boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1 start j)
  have hsub : actualPrefix hJ policy origin cutter q start j ⊆ domain origin.cells :=
    physicalPiece_subset _ _ _ _ _
  change (cond (μ cutter) (domain origin.cells)).real
    (actualPrefix hJ policy origin cutter q start j) = (q j : ℝ) at hown
  rw [measureReal_def, cond_apply (domain_measurable origin.cells), inter_eq_right.mpr hsub,
    ENNReal.toReal_mul, ENNReal.toReal_inv] at hown
  change ((μ cutter).real (domain origin.cells))⁻¹ *
    (μ cutter).real (actualPrefix hJ policy origin cutter q start j) = (q j : ℝ) at hown
  apply (div_eq_iff hpositive.ne').mp
  simpa only [div_eq_mul_inv, mul_comm] using hown

include hq1 in
theorem actual_part_mass (hq : StrictMono q) (start : Circle) (j : Fin J) :
    (μ cutter).real (actualPart hJ policy origin cutter q start j) =
      ((q j.succ : ℝ) - q j.castSucc) * (μ cutter).real (domain origin.cells) := by
  have hm := prefix_mono hJ (domain origin.cells) q hq start
    (partitionRun policy origin cutter q start).1 _ (monotone_cdf _)
    (boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1 start)
  have hord : j.castSucc ≤ j.succ := by change j.val ≤ j.val + 1; omega
  change (μ cutter).real (actualPrefix hJ policy origin cutter q start j.succ \
    actualPrefix hJ policy origin cutter q start j.castSucc) = _
  have hsub : actualPrefix hJ policy origin cutter q start j.castSucc ⊆
      actualPrefix hJ policy origin cutter q start j.succ := hm hord
  have hleft : MeasurableSet (actualPrefix hJ policy origin cutter q start j.castSucc) :=
    prefix_measurable hJ _ (domain_measurable _) q start _ j.castSucc
  rw [measureReal_sdiff hsub hleft]
  rw [actual_prefix_mass μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1,
    actual_prefix_mass μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1]
  ring

end EnvyFreeResearch.Full.UpperSnapshotSmall
