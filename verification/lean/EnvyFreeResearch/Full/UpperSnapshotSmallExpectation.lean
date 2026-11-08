import EnvyFreeResearch.Full.UpperSnapshotSmallLaws

/-! Exact signed expectations of the actual shared-start prefix partition.
The proof applies the physical inclusion law to the returned, history-dependent
roots and then subtracts consecutive nested prefixes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperUnionSampling
  UpperCircularStage UpperStageMeasurable Chores
variable {n J : ℕ} {X : Type*} [MeasurableSpace X]

theorem boundary_measurable (hJ : 0 < J) (points : X → Fin J → ℝ)
    (hpoints : ∀ j, Measurable (fun x => points x j)) (j : Fin (J + 1)) :
    Measurable (fun x => boundary hJ (points x) j) := by
  unfold boundary
  split_ifs <;> exact hpoints _

theorem partitionRun_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (origin : X → State n) (cutter : Fin n) (q : X → Fin (J + 1) → I) (start : X → Circle)
    (horigin : Measurable origin) (hq : ∀ j, Measurable (fun x => q x j)) (hstart : Measurable start) :
    Measurable (fun x => partitionRun policy (origin x) cutter (q x) (start x)) :=
  execute_measurable policy hmeas origin cutter (fun x => shifts (q x)) start horigin
    (fun j => measurable_project.comp (hq j.castSucc)) hstart

section Fixed
variable (policy : Policy n) (hmeas : MeasurablePolicy policy) (origin : State n) (cutter : Fin n)
  (hJ : 0 < J) (q : Fin (J + 1) → I)
include hmeas

theorem first_boundary_measurable :
    Measurable (fun start => (partitionRun policy origin cutter q start).1 ⟨0, hJ⟩) :=
  (measurable_pi_apply _).comp (measurable_fst.comp
    (partitionRun_measurable policy hmeas (fun _ => origin) cutter (fun _ => q) id
      measurable_const (fun _ => measurable_const) measurable_id))

theorem last_boundary_measurable (j : Fin (J + 1)) :
    Measurable (fun start => boundary hJ (partitionRun policy origin cutter q start).1 j) :=
  boundary_measurable hJ _ (fun i => (measurable_pi_apply i).comp (measurable_fst.comp
    (partitionRun_measurable policy hmeas (fun _ => origin) cutter (fun _ => q) id
      measurable_const (fun _ => measurable_const) measurable_id))) j

theorem actual_prefix_membership_measurable (j : Fin (J + 1)) :
    MeasurableSet {p : Circle × ℝ | p.2 ∈ actualPrefix hJ policy origin cutter q p.1 j} :=
  measurable_physical_membership _ (domain_measurable _) _ _ _
    (first_boundary_measurable policy hmeas origin cutter hJ q)
    (last_boundary_measurable policy hmeas origin cutter hJ q j)

theorem actual_part_membership_measurable (j : Fin J) :
    MeasurableSet {p : Circle × ℝ | p.2 ∈ actualPart hJ policy origin cutter q p.1 j} :=
  (actual_prefix_membership_measurable policy hmeas origin cutter hJ q j.succ).diff
    (actual_prefix_membership_measurable policy hmeas origin cutter hJ q j.castSucc)

theorem actual_prefix_signed_integrable (signed : SignedMeasure ℝ) (j : Fin (J + 1)) :
    Integrable (fun start => signed (actualPrefix hJ policy origin cutter q start j))
      (volume : Measure Circle) :=
  UpperSignedCircular.signed_mass_integrable _ (domain_measurable _) _ _ _
    (first_boundary_measurable policy hmeas origin cutter hJ q)
    (last_boundary_measurable policy hmeas origin cutter hJ q j) signed

end Fixed

section Laws
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (hJ : 0 < J) (q : Fin (J + 1) → I) (hq0 : q 0 = 0) (hq1 : q (Fin.last J) = 1)
include hpolicy hmeas hgood hpositive hq0 hq1

theorem actual_prefix_signed_expectation (signed : SignedMeasure ℝ) (j : Fin (J + 1)) :
    (∫ start, signed (actualPrefix hJ policy origin cutter q start j) ∂(volume : Measure Circle)) =
      (q j : ℝ) * signed (domain origin.cells) := by
  let : IsProbabilityMeasure (cond (μ cutter) (domain origin.cells)) :=
    cond_isProbabilityMeasure (positive_real_mass_ne_zero _ _ hpositive)
  exact UpperSignedCircular.signed_mass_expectation _ (domain_measurable _) _ _ _
    (first_boundary_measurable policy hmeas origin cutter hJ q)
    (last_boundary_measurable policy hmeas origin cutter hJ q j)
    (monotone_cdf (cond (μ cutter) (domain origin.cells)))
    (fun x _ => ⟨cdf_nonneg _ x, cdf_le_one _ x⟩)
    (ae_of_all _ (first_boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0))
    (ae_of_all _ (fun start => boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1 start j))
    signed

omit hmeas in
theorem actual_part_signed_eq (hq : StrictMono q) (signed : SignedMeasure ℝ)
    (start : Circle) (j : Fin J) :
    signed (actualPart hJ policy origin cutter q start j) =
      signed (actualPrefix hJ policy origin cutter q start j.succ) -
      signed (actualPrefix hJ policy origin cutter q start j.castSucc) := by
  apply VectorMeasure.of_sdiff
    (prefix_measurable hJ _ (domain_measurable _) q start _ j.castSucc)
    (prefix_measurable hJ _ (domain_measurable _) q start _ j.succ)
  exact prefix_mono hJ (domain origin.cells) q hq start _ _ (monotone_cdf _)
    (boundary_cdf μ policy hpolicy origin hgood cutter hpositive hJ q hq0 hq1 start)
    (by change j.val ≤ j.val + 1; omega)

theorem actual_part_signed_integrable (hq : StrictMono q) (signed : SignedMeasure ℝ) (j : Fin J) :
    Integrable (fun start => signed (actualPart hJ policy origin cutter q start j))
      (volume : Measure Circle) := by
  apply ((actual_prefix_signed_integrable policy hmeas origin cutter hJ q signed j.succ).sub
    (actual_prefix_signed_integrable policy hmeas origin cutter hJ q signed j.castSucc)).congr
  exact ae_of_all _ (fun start => (actual_part_signed_eq μ policy hpolicy origin hgood cutter hpositive
    hJ q hq0 hq1 hq signed start j).symm)

theorem actual_part_signed_expectation (hq : StrictMono q) (signed : SignedMeasure ℝ) (j : Fin J) :
    (∫ start, signed (actualPart hJ policy origin cutter q start j) ∂(volume : Measure Circle)) =
      ((q j.succ : ℝ) - q j.castSucc) * signed (domain origin.cells) := by
  have heq : (fun start => signed (actualPart hJ policy origin cutter q start j)) =
      fun start => signed (actualPrefix hJ policy origin cutter q start j.succ) -
        signed (actualPrefix hJ policy origin cutter q start j.castSucc) :=
    funext (fun start => actual_part_signed_eq μ policy hpolicy origin hgood cutter hpositive
      hJ q hq0 hq1 hq signed start j)
  rw [heq, integral_sub
    (actual_prefix_signed_integrable policy hmeas origin cutter hJ q signed j.succ)
    (actual_prefix_signed_integrable policy hmeas origin cutter hJ q signed j.castSucc),
    actual_prefix_signed_expectation μ policy hpolicy hmeas origin hgood cutter hpositive hJ q hq0 hq1,
    actual_prefix_signed_expectation μ policy hpolicy hmeas origin hgood cutter hpositive hJ q hq0 hq1]
  ring

end Laws
end EnvyFreeResearch.Full.UpperSnapshotSmall
