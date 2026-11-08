import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSupply
import EnvyFreeResearch.Full.UpperSnapshotSmallSecondRestoredMeasurable

/-! Conditional charging of the actual two-circle small Snapshot candidate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotSmall UpperLogicalPreparation UpperDomainDifference Chores
variable {n m J : ℕ} {Row : Type*} [Fintype Row] [Nonempty Row]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (cutter : Row)
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : 0 < (μ (active cutter)).real (domain origin.cells))
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (u : ℝ → ℝ≥0∞) (hu : Measurable u)
include hpolicy hmeas hgood hpositive ht ht2 hu

omit hzero hmono hsep in
theorem first_circle_charge :
    (∫⁻ start : UpperSnapshotSmall.Circle,
      ∑ j, u ((firstRun policy origin (active cutter) cuts selected t start).1 j) ∂volume) ≤
      ((2 : ℝ≥0∞) * ENNReal.ofReal (1 / t) * Fintype.card Row) *
        ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells := by
  exact circle_charge_le_mixture μ active origin.cells cutter hpositive policy hpolicy hmeas
    (firstSource origin (active cutter) cuts selected t)
    (firstSource_wellFormed μ origin hgood _ cuts selected t)
    (first_source_subset origin _ cuts selected t) t ht
    (first_source_fraction μ origin hgood _ cuts selected t ht2)
    (shifts (singleTargets (firstAmount origin (active cutter) cuts selected t))) u hu

include hzero hmono hsep in
theorem second_circle_charge (first : UpperSnapshotSmall.Circle) :
    (∫⁻ second : UpperSnapshotSmall.Circle,
      ∑ j, u ((secondRun (J := J) policy origin (active cutter) cuts selected t first second).1 j) ∂volume) ≤
      ((J : ℝ≥0∞) * ENNReal.ofReal (1 / t) * Fintype.card Row) *
        ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells := by
  have hs := firstSource_positive μ origin hgood _ hpositive cuts selected t ht (by linarith)
  have hp := first_partition μ policy hpolicy origin hgood (active cutter) cuts selected t hs first
  have hsub : domain (firstRemainder policy origin (active cutter) cuts selected t first).cells ⊆
      domain origin.cells := by rw [hp.2.2]; exact sdiff_subset
  exact circle_charge_le_mixture μ active origin.cells cutter hpositive policy hpolicy hmeas
    (firstRemainder policy origin (active cutter) cuts selected t first) hp.2.1 hsub t ht
    (second_source_fraction μ policy hpolicy origin hgood _ hpositive cuts hzero hmono hsep selected t ht ht2 first)
    (shifts (remainderTargets J t)) u hu

include hzero hmono hsep in
/-- The second group is conditioned on the entire first-group history. The
sum includes all J+2 actual outputs whether or not this candidate is retained. -/
theorem two_circle_charge :
    (∫⁻ p : UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle,
      ((∑ j, u ((firstRun policy origin (active cutter) cuts selected t p.1).1 j)) +
        ∑ j, u ((secondRun (J := J) policy origin (active cutter) cuts selected t p.1 p.2).1 j))
      ∂((volume : Measure UpperSnapshotSmall.Circle).prod volume)) ≤
      (((J + 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / t) * Fintype.card Row) *
        ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells := by
  let A (first : UpperSnapshotSmall.Circle) :=
    ∑ j, u ((firstRun policy origin (active cutter) cuts selected t first).1 j)
  let B (p : UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle) :=
    ∑ j, u ((secondRun (J := J) policy origin (active cutter) cuts selected t p.1 p.2).1 j)
  have ha : Measurable A := by
    have hr := firstRun_measurable (fun _ : UpperSnapshotSmall.Circle => origin) (active cutter)
      (fun _ => cuts) (fun _ => selected) (fun _ => t) measurable_const (fun _ => measurable_const)
      measurable_const measurable_const policy hmeas id measurable_id
    exact Finset.measurable_sum Finset.univ (fun j _ =>
      hu.comp ((measurable_pi_apply j).comp (measurable_fst.comp hr)))
  have hb : Measurable B := by
    have hr := secondRun_measurable (J := J) policy hmeas
      (fun _ : UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle => origin) (active cutter)
      (fun _ => cuts) (fun _ => selected) t Prod.fst Prod.snd measurable_const
      (fun _ => measurable_const) measurable_const measurable_fst measurable_snd
    exact Finset.measurable_sum Finset.univ (fun j _ =>
      hu.comp ((measurable_pi_apply j).comp (measurable_fst.comp hr)))
  change (∫⁻ p, A p.1 + B p ∂((volume : Measure UpperSnapshotSmall.Circle).prod volume)) ≤ _
  have hsum : Measurable (fun p : UpperSnapshotSmall.Circle × UpperSnapshotSmall.Circle => A p.1 + B p) :=
    (ha.comp measurable_fst).add hb
  rw [lintegral_prod _ hsum.aemeasurable]
  have hinner (first : UpperSnapshotSmall.Circle) :
      (∫⁻ second, A first + B (first, second) ∂(volume : Measure UpperSnapshotSmall.Circle)) =
        A first + ∫⁻ second, B (first, second) ∂(volume : Measure UpperSnapshotSmall.Circle) := by
    rw [lintegral_add_left measurable_const]
    simp
  simp_rw [hinner]
  rw [lintegral_add_left ha]
  have hsecond : (∫⁻ first, ∫⁻ second, B (first, second) ∂(volume : Measure UpperSnapshotSmall.Circle)
      ∂(volume : Measure UpperSnapshotSmall.Circle)) ≤
      ((J : ℝ≥0∞) * ENNReal.ofReal (1 / t) * Fintype.card Row) *
        ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells := by
    calc
      _ ≤ ∫⁻ _ : UpperSnapshotSmall.Circle,
          ((J : ℝ≥0∞) * ENNReal.ofReal (1 / t) * Fintype.card Row) *
            ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells ∂volume := by
        apply lintegral_mono
        intro first
        exact second_circle_charge μ active cutter policy hpolicy hmeas origin hgood hpositive
          cuts hzero hmono hsep selected t ht ht2 u hu first
      _ = _ := by simp
  calc
    _ ≤ ((2 : ℝ≥0∞) * ENNReal.ofReal (1 / t) * Fintype.card Row) *
          (∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells) +
        ((J : ℝ≥0∞) * ENNReal.ofReal (1 / t) * Fintype.card Row) *
          ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells :=
      add_le_add (first_circle_charge μ active cutter policy hpolicy hmeas origin hgood hpositive
        cuts selected t ht ht2 u hu) hsecond
    _ = _ := by push_cast; ring

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
