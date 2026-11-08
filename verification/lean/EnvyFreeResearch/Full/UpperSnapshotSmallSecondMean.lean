import EnvyFreeResearch.Full.UpperSnapshotSmallSecondMeasurable
import EnvyFreeResearch.Full.UpperSnapshotCandidatesMean

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ} {Cell : Type*} [Fintype Cell]

def candidateContrast (hJ : 2 ≤ J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (signed : SignedMeasure ℝ) (z : Circle × Circle) : ℝ :=
  signed (domain (firstEndowment policy origin cutter cuts selected t z.1).cells) -
    signed (domain (secondPiece (J := J) (by omega) policy origin cutter cuts selected t z.1 z.2
      ⟨0, by omega⟩).cells)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
  (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
  (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
  (hJ : 2 ≤ J) (hfit : (J : ℝ)*t < 1)
  (score : Cell → ℝ) (cells : Cell → Set ℝ) (hsum : ∑ e, score e = 0)
include hpolicy hmeas hgood hpositive hzero hmono hsep ht ht1

theorem candidate_scores_measurable :
    Measurable (fun z : Circle × Circle => signedEstimate score cells
      (domain (firstEndowment policy origin cutter cuts selected t z.1).cells)) ∧
    Measurable (fun z : Circle × Circle => signedEstimate score cells
      (domain (secondPiece (J := J) (by omega) policy origin cutter cuts selected t z.1 z.2 ⟨0, by omega⟩).cells)) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hf := firstEndowment_measurable (fun _ : Circle × Circle => origin) cutter
    (fun _ => cuts) (fun _ => selected) (fun _ => t) measurable_const (fun _ => measurable_const)
    measurable_const measurable_const policy hmeas Prod.fst measurable_fst
  have hg := secondPiece_measurable (J := J) (by omega) policy hmeas (fun _ : Circle × Circle => origin)
    cutter (fun _ => cuts) (fun _ => selected) t Prod.fst Prod.snd measurable_const
    (fun _ => measurable_const) measurable_const measurable_fst measurable_snd ⟨0, by omega⟩
  exact ⟨signedEstimate_domain_measurable score cells _ (state_cells_measurable.comp hf)
    (fun z => (first_partition μ policy hpolicy origin hgood cutter cuts selected t hs z.1).1.2.1),
    signedEstimate_domain_measurable score cells _ (state_cells_measurable.comp hg)
    (fun z => (second_piece_wellFormed μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
      selected t ht ht1 (J := J) (by omega) z.1 z.2 ⟨0, by omega⟩).2.1)⟩

include hsum in
theorem candidate_scores_integrable :
    Integrable (fun z : Circle × Circle => signedEstimate score cells
      (domain (firstEndowment policy origin cutter cuts selected t z.1).cells)) (volume.prod volume) ∧
    Integrable (fun z : Circle × Circle => signedEstimate score cells
      (domain (secondPiece (J := J) (by omega) policy origin cutter cuts selected t z.1 z.2 ⟨0, by omega⟩).cells))
      (volume.prod volume) := by
  have hm := candidate_scores_measurable μ policy hpolicy hmeas origin hgood cutter hpositive cuts hzero hmono hsep
    selected t ht ht1 hJ score cells
  constructor
  · apply (integrable_const ((∑ e, |score e|)/2)).mono' hm.1.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using
        (signedEstimate_bound score cells hsum _ (domain_measurable _)))
  · apply (integrable_const ((∑ e, |score e|)/2)).mono' hm.2.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using
        (signedEstimate_bound score cells hsum _ (domain_measurable _)))

include hsum hfit in
theorem candidate_contrast_mean (D : ℝ)
    (hwhole : signedEstimate score cells (domain origin.cells) = 0)
    (hpos : signedEstimate score cells (domain (retain origin cuts selected).cells) = D/2) :
    (∫ z, candidateContrast hJ policy origin cutter cuts selected t (signedEstimate score cells) z
      ∂(volume.prod volume)) =
      UpperSnapshotCandidates.firstMean D t (total (retain origin cuts selected) cutter / total origin cutter) -
      (-(t/(1-t)) * UpperSnapshotCandidates.firstMean D t
        (total (retain origin cuts selected) cutter / total origin cutter)) := by
  have hi := candidate_scores_integrable μ policy hpolicy hmeas origin hgood cutter hpositive cuts hzero hmono hsep
    selected t ht ht1 hJ score cells hsum
  unfold candidateContrast
  rw [integral_sub hi.1 hi.2, integral_prod _ hi.1, integral_prod _ hi.2]
  simp only [integral_const, probReal_univ, one_smul]
  simp_rw [second_conditional_signed_mean μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
    selected t ht ht1 hmeas hJ hfit (signedEstimate score cells) hwhole]
  rw [integral_const_mul,
    firstEndowment_mean μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1
      hmeas (signedEstimate score cells) D hwhole hpos]

end EnvyFreeResearch.Full.UpperSnapshotSmall
