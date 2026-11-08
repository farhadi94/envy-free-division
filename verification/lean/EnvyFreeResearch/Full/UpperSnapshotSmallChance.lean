import EnvyFreeResearch.Full.UpperSnapshotSmallSecondMean
import EnvyFreeResearch.Full.UpperSnapshotSmallActualSigned

/-! The fresh two-circle candidate has a quantitative witness probability.
Only input circles are independent; every oracle response may depend on the
complete preceding history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation UpperLogicalCells Chores
variable {n m J : ℕ}

 theorem actual_witness_chance
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells))
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hlast : cuts (Fin.last (m+1)) = 1)
    (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (t : ℝ) (ht : 0 < t) (hhalf : t ≤ 1/2) (hJ : 2 ≤ J)
    (hfit : (J : ℝ)*t < 1) (htlower : 1/(2*(J : ℝ)) ≤ t)
    (score : Fin (m+1) → ℝ) (hsum : ∑ e, score e = 0)
    (hnull : ∀ e, volume (cell (domain origin.cells) cuts e) = 0 → score e = 0)
    (hD : 0 < ∑ e, |score e|) :
    1/(8*(J : ℝ)) ≤ (volume.prod volume).real {z : Circle × Circle |
      (∑ e, |score e|)/(8*(J : ℝ)) ≤ candidateContrast hJ policy origin cutter cuts
        (positiveIndices score) t (signedEstimate score (cell (domain origin.cells) cuts)) z} := by
  have ht1 : t < 1 := by linarith
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hf := logical_interpolant_facts origin cuts hzero hlast hmono hsep score hsum hnull
  have hm := candidate_scores_measurable μ policy hpolicy hmeas origin hgood cutter hpositive cuts hzero hmono hsep
    (positiveIndices score) t ht ht1 hJ score (cell (domain origin.cells) cuts)
  have hi := candidate_scores_integrable μ policy hpolicy hmeas origin hgood cutter hpositive cuts hzero hmono hsep
    (positiveIndices score) t ht ht1 hJ score (cell (domain origin.cells) cuts) hsum
  apply UpperSnapshotCandidates.witness_chance_from_mean (volume.prod volume) _
    (hm.1.sub hm.2) (hi.1.sub hi.2) _ _ hD hj
  · intro z
    exact signedEstimate_contrast_bound score _ hsum _ _ (domain_measurable _) (domain_measurable _)
  · change (∑ e, |score e|)/(4*(J : ℝ)) ≤
      ∫ z, candidateContrast hJ policy origin cutter cuts (positiveIndices score) t
        (signedEstimate score (cell (domain origin.cells) cuts)) z ∂(volume.prod volume)
    rw [candidate_contrast_mean μ policy hpolicy hmeas origin hgood cutter hpositive cuts hzero hmono hsep
      (positiveIndices score) t ht ht1 hJ hfit score (cell (domain origin.cells) cuts) hsum _ hf.1 hf.2]
    have hM : 0 < total origin cutter := by rw [total_correct μ origin hgood]; exact hpositive
    have hP : 0 ≤ total (retain origin cuts (positiveIndices score)) cutter := by
      rw [total_correct μ _ (retain_wellFormed μ origin hgood cuts _)]; exact measureReal_nonneg
    have hPM : total (retain origin cuts (positiveIndices score)) cutter ≤ total origin cutter := by
      rw [total_correct μ _ (retain_wellFormed μ origin hgood cuts _), total_correct μ origin hgood]
      exact measureReal_mono (retain_subset origin cuts _)
    exact UpperSnapshotCandidates.contrastMean_lower _ t _ J hD.le ht hhalf
      (div_nonneg hP hM.le) ((div_le_one hM).mpr hPM) hj htlower

end EnvyFreeResearch.Full.UpperSnapshotSmall
